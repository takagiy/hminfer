use crate::ast::Expr;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{self, Display, Formatter},
    iter,
    sync::atomic::{AtomicUsize, Ordering},
};
use typed_arena::Arena;

mod ast;

#[derive(Debug, Clone)]
pub enum Type<'a> {
    Primitive(Primitive),
    Apply(Constructor, Vec<&'a Type<'a>>),
    Var(RefCell<TypeVar<'a>>),
}

#[derive(Debug, Clone)]
pub enum TypeVar<'a> {
    Unbound { id: usize, level: usize },
    Link(&'a Type<'a>),
    Poly { id: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Primitive {
    Int,
    Bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constructor {
    Func,
    Tuple,
}

impl Display for Type<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use Constructor::*;
        use Type::*;
        use TypeVar::*;

        match self {
            Primitive(t) => write!(f, "{}", format!("{:?}", t).to_lowercase())?,
            Apply(ctor, args) => {
                let delimiter = match ctor {
                    Func => " -> ",
                    Tuple => ", ",
                };
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, "{delimiter}")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")?;
            }
            Var(var) => match *var.borrow() {
                Unbound { .. } => write!(f, "?")?,
                Link(t) => write!(f, "{}", t)?,
                Poly { id } => write!(f, "'{}", id)?,
            },
        }
        Ok(())
    }
}

impl<'a> Type<'a> {
    fn new_unbound_var(id: usize, level: usize) -> Type<'a> {
        Type::Var(RefCell::new(TypeVar::Unbound { id, level }))
    }

    fn unify(&'a self, other: &'a Type<'a>) {
        use Type::*;

        match (self, other) {
            (Primitive(left), Primitive(right)) if left == right => {}
            (Apply(lctor, largs), Apply(rctor, rargs))
                if lctor == rctor && largs.len() == rargs.len() =>
            {
                for (left, right) in largs.iter().zip(rargs) {
                    left.unify(right);
                }
            }
            (Var(left), right) => left.borrow_mut().unify(right),
            (left, Var(right)) => right.borrow_mut().unify(left),
            _ => panic!("unsatisfiable constraint: {:?} = {:?}", self, other),
        }
    }

    fn generalized(&'a self, level: usize, arena: &'a Arena<Self>) -> &'a Type<'a> {
        use Type::*;

        match self {
            Primitive(_) => self,
            Apply(ctor, args) => arena.alloc(Apply(
                ctor.clone(),
                args.into_iter()
                    .map(|arg| arg.generalized(level, arena))
                    .collect(),
            )),
            Var(var) => match *var.borrow() {
                TypeVar::Link(t) => t.generalized(level, arena),
                TypeVar::Poly { .. } => self,
                TypeVar::Unbound {
                    id,
                    level: var_level,
                } => {
                    if var_level > level {
                        arena.alloc(Var(RefCell::new(TypeVar::Poly { id })))
                    } else {
                        self
                    }
                }
            },
        }
    }

    pub fn instance(&'a self, level: usize, arena: &'a Arena<Self>) -> &'a Type<'a> {
        self.instance_rec(level, arena, &mut HashMap::new())
    }

    fn instance_rec(
        &'a self,
        level: usize,
        arena: &'a Arena<Self>,
        context: &mut HashMap<usize, &'a Self>,
    ) -> &'a Type<'a> {
        use Type::*;

        match self {
            Primitive(_) => self,
            Apply(ctor, args) => arena.alloc(Apply(
                ctor.clone(),
                args.iter()
                    .map(|arg| arg.instance_rec(level, arena, context))
                    .collect(),
            )),
            Var(var) => match *var.borrow() {
                TypeVar::Link(t) => t.instance_rec(level, arena, context),
                TypeVar::Unbound { .. } => self,
                TypeVar::Poly { id } => context
                    .entry(id)
                    .or_insert_with(|| arena.alloc(Type::new_unbound_var(id, level))),
            },
        }
    }
}

impl<'a> TypeVar<'a> {
    pub fn unify(&mut self, other: &'a Type<'a>) {
        use TypeVar::*;

        if let Type::Var(other) = other {
            match (&mut *self, &mut *other.borrow_mut()) {
                (left, Link(right)) => {
                    return left.unify(right);
                }
                (Unbound { level: llevel, .. }, Unbound { level: rlevel, .. }) => {
                    *rlevel = *llevel.min(rlevel);
                }
                _ => {}
            }
        }
        match (self, other) {
            (left @ Unbound { .. }, right) => {
                *left = Link(right);
            }
            (Link(left), right) => {
                left.unify(right);
            }
            (Poly { .. }, _) => panic!("uninstantiated type variable"),
        }
    }
}

struct TypeEnv<'a> {
    variable_types: HashMap<String, &'a Type<'a>>,
}

impl<'a> TypeEnv<'a> {
    pub fn new() -> TypeEnv<'a> {
        TypeEnv {
            variable_types: HashMap::new(),
        }
    }

    pub fn with<F, R>(&mut self, name: String, ty: &'a Type<'a>, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old_type = self.variable_types.insert(name.clone(), ty);
        let result = f(self);
        if let Some(old_type) = old_type {
            self.variable_types.insert(name, old_type);
        } else {
            self.variable_types.remove(&name);
        }
        result
    }
}

struct TypeChecker<'arena> {
    arena: Arena<Type<'arena>>,
    fresh_var_id: AtomicUsize,
}

impl<'a> TypeChecker<'a> {
    pub fn new() -> TypeChecker<'a> {
        TypeChecker {
            arena: Arena::new(),
            fresh_var_id: AtomicUsize::new(0),
        }
    }

    pub fn infer(&'a self, expr: &Expr, env: &mut TypeEnv<'a>, level: usize) -> &'a Type<'a> {
        use Expr::*;

        match expr {
            ILit(_) => self.arena.alloc(Type::Primitive(Primitive::Int)),
            BLit(_) => self.arena.alloc(Type::Primitive(Primitive::Bool)),
            VarRef(name) => env.variable_types[name],
            Tuple(items) => self.arena.alloc(Type::Apply(
                Constructor::Tuple,
                items
                    .iter()
                    .map(|item| self.infer(item, env, level))
                    .collect(),
            )),
            If {
                condition,
                then,
                otherwise,
            } => {
                let condition_type = self.infer(condition, env, level);
                let then_type = self.infer(then, env, level);
                let otherwise_type = self.infer(otherwise, env, level);
                condition_type.unify(self.arena.alloc(Type::Primitive(Primitive::Bool)));
                then_type.unify(otherwise_type);
                then_type
            }
            Lambda { argument, body } => {
                let argument_type = self.alloc_var(level);
                let return_type = env.with(argument.clone(), argument_type, |env| {
                    self.infer(body, env, level)
                });
                self.arena.alloc(Type::Apply(
                    Constructor::Func,
                    vec![argument_type, return_type],
                ))
            }
            Apply {
                function,
                arguments,
            } => {
                let function_type = self
                    .infer(function, env, level)
                    .instance(level, &self.arena);
                let argument_types = arguments
                    .iter()
                    .map(|argument| self.infer(argument, env, level));
                let return_type = self.alloc_var(level);
                let expected_function_type = self.arena.alloc(Type::Apply(
                    Constructor::Func,
                    argument_types.chain(iter::once(return_type)).collect(),
                ));
                function_type.unify(expected_function_type);
                return_type
            }
            Let {
                variable,
                definition,
                body,
            } => {
                let definition_type = self
                    .infer(definition, env, level + 1)
                    .generalized(level, &self.arena);
                env.with(variable.clone(), definition_type, |env| {
                    self.infer(body, env, level)
                })
            }
        }
    }

    fn alloc_var(&'a self, level: usize) -> &'a Type<'a> {
        let id = self.fresh_var_id.fetch_add(1, Ordering::Relaxed);
        self.arena.alloc(Type::new_unbound_var(id, level))
    }
}

fn main() {
    let asts = vec![
        ast! {
            if true then 1 else 2
        },
        ast! {
            if (if true then false else true) then 1 else 2
        },
        ast! {
            if true then (func x => true) else (func x => false)
        },
        ast! {
            let f = (func x => x) in
            let y = (f 1) in false
        },
        ast! {
            let pair = (1, true) in
            let x = 2 in pair, x
        },
        ast! {
            let make_pair = (func x => func y => (x, y)) in make_pair
        },
    ];
    for ast in asts {
        println!("AST: {:?}", ast);
        let mut env = TypeEnv::new();
        let checker = TypeChecker::new();
        let ty = checker.infer(&ast, &mut env, 0);
        println!("Type: {}", ty);
    }
}
