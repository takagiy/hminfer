use crate::ast::Expr;
use itertools::Itertools;
use std::{
    cell::{RefCell, RefMut},
    collections::{BTreeMap, HashMap},
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
    Record(&'a Row<'a>),
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

#[derive(Debug, Clone)]
pub struct Row<'a> {
    columns: BTreeMap<String, &'a Type<'a>>,
    rest: RefCell<RowVar<'a>>,
}

#[derive(Debug, Clone)]
pub enum RowVar<'a> {
    Unbound { id: usize, level: usize },
    Link(&'a Row<'a>),
    Poly { id: usize },
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
                Unbound { id, level } => write!(f, "'?{id}({level})")?,
                Link(t) => write!(f, "{t}")?,
                Poly { id } => write!(f, "'{id}")?,
            },
            Record(row) => write!(f, "{{{row}}}")?,
        }
        Ok(())
    }
}

impl Display for Row<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use RowVar::*;

        match &*self.rest.borrow() {
            rest @ Unbound { .. } | rest @ Poly { .. } => write!(f, "{rest} | ")?,
            rest @ Link(_) => write!(f, "{rest}, ")?,
        }
        for (i, (label, t)) in self.columns.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", label, t)?;
        }
        Ok(())
    }
}

impl Display for RowVar<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use RowVar::*;

        match self {
            Unbound { id, level } => write!(f, "'?{id}({level})"),
            Link(row) => write!(f, "{row}"),
            Poly { id } => write!(f, "'{id}"),
        }
    }
}

impl<'a> Type<'a> {
    fn new_unbound_var(id: usize, level: usize) -> Type<'a> {
        Type::Var(RefCell::new(TypeVar::Unbound { id, level }))
    }

    fn unify(&'a self, other: &'a Type<'a>, ctx: &'a InferContext<'a>) {
        use Type::*;

        match (self, other) {
            (Primitive(left), Primitive(right)) if left == right => {}
            (Apply(lctor, largs), Apply(rctor, rargs))
                if lctor == rctor && largs.len() == rargs.len() =>
            {
                for (left, right) in largs.iter().zip(rargs) {
                    left.unify(right, ctx);
                }
            }
            (Record(left), Record(right)) => left.unify(right, ctx),
            (Var(left), right) => left.borrow_mut().unify(right, ctx),
            (left, Var(right)) => right.borrow_mut().unify(left, ctx),
            _ => panic!("unsatisfiable constraint: {:?} = {:?}", self, other),
        }
    }

    fn generalized(&'a self, level: usize, ctx: &'a InferContext<'a>) -> &'a Type<'a> {
        use Type::*;

        match self {
            Primitive(_) => self,
            Apply(ctor, args) => ctx.types.alloc(Apply(
                ctor.clone(),
                args.iter().map(|arg| arg.generalized(level, ctx)).collect(),
            )),
            Var(var) => match *var.borrow() {
                TypeVar::Link(t) => t.generalized(level, ctx),
                TypeVar::Poly { .. } => self,
                TypeVar::Unbound {
                    id,
                    level: var_level,
                } => {
                    if var_level > level {
                        ctx.types.alloc(Var(RefCell::new(TypeVar::Poly { id })))
                    } else {
                        self
                    }
                }
            },
            Record(row) => ctx.types.alloc(Record(row.generalized(level, ctx))),
        }
    }

    pub fn instance(&'a self, level: usize, ctx: &'a InferContext<'a>) -> &'a Type<'a> {
        self.instance_rec(level, ctx, &mut HashMap::new())
    }

    fn instance_rec(
        &'a self,
        level: usize,
        ctx: &'a InferContext<'a>,
        context: &mut HashMap<usize, &'a Self>,
    ) -> &'a Type<'a> {
        use Type::*;

        match self {
            Primitive(_) => self,
            Apply(ctor, args) => ctx.types.alloc(Apply(
                ctor.clone(),
                args.iter()
                    .map(|arg| arg.instance_rec(level, ctx, context))
                    .collect(),
            )),
            Var(var) => match *var.borrow() {
                TypeVar::Link(t) => t.instance_rec(level, ctx, context),
                TypeVar::Unbound { .. } => self,
                TypeVar::Poly { id } => context
                    .entry(id)
                    .or_insert_with(|| ctx.types.alloc(Type::new_unbound_var(id, level))),
            },
            Record(row) => ctx.types.alloc(Record(row.instance(level, ctx, context))),
        }
    }
}

impl<'a> TypeVar<'a> {
    pub fn unify(&mut self, other: &'a Type<'a>, ctx: &'a InferContext<'a>) {
        use TypeVar::*;

        if let Type::Var(other) = other {
            match (&mut *self, &mut *other.borrow_mut()) {
                (left, Link(right)) => {
                    return left.unify(right, ctx);
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
                left.unify(right, ctx);
            }
            (Poly { .. }, _) => panic!("uninstantiated type variable"),
        }
    }
}

impl<'a> Row<'a> {
    pub fn unify(&'a self, other: &'a Self, ctx: &'a InferContext<'a>) {
        use itertools::EitherOrBoth::*;

        let presences = self
            .columns
            .iter()
            .merge_join_by(other.columns.iter(), |(left, _), (right, _)| {
                left.cmp(right)
            });
        let mut lcolumns = BTreeMap::new();
        let mut rcolumns = BTreeMap::new();
        for presence in presences {
            match presence {
                Both((_, left), (_, right)) => left.unify(right, ctx),
                Left((label, t)) => {
                    lcolumns.insert(label.clone(), *t);
                }
                Right((label, t)) => {
                    rcolumns.insert(label.clone(), *t);
                }
            }
        }
        let level = self.base_var_level().min(*other.base_var_level());
        let rest = RefCell::new(RowVar::Unbound {
            id: ctx.fresh_var_id(),
            level,
        });
        let left = ctx.rows.alloc(Row {
            columns: rcolumns,
            rest: rest.clone(),
        });
        let right = ctx.rows.alloc(Row {
            columns: lcolumns,
            rest,
        });
        self.rest.borrow_mut().unify(left, ctx);
        other.rest.borrow_mut().unify(right, ctx);
    }

    pub fn generalized(&'a self, level: usize, ctx: &'a InferContext<'a>) -> &'a Self {
        let columns = self
            .columns
            .iter()
            .map(|(label, t)| (label.clone(), t.generalized(level, ctx)))
            .collect();
        let rest = match *self.rest.borrow() {
            RowVar::Unbound {
                id,
                level: var_level,
            } if var_level > level => RowVar::Poly { id },
            RowVar::Link(row) => RowVar::Link(row.generalized(level, ctx)),
            ref other => other.clone(),
        };
        ctx.rows.alloc(Row {
            columns,
            rest: RefCell::new(rest),
        })
    }

    pub fn instance(
        &'a self,
        level: usize,
        ctx: &'a InferContext<'a>,
        context: &mut HashMap<usize, &'a Type<'a>>,
    ) -> &'a Self {
        unimplemented!()
    }

    pub fn base_var(&'a self) -> &RefCell<RowVar<'a>> {
        match *self.rest.borrow() {
            RowVar::Unbound { .. } => &self.rest,
            RowVar::Link(row) => row.base_var(),
            RowVar::Poly { .. } => panic!("uninstantiated row variable"),
        }
    }

    pub fn base_var_level(&'a self) -> RefMut<'a, usize> {
        RefMut::map(self.base_var().borrow_mut(), |base_var| match base_var {
            RowVar::Unbound { level, .. } => level,
            _ => unreachable!(),
        })
    }
}

impl<'a> RowVar<'a> {
    pub fn unify(&mut self, other: &'a Row<'a>, ctx: &'a InferContext<'a>) {
        use RowVar::*;

        match self {
            Unbound { level: llevel, .. } => {
                let rlevel = &mut *other.base_var_level();
                *rlevel = *llevel.min(rlevel);
                *self = Link(other);
            }
            Link(left) => {
                left.unify(other, ctx);
            }
            Poly { .. } => panic!("uninstantiated row variable"),
        }
    }
}

pub struct TypeEnv<'a> {
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

pub struct InferContext<'arena> {
    types: Arena<Type<'arena>>,
    rows: Arena<Row<'arena>>,
    fresh_var_id: AtomicUsize,
}

impl<'a> InferContext<'a> {
    pub fn new() -> InferContext<'a> {
        InferContext {
            types: Arena::new(),
            rows: Arena::new(),
            fresh_var_id: AtomicUsize::new(0),
        }
    }

    pub fn infer(&'a self, expr: &Expr, env: &mut TypeEnv<'a>, level: usize) -> &'a Type<'a> {
        use Expr::*;

        match expr {
            ILit(_) => self.types.alloc(Type::Primitive(Primitive::Int)),
            BLit(_) => self.types.alloc(Type::Primitive(Primitive::Bool)),
            VarRef(name) => env.variable_types[name],
            Tuple(items) => self.types.alloc(Type::Apply(
                Constructor::Tuple,
                items
                    .iter()
                    .map(|item| self.infer(item, env, level))
                    .collect(),
            )),
            Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(label, expr)| (label.clone(), self.infer(expr, env, level)))
                    .collect();
                let rest = RefCell::new(RowVar::Unbound {
                    id: self.fresh_var_id(),
                    level,
                });
                let row = self.rows.alloc(Row {
                    columns: fields,
                    rest,
                });
                self.types.alloc(Type::Record(row))
            }
            Projection { record, label } => {
                let rest = RefCell::new(RowVar::Unbound {
                    id: self.fresh_var_id(),
                    level,
                });
                let field_type = self.alloc_var(level);
                let row = self.rows.alloc(Row {
                    columns: iter::once((label.clone(), field_type)).collect(),
                    rest,
                });
                let expected_record_type = self.types.alloc(Type::Record(row));
                let record_type = self.infer(record, env, level);
                record_type.unify(expected_record_type, self);
                field_type
            }
            If {
                condition,
                then,
                otherwise,
            } => {
                let condition_type = self.infer(condition, env, level);
                let then_type = self.infer(then, env, level);
                let otherwise_type = self.infer(otherwise, env, level);
                condition_type.unify(self.types.alloc(Type::Primitive(Primitive::Bool)), self);
                then_type.unify(otherwise_type, self);
                then_type
            }
            Lambda { argument, body } => {
                let argument_type = self.alloc_var(level);
                let return_type = env.with(argument.clone(), argument_type, |env| {
                    self.infer(body, env, level)
                });
                self.types.alloc(Type::Apply(
                    Constructor::Func,
                    vec![argument_type, return_type],
                ))
            }
            Apply {
                function,
                arguments,
            } => {
                let function_type = self.infer(function, env, level).instance(level, &self);
                let argument_types = arguments
                    .iter()
                    .map(|argument| self.infer(argument, env, level));
                let return_type = self.alloc_var(level);
                let expected_function_type = self.types.alloc(Type::Apply(
                    Constructor::Func,
                    argument_types.chain(iter::once(return_type)).collect(),
                ));
                function_type.unify(expected_function_type, self);
                return_type
            }
            Let {
                variable,
                definition,
                body,
            } => {
                let definition_type = self
                    .infer(definition, env, level + 1)
                    .generalized(level, &self);
                env.with(variable.clone(), definition_type, |env| {
                    self.infer(body, env, level)
                })
            }
        }
    }

    pub fn fresh_var_id(&self) -> usize {
        self.fresh_var_id.load(Ordering::Relaxed)
    }

    fn alloc_var(&'a self, level: usize) -> &'a Type<'a> {
        let id = self.fresh_var_id.fetch_add(1, Ordering::Relaxed);
        self.types.alloc(Type::new_unbound_var(id, level))
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
        ast! {
            let make_pair = (func x => let f = (func y => (x, y)) in f) in make_pair
        },
        ast! {
            let make_pair = (func x => let f = (func y => (x, y)) in f) in
            let pair_1 = ((make_pair 1) true) in
            let pair_2 = (let make_pair = (make_pair true) in (make_pair true)) in
            pair_1, pair_2
        },
        ast! {
            let f = (func record =>
                if (record.foo) then (record.bar) else (record.baz))
            in f
        },
    ];
    for ast in asts {
        println!("AST: {:?}", ast);
        println!("");
        let mut env = TypeEnv::new();
        let ctx = InferContext::new();
        let ty = ctx.infer(&ast, &mut env, 0);
        println!("Type: {}", ty);
        println!("")
    }
}
