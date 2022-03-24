use std::{cell::RefCell, collections::HashMap};

type VarId = usize;

#[derive(Debug)]
enum Expr {
    Let {
        new_var: VarId,
        def: Box<Expr>,
        body: Box<Expr>,
    },
    Fun {
        arg: VarId,
        body: Box<Expr>,
    },
    App {
        fun: Box<Expr>,
        arg: Box<Expr>,
    },
    Ref {
        var: VarId,
    },
    Pair {
        e1: Box<Expr>,
        e2: Box<Expr>,
    },
    Zero,
    True,
    Add,
}

macro_rules! ast {
    (let $n:tt = $def:tt in $body:tt) => {
        Expr::Let {
            new_var: $n,
            def: Box::new(ast!($def)),
            body: Box::new(ast!($body)),
        }
    };
    ((fun $arg:tt => $body:tt)) => {
        Expr::Fun {
            arg: $arg,
            body: Box::new(ast!($body)),
        }
    };
    ((ref $n:tt)) => {
        Expr::Ref {
            var: $n,
        }
    };
    (app $fun:tt $arg:tt) => {
        Expr::App {
            fun: Box::new(ast!($fun)),
            arg: Box::new(ast!($arg)),
        }
    };
    (pair $e1:tt $e2:tt) => {
        Expr::Pair {
            e1: Box::new(ast!($e1)),
            e2: Box::new(ast!($e2)),
        }
    };
    (zero) => {
        Expr::Zero
    };
    (true) => {
        Expr::True
    };
    (add) => {
        Expr::Add
    };
    (($($tt:tt)+)) => {
        ast!($($tt)+)
    };
}

#[derive(Debug, PartialEq, Clone)]
enum Type {
    TyVar(usize),
    Fun(Box<Type>, Box<Type>),
    Int,
    Bool,
    Pair(Box<Type>, Box<Type>),
    PolyVar(VarId),
}

struct TyEnv {
    map: HashMap<VarId, Type>,
}

struct Inferer {
    ty_vars: Vec<RefCell<(Option<Type>, usize)>>,
    level: usize,
}

trait TypeVariables {
    fn fresh_tyvar(&mut self, level: usize) -> Type;

    fn unify(&self, t1: &Type, t2: &Type);
}

impl TypeVariables for Vec<RefCell<(Option<Type>, usize)>> {
    fn fresh_tyvar(&mut self, level: usize) -> Type {
        self.push(RefCell::new((None, level)));
        Type::TyVar(self.len() - 1)
    }

    fn unify(&self, t1: &Type, t2: &Type) {
        use Type::*;
        match (t1, t2) {
            (Fun(in1, out1), Fun(in2, out2)) => {
                self.unify(in1, in2);
                self.unify(out1, out2);
            }
            (Pair(head1, tail1), Pair(head2, tail2)) => {
                self.unify(head1, head2);
                self.unify(tail1, tail2);
            }
            (TyVar(ref1), TyVar(ref2)) => {
                if ref1 == ref2 {
                    ()
                } else {
                    let mut ref1 = self[*ref1].borrow_mut();
                    let mut ref2 = self[*ref2].borrow_mut();
                    match (&ref1.0, &ref2.0) {
                        (None, None) => {
                            ref2.1 = ref1.1.min(ref2.1);
                            ref1.0 = Some(t2.clone())
                        }
                        (None, ref_t2 @ Some(_)) => ref1.0 = ref_t2.clone(),
                        (ref_t1 @ Some(_), None) => ref2.0 = ref_t1.clone(),
                        (Some(ref_t1), Some(ref_t2)) => self.unify(&ref_t1, &ref_t2),
                    }
                }
            }
            (TyVar(ref1), t2) => {
                let mut ref1 = self[*ref1].borrow_mut();
                match &ref1.0 {
                    None => ref1.0 = Some(t2.clone()),
                    Some(ref_t1) => self.unify(&ref_t1, t2),
                }
            }
            (t1, TyVar(ref2)) => {
                let mut ref2 = self[*ref2].borrow_mut();
                match &ref2.0 {
                    None => ref2.0 = Some(t1.clone()),
                    Some(ref_t2) => self.unify(t1, &ref_t2),
                }
            }
            (t1, t2) => {
                if t1 != t2 {
                    panic!("unify diffent types, {:?} != {:?}", t1, t2);
                } else {
                    ()
                }
            }
        }
    }
}

impl Type {
    fn generalize(self, ctx: &mut Inferer) -> Type {
        use Type::*;
        match self {
            TyVar(var_id) => {
                let ref1 = ctx.ty_vars[var_id].borrow();
                match &ref1.0 {
                    None => {
                        if ref1.1 > ctx.level {
                            PolyVar(var_id)
                        } else {
                            self
                        }
                    }
                    Some(_) => self,
                }
            }
            Fun(arg, ret) => Fun(Box::new(arg.generalize(ctx)), Box::new(ret.generalize(ctx))),
            Pair(t1, t2) => Pair(Box::new(t1.generalize(ctx)), Box::new(t2.generalize(ctx))),
            Int | Bool | PolyVar(_) => self,
        }
    }

    fn instantiate(&self, ctx: &mut Inferer) -> Type {
        self.instantiate_inner(ctx, &mut HashMap::new())
    }

    fn instantiate_inner(&self, ctx: &mut Inferer, var_map: &mut HashMap<usize, Type>) -> Type {
        use Type::*;
        match self {
            PolyVar(var_id) => var_map
                .entry(*var_id)
                .or_insert_with(|| ctx.fresh_tyvar())
                .clone(),
            Fun(arg, ret) => Fun(
                Box::new(arg.instantiate_inner(ctx, var_map)),
                Box::new(ret.instantiate_inner(ctx, var_map)),
            ),
            Pair(t1, t2) => Pair(
                Box::new(t1.instantiate_inner(ctx, var_map)),
                Box::new(t2.instantiate_inner(ctx, var_map)),
            ),
            TyVar(var_id) => {
                let t = ctx.ty_vars[*var_id].borrow().0.clone();
                match t {
                    Some(t) => t.instantiate_inner(ctx, var_map),
                    None => self.clone(),
                }
            }
            Int | Bool => self.clone(),
        }
    }
}

impl Inferer {
    fn new() -> Self {
        Inferer {
            ty_vars: Vec::new(),
            level: 0,
        }
    }

    fn fresh_tyvar(&mut self) -> Type {
        self.ty_vars.fresh_tyvar(self.level)
    }

    fn infer(&mut self, env: &mut TyEnv, expr: &Expr) -> Type {
        match expr {
            Expr::Let { new_var, def, body } => {
                self.level += 1;
                let t_def = self.infer(env, def);
                self.level -= 1;
                let t_def = t_def.generalize(self);
                env.extended(*new_var, t_def, |env| self.infer(env, body))
            }
            Expr::Fun { arg, body } => {
                let t1 = self.fresh_tyvar();
                env.extended(*arg, t1.clone(), |env| {
                    Type::Fun(Box::new(t1), Box::new(self.infer(env, body)))
                })
            }
            Expr::App { fun, arg } => match self.infer(env, fun) {
                Type::Fun(mut t_in, t_out) => {
                    let mut t_arg = self.infer(env, arg);
                    self.ty_vars.unify(&mut t_in, &mut t_arg);
                    t_out.as_ref().clone()
                }
                mut t_fn @ Type::TyVar(_) => {
                    let mut t_in = self.fresh_tyvar();
                    let t_out = self.fresh_tyvar();
                    self.ty_vars.unify(
                        &mut t_fn,
                        &mut Type::Fun(Box::new(t_in.clone()), Box::new(t_out.clone())),
                    );
                    let mut t_arg = self.infer(env, arg);
                    self.ty_vars.unify(&mut t_in, &mut t_arg);
                    t_out
                }
                _ => panic!("apply non-fun type"),
            },
            Expr::Pair { e1, e2 } => {
                let t1 = self.infer(env, e1);
                let t2 = self.infer(env, e2);
                Type::Pair(Box::new(t1), Box::new(t2))
            }
            Expr::Zero => Type::Int,
            Expr::True => Type::Bool,
            Expr::Add => Type::Fun(
                Box::new(Type::Int),
                Box::new(Type::Fun(Box::new(Type::Int), Box::new(Type::Int))),
            ),
            Expr::Ref { var } => env.map[var].instantiate(self),
        }
    }
}

impl TyEnv {
    fn new() -> Self {
        TyEnv {
            map: HashMap::new(),
        }
    }

    fn extended<R>(&mut self, id: VarId, ty: Type, f: impl FnOnce(&mut TyEnv) -> R) -> R {
        self.map.insert(id, ty);
        let r = f(self);
        self.map.remove(&id);
        r
    }
}

fn main() {
    let ast = ast!(
        let 0 = (
            fun 1 => (
                let 2 = (
                    fun 3 => (pair (ref 1) (ref 3))
                ) in (
                ref 2
                )
            )
        ) in (
        let 4 = (app (ref 0) zero) in (
        let 5 = (app (ref 4) true) in (
        let 6 = (app (ref 0) (ref 5)) in (
        app (ref 6) true
        ))))
    );
    let mut inferer = Inferer::new();
    let t = inferer.infer(&mut TyEnv::new(), &ast);
    println!("{:?}", t);
    for (i, v) in inferer.ty_vars.iter().enumerate() {
        println!("{}: {:?}", i, v.borrow());
    }
}
