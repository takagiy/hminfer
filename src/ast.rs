#[derive(Debug)]
pub enum Expr {
    VarRef(String),
    ILit(i64),
    BLit(bool),
    If {
        condition: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
    },
    Apply {
        function: Box<Expr>,
        arguments: Vec<Expr>,
    },
    Lambda {
        argument: String,
        body: Box<Expr>,
    },
    Let {
        variable: String,
        definition: Box<Expr>,
        body: Box<Expr>,
    },
}

#[macro_export]
macro_rules! ast {
    (($($e:tt)*)) => {
        ast!($($e)*)
    };
    (true) => {
        Expr::BLit(true)
    };
    (false) => {
        Expr::BLit(false)
    };
    ($e:ident) => {
        Expr::VarRef(stringify!($e).to_string())
    };
    ($e:literal) => {
        Expr::ILit($e)
    };
    (if $cond:tt then $then:tt else $otherwise:tt) => {
        Expr::If {
            condition: Box::new(ast!($cond)),
            then: Box::new(ast!($then)),
            otherwise: Box::new(ast!($otherwise)),
        }
    };
    (func $argument:ident => $($body:tt)*) => {
        Expr::Lambda {
            argument: stringify!($argument).to_string(),
            body: Box::new(ast!($($body)*)),
        }
    };
    (let $variable:ident = $definition:tt in $($body:tt)*) => {
        Expr::Let {
            variable: stringify!($variable).to_string(),
            definition: Box::new(ast!($definition)),
            body: Box::new(ast!($($body)*)),
        }
    };
    ($function:tt $($argument:tt)*) => {
        Expr::Apply {
            function: Box::new(ast!($function)),
            arguments: vec![ $(ast!($argument)),* ],
        }
    };
}
