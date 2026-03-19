use std::sync::atomic::{AtomicU64, Ordering};

use Expr::*;

// A but good
pub type __<A> = &'static A;
pub(crate) fn __<A>(a: A) -> &'static A {
    Box::leak(Box::new(a))
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Variable {
    User(__<str>),
    SorryDeBruijn(__<str>, u128),
}

impl Variable {
    pub(crate) fn refresh(self) -> Variable {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        match self {
            Variable::User(x) | Variable::SorryDeBruijn(x, _) => {
                let k = COUNTER.fetch_add(1, Ordering::Relaxed);
                Variable::SorryDeBruijn(x, k as u128)
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Expr {
    Var(Variable),
    Type(usize),
    Pi(Variable, __<Expr>, __<Expr>),
    Lambda(Variable, __<Expr>, __<Expr>),
    App(__<Expr>, __<Expr>),
    Struct(__<[(__<str>, Expr)]>),
    /// Struct type. Binds a variable (typically `self`) that has the type being constructed,
    /// making it an unordered dependent record.
    StructTy(Variable, __<[(__<str>, Expr)]>),
    /// Record value with explicit type annotation: `make (ty) { a = e, ... }`.
    TypedStruct(__<Expr>, __<[(__<str>, Expr)]>),
    Field(__<Expr>, __<str>),
    /// `let x = e1 in e2`.
    Let(Variable, __<Expr>, __<Expr>),
    /// `let rec x: T = e1 in e2`.
    LetRec(Variable, __<Expr>, __<Expr>, __<Expr>),
    Eq(__<Expr>, __<Expr>),
    Refl(__<Expr>),
    Transport(__<(Expr, Expr)>),
    /// `todo ty` — has type `ty`, panics on normalization.
    Todo(__<Expr>),
}

pub trait ExprMapper {
    fn map_expr(&mut self, e: Expr) -> Expr;

    type SelfWithNewLifetime<'a>: ExprMapper;
    fn under_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The already-mapped type of `var`, if any.
        ty: Option<Expr>,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T;
    fn under_recursive_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The not-yet-mapped type of `var`.
        ty: Expr,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T {
        self.under_abstraction(var, Some(ty), f)
    }

    // Helper
    fn map_fields(&mut self, fields: __<[(__<str>, Expr)]>) -> __<[(__<str>, Expr)]> {
        let fields: Vec<_> = fields.iter().map(|&(n, e)| (n, self.map_expr(e))).collect();
        Box::leak(fields.into_boxed_slice())
    }
}

impl Expr {
    /// Apply a transformation to all direct subexpressions of this expression.
    pub fn map(self, v: &mut impl ExprMapper) -> Self {
        match self {
            Var(x) => Var(x),
            Type(k) => Type(k),
            App(e1, e2) => App(__(v.map_expr(*e1)), __(v.map_expr(*e2))),
            Pi(mut x, t, e) => {
                let t = v.map_expr(*t);
                let e = v.under_abstraction(&mut x, Some(t), |v| v.map_expr(*e));
                Pi(x, __(t), __(e))
            }
            Lambda(mut x, t, e) => {
                let t = v.map_expr(*t);
                let e = v.under_abstraction(&mut x, Some(t), |v| v.map_expr(*e));
                Lambda(x, __(t), __(e))
            }
            Let(mut x, e1, e2) => {
                let e1 = v.map_expr(*e1);
                let e2 = v.under_abstraction(&mut x, None, |ctx| ctx.map_expr(*e2));
                Let(x, __(e1), __(e2))
            }
            LetRec(mut x, ty, e1, e2) => {
                let (ty, e1, e2) = v.under_recursive_abstraction(&mut x, *ty, |ctx| {
                    (ctx.map_expr(*ty), ctx.map_expr(*e1), ctx.map_expr(*e2))
                });
                LetRec(x, __(ty), __(e1), __(e2))
            }
            Struct(fields) => Struct(v.map_fields(fields)),
            TypedStruct(ty, fields) => TypedStruct(__(v.map_expr(*ty)), v.map_fields(fields)),
            StructTy(mut x, fields) => {
                let fields =
                    v.under_recursive_abstraction(&mut x, self, |ctx| ctx.map_fields(fields));
                StructTy(x, fields)
            }
            Field(e, name) => Field(__(v.map_expr(*e)), name),
            Eq(a, b) => Eq(__(v.map_expr(*a)), __(v.map_expr(*b))),
            Refl(a) => Refl(__(v.map_expr(*a))),
            Transport((eq, f)) => Transport(__((v.map_expr(*eq), v.map_expr(*f)))),
            Todo(t) => Todo(__(v.map_expr(*t))),
        }
    }
}
