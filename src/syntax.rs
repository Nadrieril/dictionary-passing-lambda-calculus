use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use indexmap::IndexMap;
use ustr::Ustr;

use ExprKind::*;

use crate::semantics::FunctionShape;

pub type Fields = Arc<IndexMap<Ustr, Expr>>;

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Variable {
    User(Ustr),
    SorryDeBruijn(Ustr, u128),
}

impl Variable {
    pub fn user(s: &str) -> Variable {
        Variable::User(Ustr::from(s))
    }

    pub(crate) fn anon() -> Variable {
        Variable::user("_")
    }

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

#[derive(Clone, Debug)]
pub enum ExprKind {
    Var(Variable),
    Type(usize),

    /// `let x [: T] = e1 in e2`. Non-recursive.
    Let(Variable, Option<Expr>, Expr, Expr),
    /// `let rec x: T = e1 in e2`. A coinductive value, checked for productivity at type-checking
    /// time.
    LetRec(Variable, Expr, Expr, Expr),

    /// Function type. The last argument records the exhaustive set of locations where the variable
    /// is used in the function body, if known.
    Pi(Variable, Expr, Expr, Option<FunctionShape>),
    Lambda(Variable, Expr, Expr),
    App(Expr, Expr),

    /// Struct type. Binds a variable (typically `self`) that has the type being constructed,
    /// making it an unordered dependent record.
    StructTy(Variable, Fields),
    /// Struct value, optionally with explicit type annotation: `{ a = e }` or `make (ty) { a = e }`.
    Struct(Option<Expr>, Fields),
    Field(Expr, Ustr),

    Eq(Expr, Expr),
    Refl(Expr),
    Transport(Expr, Expr),

    /// `todo ty` has type `ty`, panics on normalization.
    Todo(Expr),
}

/// An expression, optionally annotated with its inferred type.
#[derive(Clone, Debug)]
pub struct ExprContents {
    pub kind: ExprKind,
    pub ty: Option<Expr>,
}

#[derive(Clone, Debug)]
pub struct Expr(Arc<ExprContents>);

pub trait ExprMapper {
    fn map_expr(&mut self, e: &Expr) -> Expr;

    type SelfWithNewLifetime<'a>: ExprMapper;
    fn under_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The already-mapped type of `var`, if any.
        ty: Option<&Expr>,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T;
    fn under_recursive_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The not-yet-mapped type of `var`.
        ty: &Expr,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T {
        self.under_abstraction(var, Some(ty), f)
    }

    // Helper
    fn map_fields(&mut self, fields: &IndexMap<Ustr, Expr>) -> Fields {
        Arc::new(fields.iter().map(|(n, e)| (*n, self.map_expr(e))).collect())
    }
}

impl Expr {
    fn new(kind: ExprKind, ty: Option<Expr>) -> Expr {
        Expr(Arc::new(ExprContents { kind, ty }))
    }

    pub fn kind(&self) -> &ExprKind {
        &self.0.kind
    }

    pub fn ty(&self) -> &Expr {
        self.0.ty.as_ref().expect("type annotation missing")
    }

    /// Apply a transformation to all direct subexpressions of this expression.
    pub fn map(&self, v: &mut impl ExprMapper) -> Self {
        let new_kind = match self.kind() {
            Var(x) => Var(*x),
            Type(k) => Type(*k),
            App(e1, e2) => App(v.map_expr(e1), v.map_expr(e2)),
            Pi(x, t, e, mentions) => {
                let mut x = *x;
                let t = v.map_expr(t);
                let e = v.under_abstraction(&mut x, Some(&t), |v| v.map_expr(e));
                Pi(x, t, e, mentions.clone())
            }
            Lambda(x, t, e) => {
                let mut x = *x;
                let t = v.map_expr(t);
                let e = v.under_abstraction(&mut x, Some(&t), |v| v.map_expr(e));
                Lambda(x, t, e)
            }
            Let(x, ty, e1, e2) => {
                let mut x = *x;
                let ty = ty.as_ref().map(|ty| v.map_expr(ty));
                let e1 = v.map_expr(e1);
                let e2 = v.under_abstraction(&mut x, ty.as_ref(), |ctx| ctx.map_expr(e2));
                Let(x, ty, e1, e2)
            }
            LetRec(x, ty, e1, e2) => {
                let mut x = *x;
                let ty = ty.clone();
                let e1 = e1.clone();
                let e2 = e2.clone();
                let (ty, e1, e2) = v.under_recursive_abstraction(&mut x, &ty, |ctx| {
                    (ctx.map_expr(&ty), ctx.map_expr(&e1), ctx.map_expr(&e2))
                });
                LetRec(x, ty, e1, e2)
            }
            Struct(ty, fields) => {
                Struct(ty.as_ref().map(|ty| v.map_expr(ty)), v.map_fields(&fields))
            }
            StructTy(x, fields) => {
                let mut x = *x;
                let self_expr = self.clone();
                let fields = v
                    .under_recursive_abstraction(&mut x, &self_expr, |ctx| ctx.map_fields(&fields));
                StructTy(x, fields)
            }
            Field(e, name) => Field(v.map_expr(e), *name),
            Eq(a, b) => Eq(v.map_expr(a), v.map_expr(b)),
            Refl(a) => Refl(v.map_expr(a)),
            Transport(eq, f) => Transport(v.map_expr(eq), v.map_expr(f)),
            Todo(t) => Todo(v.map_expr(t)),
        };
        let new_ty = self.0.ty.as_ref().map(|ty| v.map_expr(ty));
        Expr::new(new_kind, new_ty)
    }
}

impl ExprKind {
    pub fn into_expr(self) -> Expr {
        Expr::new(self, None)
    }

    pub fn with_ty(self, ty: Expr) -> Expr {
        Expr::new(self, Some(ty))
    }
}
