use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock};

use indexmap::IndexMap;
use ustr::Ustr;

use ExprKind::*;

use crate::semantics::{Constructor, FunctionShape, SubExprLocation, TypeAnnotLocation};

pub type Fields = Arc<IndexMap<Ustr, Expr>>;

/// Source span for a parsed expression.
#[derive(Clone, Debug)]
pub struct Span {
    /// Byte offset of the start of the expression in the source.
    pub start: usize,
    /// Byte offset of the end of the expression in the source.
    pub end: usize,
    /// The original source string.
    pub source: Arc<str>,
}

impl Span {
    pub fn dummy() -> Span {
        static DUMMY_SP: LazyLock<Arc<str>> = LazyLock::new(|| Arc::from(""));
        Span {
            start: 0,
            end: 0,
            source: DUMMY_SP.clone(),
        }
    }

    pub fn is_dummy(&self) -> bool {
        self.start == 0 && self.end == 0
    }
    pub fn or<'a>(&'a self, other: &'a Self) -> &'a Self {
        if self.is_dummy() { other } else { self }
    }

    /// Display a formatted error message with source context, then panic.
    pub fn error(&self, msg: &str) -> ! {
        use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};
        if !self.is_dummy() {
            let report = &[Level::ERROR.primary_title(msg).element(
                Snippet::source(&*self.source)
                    .line_start(1)
                    .annotation(AnnotationKind::Primary.span(self.start..self.end)),
            )];
            eprintln!("{}", Renderer::styled().render(report));
        }
        panic!("{msg}");
    }
}

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
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Expr(Arc<ExprContents>);

pub trait ExprMapper {
    fn map_expr(&mut self, l: SubExprLocation, e: &Expr) -> Expr;

    type SelfWithNewLifetime<'a>: ExprMapper;
    fn under_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The already-mapped value of `var`, if any.
        val: Option<&Expr>,
        // The already-mapped type of `var`, if any.
        ty: Option<&Expr>,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T;
    fn under_recursive_abstraction<T>(
        &mut self,
        var: &mut Variable,
        // The not-yet-mapped value of `var`, if any.
        val: Option<&Expr>,
        // The not-yet-mapped type of `var`.
        ty: &Expr,
        f: impl for<'a> FnOnce(&mut Self::SelfWithNewLifetime<'a>) -> T,
    ) -> T {
        self.under_abstraction(var, val, Some(ty), f)
    }
}

impl Expr {
    fn new(kind: ExprKind, ty: Option<Expr>) -> Expr {
        Expr(Arc::new(ExprContents {
            kind,
            ty,
            span: Span::dummy(),
        }))
    }

    /// Attach a type to this expression.
    pub fn with_ty(self, ty: Expr) -> Expr {
        Expr(Arc::new(ExprContents {
            kind: self.kind().clone(),
            ty: Some(ty),
            span: self.span().clone(),
        }))
    }
    pub fn without_ty(&self) -> Expr {
        if self.opt_ty().is_some() {
            Expr(Arc::new(ExprContents {
                kind: self.kind().clone(),
                ty: None,
                span: self.span().clone(),
            }))
        } else {
            self.clone()
        }
    }
    /// Attach a source span to this expression.
    pub fn with_span(self, span: Span) -> Expr {
        Expr(Arc::new(ExprContents {
            kind: self.kind().clone(),
            ty: self.0.ty.clone(),
            span,
        }))
    }

    pub fn span(&self) -> &Span {
        &self.0.span
    }

    pub fn kind(&self) -> &ExprKind {
        &self.0.kind
    }
    pub fn as_type(&self) -> Option<usize> {
        self.kind().as_type()
    }
    pub fn unwrap_universe(&self) -> usize {
        self.as_type()
            .unwrap_or_else(|| self.error(&format!("Type expected, got `{self}`")))
    }

    /// Display a formatted error message with source context, then panic.
    pub fn error(&self, msg: &str) -> ! {
        self.span().error(msg)
    }

    pub fn opt_ty(&self) -> Option<Expr> {
        // To avoid infinite recursion, we don't store the type of `Type`s, so we recover that info
        // here.
        match self.kind() {
            Type(k) => Some(Type(k + 1).into_expr()),
            _ => self.0.ty.clone(),
        }
    }
    pub fn ty(&self) -> Expr {
        self.opt_ty()
            .unwrap_or_else(|| self.error("type annotation missing"))
    }

    /// Apply a transformation to all direct subexpressions of this expression.
    pub fn map(&self, v: &mut impl ExprMapper) -> Self {
        let new_kind = match self.kind() {
            Var(x) => Var(*x),
            Type(k) => Type(*k),
            App(f, arg) => {
                let f = v.map_expr(SubExprLocation::Destruct(Constructor::Lambda), f);
                let mentions = match &f.opt_ty() {
                    Some(ty) if let Pi(_, _, _, mentions) = ty.kind() => mentions.clone(),
                    _ => None,
                };
                let arg = v.map_expr(SubExprLocation::AppArg(mentions), arg);
                App(f, arg)
            }
            Pi(x, t, e, mentions) => {
                let mut x = *x;
                let t = v.map_expr(SubExprLocation::PiType, t);
                let e = v.under_abstraction(&mut x, None, Some(&t), |v| {
                    v.map_expr(SubExprLocation::Construct(Constructor::Pi), e)
                });
                Pi(x, t, e, mentions.clone())
            }
            Lambda(x, t, e) => {
                let mut x = *x;
                let t = v.map_expr(SubExprLocation::LambdaType, t);
                let e = v.under_abstraction(&mut x, None, Some(&t), |v| {
                    v.map_expr(SubExprLocation::Construct(Constructor::Lambda), e)
                });
                Lambda(x, t, e)
            }
            Let(x, ty, e1, e2) => {
                let ty = ty.as_ref().map(|ty| {
                    let loc = SubExprLocation::TypeAnnot(TypeAnnotLocation::Let);
                    v.map_expr(loc, ty)
                });
                let e1 = v.map_expr(SubExprLocation::LetVal, e1);
                let mut x = *x;
                let e2 = v.under_abstraction(&mut x, Some(&e1), ty.as_ref(), |ctx| {
                    ctx.map_expr(SubExprLocation::LetBody, e2)
                });
                Let(x, ty, e1, e2)
            }
            LetRec(x, ty, e1, e2) => {
                let orig_x = *x;
                let mut x = *x;
                let (ty, e1, e2) = v.under_recursive_abstraction(&mut x, Some(&e1), &ty, |ctx| {
                    (
                        ctx.map_expr(SubExprLocation::TypeAnnot(TypeAnnotLocation::LetRec), &ty),
                        ctx.map_expr(SubExprLocation::LetRecVal(orig_x), &e1),
                        ctx.map_expr(SubExprLocation::LetRecBody, &e2),
                    )
                });
                LetRec(x, ty, e1, e2)
            }
            Struct(ty, fields) => Struct(
                ty.as_ref().map(|ty| {
                    let loc = SubExprLocation::TypeAnnot(TypeAnnotLocation::StructMake);
                    v.map_expr(loc, ty)
                }),
                Arc::new(
                    fields
                        .iter()
                        .map(|(n, e)| {
                            let loc = SubExprLocation::Construct(Constructor::StructField(*n));
                            (*n, v.map_expr(loc, e))
                        })
                        .collect(),
                ),
            ),
            StructTy(x, fields) => {
                let mut x = *x;
                let fields = v.under_recursive_abstraction(&mut x, None, self, |ctx| {
                    Arc::new(
                        fields
                            .iter()
                            .map(|(n, e)| {
                                let loc =
                                    SubExprLocation::Construct(Constructor::StructTyField(*n));
                                (*n, ctx.map_expr(loc, e))
                            })
                            .collect(),
                    )
                });
                StructTy(x, fields)
            }
            Field(e, name) => {
                let loc = SubExprLocation::Destruct(Constructor::StructField(*name));
                Field(v.map_expr(loc, e), *name)
            }
            Eq(a, b) => Eq(
                v.map_expr(SubExprLocation::Construct(Constructor::EqLeft), a),
                v.map_expr(SubExprLocation::Construct(Constructor::EqRight), b),
            ),
            Refl(a) => Refl(v.map_expr(SubExprLocation::Construct(Constructor::Refl), a)),
            Transport(eq, f) => Transport(
                v.map_expr(SubExprLocation::Destruct(Constructor::Refl), eq),
                v.map_expr(SubExprLocation::TransportFn, f),
            ),
            Todo(t) => Todo(v.map_expr(SubExprLocation::TodoArg, t)),
        };
        let new_ty = self
            .0
            .ty
            .as_ref()
            .map(|ty| v.map_expr(SubExprLocation::TypeAnnot(TypeAnnotLocation::TypeOf), ty));
        Expr(Arc::new(ExprContents {
            kind: new_kind,
            ty: new_ty,
            span: self.span().clone(),
        }))
    }
}

impl ExprKind {
    pub fn as_type(&self) -> Option<usize> {
        match self {
            Type(k) => Some(*k),
            _ => None,
        }
    }

    pub fn into_expr(self) -> Expr {
        Expr::new(self, None)
    }
}
