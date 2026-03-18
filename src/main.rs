#![allow(dead_code)]
use Expr::*;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

mod parser;
mod printer;

// A but good
pub type __<A> = &'static A;
fn __<A>(a: A) -> &'static A {
    Box::leak(Box::new(a))
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum Variable {
    User(__<str>),
    SorryDeBruijn(__<str>, u128),
}

impl Variable {
    fn refresh(self) -> Variable {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        match self {
            Variable::User(x) | Variable::SorryDeBruijn(x, _) => {
                let k = COUNTER.fetch_add(1, Ordering::Relaxed);
                Variable::SorryDeBruijn(x, k as u128)
            }
        }
    }
}

pub type Abstraction = (Variable, Expr, Expr);

#[derive(Clone, Copy, Debug, Eq)]
pub enum Expr {
    Var(Variable),
    Type(usize),
    Pi(__<Abstraction>),
    Lambda(__<Abstraction>),
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
            Pi((x, t, e)) => {
                let mut x = *x;
                let t = v.map_expr(*t);
                let e = v.under_abstraction(&mut x, Some(t), |v| v.map_expr(*e));
                Pi(__((x, t, e)))
            }
            Lambda((x, t, e)) => {
                let mut x = *x;
                let t = v.map_expr(*t);
                let e = v.under_abstraction(&mut x, Some(t), |v| v.map_expr(*e));
                Lambda(__((x, t, e)))
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

    fn subst1(self, x: Variable, e: Expr) -> Expr {
        self.subst([(x, e)].into())
    }
    fn subst(self, s: HashMap<Variable, Expr>) -> Expr {
        struct Substituter(HashMap<Variable, Expr>);

        impl Substituter {
            fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
                let old = self.0.clone();
                let result = f(self);
                self.0 = old;
                result
            }
            fn subst(&mut self, e: Expr) -> Expr {
                match e {
                    Var(x) => self.0.get(&x).copied().unwrap_or(e),
                    _ => e.map(self),
                }
            }
        }
        impl ExprMapper for Substituter {
            fn map_expr(&mut self, e: Expr) -> Expr {
                self.subst(e)
            }

            type SelfWithNewLifetime<'a> = Self;
            fn under_abstraction<T>(
                &mut self,
                x: &mut Variable,
                _ty: Option<Expr>,
                f: impl FnOnce(&mut Self) -> T,
            ) -> T {
                self.scoped(|ctx| {
                    let x_fresh = x.refresh();
                    ctx.0.insert(*x, Var(x_fresh));
                    *x = x_fresh;
                    f(ctx)
                })
            }
        }

        Substituter(s).subst(self)
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        /// Alpha-equality for abstractions: freshen both binders to a common variable.
        fn eq_abstraction(a1: __<Abstraction>, a2: __<Abstraction>) -> bool {
            let (x, t1, e1) = *a1;
            let (y, t2, e2) = *a2;
            let z = x.refresh();
            t1 == t2 && e1.subst([(x, Var(z))].into()) == e2.subst([(y, Var(z))].into())
        }

        fn eq_fields(f1: &[(__<str>, Expr)], f2: &[(__<str>, Expr)]) -> bool {
            f1.len() == f2.len()
                && f1
                    .iter()
                    .all(|(n, e)| f2.iter().any(|(n2, e2)| n == n2 && e == e2))
        }

        match (*self, *other) {
            (Pi(a1), Pi(a2)) | (Lambda(a1), Lambda(a2)) => eq_abstraction(a1, a2),
            (Struct(f1), Struct(f2)) | (TypedStruct(_, f1), TypedStruct(_, f2)) => {
                eq_fields(f1, f2)
            }
            (StructTy(x1, f1), StructTy(x2, f2)) => {
                if f1.len() != f2.len() {
                    return false;
                }
                let z = x1.refresh();
                let s1: HashMap<_, _> = [(x1, Var(z))].into();
                let s2: HashMap<_, _> = [(x2, Var(z))].into();
                f1.iter().all(|(n, e)| {
                    f2.iter()
                        .any(|(n2, e2)| n == n2 && e.subst(s1.clone()) == e2.subst(s2.clone()))
                })
            }
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            (App(e11, e12), App(e21, e22)) => e11 == e21 && e12 == e22,
            (Field(e1, n1), Field(e2, n2)) => n1 == n2 && e1 == e2,
            (Let(x1, e1, b1), Let(x2, e2, b2)) => x1 == x2 && e1 == e2 && b1 == b2,
            (LetRec(x1, t1, e1, b1), LetRec(x2, t2, e2, b2)) => {
                x1 == x2 && t1 == t2 && e1 == e2 && b1 == b2
            }
            (Eq(a1, b1), Eq(a2, b2)) => a1 == a2 && b1 == b2,
            (Refl(a1), Refl(a2)) => a1 == a2,
            (Transport((eq1, f1)), Transport((eq2, f2))) => eq1 == eq2 && f1 == f2,
            (Todo(t1), Todo(t2)) => t1 == t2,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Binding {
    /// `None` for uninterpreted symbols and normalizing under binders.
    value: Option<Expr>,
    ty: Expr,
    /// Nominal variables are not unfolded by whnf. These come from `let rec` binders.
    nominal: bool,
}

#[derive(Debug, Default)]
struct Context(Vec<(Variable, Binding)>);

impl Context {
    fn get(&self, x: Variable) -> Binding {
        self.0
            .iter()
            .rev()
            .find(|elem| x == elem.0)
            .expect(&format!("Failed to find variable {x}!"))
            .1
    }
    fn lookup_ty(&self, x: Variable) -> Expr {
        self.get(x).ty
    }

    /// Add a new uninterpreted term to the environment. Used in tests.
    fn add_uninterpreted(&mut self, x: &'static str, t: Expr) {
        let x = Variable::User(x);
        self.0.push((
            x,
            Binding {
                ty: t,
                value: None,
                nominal: false,
            },
        ));
    }
    /// Add a value to the environment. Used in tests.
    fn add_val(&mut self, x: &'static str, value: Expr) {
        let x = Variable::User(x);
        let t = self.infer_type(value);
        self.0.push((
            x,
            Binding {
                ty: t,
                value: Some(value),
                nominal: false,
            },
        ));
    }
    /// Push a variable to the context stack.
    fn push(&mut self, x: Variable, t: Expr) {
        self.0.push((
            x,
            Binding {
                ty: t,
                value: None,
                nominal: false,
            },
        ));
    }
    /// Run `f` with a temporary scope: any `push` calls inside are undone on return.
    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let len = self.0.len();
        let result = f(self);
        self.0.truncate(len);
        result
    }

    /// Infers the type of an expression. Also typechecks that expression.
    fn infer_type(&mut self, e: Expr) -> Expr {
        let ty = match e {
            Var(x) => return self.lookup_ty(x),
            Type(k) => return Type(k + 1),
            Pi((x, t1, t2)) => {
                let k1 = self.infer_universe(*t1);
                let k2 = self.scoped(|ctx| {
                    ctx.push(*x, *t1);
                    ctx.infer_universe(*t2)
                });
                Type(k1.max(k2))
            }
            Lambda((x, t, e)) => {
                let _ = self.infer_universe(*t);
                let te = self.scoped(|ctx| {
                    ctx.push(*x, *t);
                    ctx.infer_type(*e)
                });
                Pi(__((*x, *t, te)))
            }
            App(f, arg) => {
                let f_ty = self.infer_type(*f);
                let Pi((x, s, t)) = self.whnf_unfold(f_ty) else {
                    panic!("Function expected.")
                };
                let arg_ty = self.infer_type(*arg);
                self.assert_equal(*s, arg_ty);
                t.subst1(*x, *arg)
            }
            StructTy(x, fields) => {
                let k = self.scoped(|ctx| {
                    ctx.push(x, e);
                    fields
                        .iter()
                        .map(|&(_, t)| ctx.infer_universe(t))
                        .max()
                        .unwrap_or(0)
                });
                Type(k)
            }
            Struct(fields) => {
                let ty_fields: Vec<_> = fields
                    .iter()
                    .map(|&(n, e)| (n, self.infer_type(e)))
                    .collect();
                StructTy(
                    Variable::User("self"),
                    Box::leak(ty_fields.into_boxed_slice()),
                )
            }
            TypedStruct(ty, fields) => {
                let _ = self.infer_universe(*ty);
                let StructTy(self_var, field_tys) = self.whnf_unfold(*ty) else {
                    panic!("Struct type expected for rec")
                };
                // Check each field against the expected type, with self = the rec expression.
                for &(name, val) in fields.iter() {
                    let expected = field_tys
                        .iter()
                        .find(|(n, _)| *n == name)
                        .unwrap_or_else(|| panic!("Field {name} not found in type"))
                        .1;
                    let expected = expected.subst1(self_var, e);
                    let actual = self.infer_type(val);
                    self.assert_equal(expected, actual);
                }
                *ty
            }
            Let(x, e1, e2) => {
                let t1 = self.infer_type(*e1);
                return self.scoped(|ctx| {
                    ctx.0.push((
                        x,
                        Binding {
                            ty: t1,
                            value: Some(*e1),
                            nominal: false,
                        },
                    ));
                    ctx.infer_type(*e2)
                });
            }
            LetRec(x, ty, e1, e2) => {
                let _ = self.infer_universe(*ty);
                return self.scoped(|ctx| {
                    // Push x with value immediately so it can reduce during
                    // its own typechecking (needed for self-referential types
                    // like `Trait` whose fields reference `Trait` applied to args).
                    // Marked nominal so whnf doesn't unfold it.
                    ctx.0.push((
                        x,
                        Binding {
                            ty: *ty,
                            value: Some(*e1),
                            nominal: true,
                        },
                    ));
                    let t1 = ctx.infer_type(*e1);
                    ctx.assert_equal(*ty, t1);
                    ctx.infer_type(*e2)
                });
            }
            Field(e, name) => {
                let te = self.infer_type(*e);
                let te = self.whnf_unfold(te);
                let StructTy(self_var, fields) = te else {
                    panic!("Struct type expected for field access, got `{te}`")
                };
                let field_ty = fields
                    .iter()
                    .find(|(n, _)| *n == name)
                    .unwrap_or_else(|| panic!("Field {name} not found"))
                    .1;
                field_ty.subst1(self_var, *e)
            }
            Eq(a, b) => {
                let ta = self.infer_type(*a);
                let tb = self.infer_type(*b);
                self.assert_equal(ta, tb);
                let k = self.infer_universe(ta);
                Type(k)
            }
            Refl(a) => {
                let _ = self.infer_type(*a);
                Eq(a, a)
            }
            Transport((eq, f)) => {
                let eq_ty = self.infer_type(*eq);
                let Eq(a, b) = self.whnf_unfold(eq_ty) else {
                    panic!("Equality type expected for transport")
                };
                let f_ty = self.infer_type(*f);
                let Pi(..) = self.whnf_unfold(f_ty) else {
                    panic!("Function expected for transport's second argument")
                };
                Pi(__((Variable::User("_"), App(f, a), App(f, b))))
            }
            Todo(t) => {
                let _ = self.infer_universe(*t);
                return *t;
            }
        };
        // Recursively check the type is well-formed.
        let _ = self.infer_type(ty);
        ty
    }
    fn infer_universe(&mut self, t: Expr) -> usize {
        match self.infer_type(t) {
            Type(k) => k,
            t => panic!("Type expected, got {t:?}."),
        }
    }

    /// Weak head normal form. Does not unfold nominal variables,
    /// giving them nominal equality semantics.
    fn whnf(&mut self, e: Expr) -> Expr {
        self.whnf_inner(e, false)
    }
    /// Weak head normal form, unfolding nominal variables too.
    /// Used in `infer_type` where we need to see through nominal types
    /// (e.g. to find StructTy for field access, Pi for application).
    fn whnf_unfold(&mut self, e: Expr) -> Expr {
        self.whnf_inner(e, true)
    }
    fn whnf_inner(&mut self, e: Expr, unfold_nominal: bool) -> Expr {
        match e {
            Var(x) => match self.0.iter().rev().find(|elem| x == elem.0) {
                Some((_, b))
                    if let Some(val) = b.value
                        && (unfold_nominal || !b.nominal) =>
                {
                    self.whnf_inner(val, unfold_nominal)
                }
                _ => Var(x),
            },
            App(e1, e2) => match self.whnf_inner(*e1, unfold_nominal) {
                Lambda((x, _, body)) => self.whnf_inner(body.subst1(*x, *e2), unfold_nominal),
                e1 => App(__(e1), e2),
            },
            Field(e, name) => match self.whnf_inner(*e, true) {
                Struct(fields) | TypedStruct(_, fields) => self.whnf_inner(
                    fields
                        .iter()
                        .find(|(n, _)| *n == name)
                        .unwrap_or_else(|| panic!("Field {name} not found"))
                        .1,
                    unfold_nominal,
                ),
                e => Field(__(e), name),
            },
            Let(x, e1, e2) => self.whnf_inner(e2.subst1(x, *e1), unfold_nominal),
            LetRec(x, ty, e1, e2) => {
                let fixpoint = LetRec(x, ty, e1, __(Var(x)));
                let e1_unrolled = e1.subst1(x, fixpoint);
                self.whnf_inner(e2.subst1(x, e1_unrolled), unfold_nominal)
            }
            Transport((eq, f)) => {
                let eq = self.whnf_inner(*eq, unfold_nominal);
                match eq {
                    // transport (refl x) f : fn(f x) -> f x  reduces to identity
                    Refl(x) => {
                        let y = Variable::User("_").refresh();
                        Lambda(__((y, App(f, x), Var(y))))
                    }
                    eq => Transport(__((eq, *f))),
                }
            }
            Todo(t) => panic!("tried to normalize `todo {t}`"),
            _ => e,
        }
    }

    /// Typecheck then fully normalize the value.
    fn normalize(&mut self, e: Expr) -> Expr {
        struct Normalizer<'a>(&'a mut Context);

        impl<'a> ExprMapper for Normalizer<'a> {
            fn map_expr(&mut self, e: Expr) -> Expr {
                self.0.whnf(e).map(self)
            }

            type SelfWithNewLifetime<'b> = Normalizer<'b>;
            fn under_abstraction<T>(
                &mut self,
                var: &mut Variable,
                ty: Option<Expr>,
                f: impl for<'b> FnOnce(&mut Normalizer<'b>) -> T,
            ) -> T {
                let ty = ty.expect("found a `let` after wnhf");
                self.0.scoped(|ctx| {
                    ctx.push(*var, ty);
                    f(&mut Normalizer(ctx))
                })
            }
        }

        let _ = self.infer_type(e);
        Normalizer(self).map_expr(e)
    }

    fn assert_equal(&mut self, e1: Expr, e2: Expr) {
        if !self.equal(e1, e2) {
            panic!("`{e1}` and `{e2}` are not equal.")
        }
    }
    fn equal(&mut self, e1: Expr, e2: Expr) -> bool {
        let e1 = self.whnf(e1);
        let e2 = self.whnf(e2);
        // Recurse into sub-expressions, applying whnf at each level.
        match (e1, e2) {
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            // Undecidable, let's not even try.
            (Lambda(..), Lambda(..)) => false,
            (Pi(a1), Pi(a2)) => {
                let (x, t1, e1) = *a1;
                let (y, t2, e2) = *a2;
                let z = x.refresh();
                self.equal(t1, t2) && self.equal(e1.subst1(x, Var(z)), e2.subst1(y, Var(z)))
            }
            // Should only happen for uninterpreted symbols.
            (App(f1, a1), App(f2, a2)) => self.equal(*f1, *f2) && self.equal(*a1, *a2),
            (Struct(f1), Struct(f2)) | (TypedStruct(_, f1), TypedStruct(_, f2)) => {
                f1.len() == f2.len()
                    && f1
                        .iter()
                        .all(|(n, e)| f2.iter().any(|(n2, e2)| n == n2 && self.equal(*e, *e2)))
            }
            (StructTy(x1, f1), StructTy(x2, f2)) => {
                if f1.len() != f2.len() {
                    return false;
                }
                // Fields are under the self-binder; compare syntactically.
                let z = x1.refresh();
                f1.iter().all(|(n, e)| {
                    f2.iter()
                        .any(|(n2, e2)| n == n2 && e.subst1(x1, Var(z)) == e2.subst1(x2, Var(z)))
                })
            }
            (Field(e1, n1), Field(e2, n2)) => n1 == n2 && self.equal(*e1, *e2),
            (Eq(a1, b1), Eq(a2, b2)) => self.equal(*a1, *a2) && self.equal(*b1, *b2),
            (Refl(a1), Refl(a2)) => self.equal(*a1, *a2),
            (Transport((eq1, f1)), Transport((eq2, f2))) => {
                self.equal(*eq1, *eq2) && self.equal(*f1, *f2)
            }
            (Todo(t1), Todo(t2)) => t1 == t2,
            _ => false,
        }
    }
}

fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Expr {
        parser::parse(s).unwrap()
    }

    #[test]
    fn test_application() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.add_uninterpreted("s", p("fn(_: N) -> N"));
        ctx.add_val("three", p(r"\(f: fn(_: N) -> N) -> \(x: N) -> f (f (f x))"));

        let expr = p("three (three s) z");
        let normalized = ctx.normalize(expr);
        let ty = ctx.infer_type(expr);
        assert_eq!(
            normalized.to_string(),
            "s (s (s (s (s (s (s (s (s z))))))))"
        );
        assert_eq!(ty.to_string(), "N");
    }

    #[test]
    fn test_types() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));

        let sty = p("fn(_: fn(_: N) -> N) -> fn(_: N) -> N");
        assert_eq!(ctx.infer_type(sty).to_string(), "Type(0)");
    }

    #[test]
    fn test_structs() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));

        // Struct type has a type
        let sty = p("{ a: N, b: N }");
        assert_eq!(ctx.infer_type(sty).to_string(), "Type(0)");

        // Struct value has a struct type
        let sval = p("{ a = z, b = z }");
        assert_eq!(ctx.infer_type(sval).to_string(), "{ a: N, b: N }");

        // Field access
        let fa = p("{ a = z, b = z }.a");
        assert_eq!(ctx.infer_type(fa).to_string(), "N");
        assert_eq!(ctx.normalize(fa).to_string(), "z");

        // Field access via variable
        ctx.add_val("p", p("{ a = z, b = z }"));
        let fb = p("p.b");
        assert_eq!(ctx.infer_type(fb).to_string(), "N");
        assert_eq!(ctx.normalize(fb).to_string(), "z");
    }

    #[test]
    fn test_equality() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("M", Type(0));
        ctx.add_val("f", p(r"\(t: Type(0)) -> t == N"));

        // Eq type has a type
        let eq_ty = p("N == M");
        assert_eq!(ctx.infer_type(eq_ty).to_string(), "Type(1)");

        // refl has an Eq type
        let r = p("refl N");
        assert_eq!(ctx.infer_type(r).to_string(), "N == N");

        // transport type-checks: transport eq f : fn(f N) -> f M
        ctx.add_uninterpreted("eq", p("N == M"));
        let tr = p("transport eq f");
        let ty = ctx.infer_type(tr);
        let ty = ctx.normalize(ty);
        assert_eq!(ty.to_string(), "fn(_: N == N) -> M == N");

        // transport with refl reduces to identity
        assert_eq!(
            ctx.normalize(p("(transport (refl N) f) (refl N)"))
                .to_string(),
            "refl N"
        );
    }

    #[test]
    fn test_scoping() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("M", Type(0));
        ctx.add_uninterpreted("x", p("N"));

        // Type-checking a lambda that shadows x should not leak x:M
        ctx.infer_type(p(r"\(x: M) -> x"));
        assert_eq!(ctx.infer_type(p("x")).to_string(), "N");

        // Same for normalization
        ctx.normalize(p(r"\(x: M) -> x"));
        assert_eq!(ctx.infer_type(p("x")).to_string(), "N");

        // A defined variable should still reduce after normalizing a shadowing binder
        ctx.add_val("y", p("x"));
        ctx.normalize(p(r"\(y: M) -> y"));
        assert_eq!(ctx.normalize(p("y")).to_string(), "x");
    }

    #[test]
    fn test_capture_avoidance() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("x", p("N"));
        ctx.add_uninterpreted("y", p("N"));
        ctx.add_uninterpreted("z", p("N"));
        ctx.add_uninterpreted("s", p("fn(N) -> N"));

        assert_eq!(
            ctx.normalize(p(r"(\(y: N) -> \(x: N) -> y) x z"))
                .to_string(),
            "x"
        );
        assert_eq!(
            ctx.normalize(p(r"(\(x: N) -> \(x: N) -> x) y z"))
                .to_string(),
            "z"
        );
        assert_eq!(
            ctx.normalize(p(r"(\(x: N) -> (\(y: N) -> \(x: N) -> y) x) z y"))
                .to_string(),
            "z"
        );
        assert_eq!(
            ctx.normalize(p(r"(\(f: fn(N) -> N) -> f (f x)) (\(x: N) -> s x)"))
                .to_string(),
            "s (s x)"
        );

        ctx.add_val(
            "ap",
            p(r"\(t: Type(0)) -> \(u: Type(0)) -> \(f: fn(t) -> u) -> \(x: t) -> f x"),
        );
        assert_eq!(
            ctx.normalize(p("ap (fn(N) -> N) (fn(N) -> N) (ap N N)")),
            p(r"\(x1: fn(N) -> N) -> \(x2: N) -> x1 x2")
        );
    }

    #[test]
    fn test_equality_capture() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("x", Type(0));

        let id_ty = p("fn(x: Type(0)) -> x");
        let const_ty = p("fn(y: Type(0)) -> x");
        assert!(!ctx.equal(id_ty, const_ty));
    }

    #[test]
    fn test_rec() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));

        let r = p("make ({ a: N }) { a = z }");
        assert_eq!(ctx.infer_type(r).to_string(), "{ a: N }");
        assert_eq!(
            ctx.normalize(p("make ({ a: N }) { a = z }.a")).to_string(),
            "z"
        );

        ctx.add_val("MyTy", p("{ val: N, same: self.val == self.val }"));
        let r = p("make (MyTy) { val = z, same = refl z }");
        assert_eq!(ctx.infer_type(r).to_string(), "MyTy");
    }

    #[test]
    fn test_let() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.add_uninterpreted("s", p("fn(N) -> N"));

        // Basic let
        assert_eq!(ctx.normalize(p("let x = z in s x")).to_string(), "s z");
        assert_eq!(ctx.infer_type(p("let x = z in x")).to_string(), "N");

        // Nested let
        assert_eq!(
            ctx.normalize(p("let x = z in let y = s x in s y"))
                .to_string(),
            "s (s z)"
        );
    }

    #[test]
    fn test_let_rec() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));

        // let rec with self-referential struct — field access through the fixpoint
        let expr = p(r"
            let rec x: { a: N, b: self.a == self.a } = make ({ a: N, b: self.a == self.a }) { a = z, b = refl z }
            in x.a
        ");
        assert_eq!(ctx.normalize(expr).to_string(), "z");

        // let rec where a later field references an earlier one via self
        let expr = p(r"
            let rec x: { a: N, b: N } = { a = z, b = x.a }
            in x.b
        ");
        assert_eq!(ctx.normalize(expr).to_string(), "z");
    }

    #[test]
    fn test_todo() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));

        // todo has the declared type
        assert_eq!(ctx.infer_type(p("todo N")).to_string(), "N");
        // todo works in larger expressions
        assert_eq!(
            ctx.infer_type(p(r"\(x: N) -> todo N")).to_string(),
            "fn(x: N) -> N"
        );
    }

    #[test]
    #[should_panic(expected = "tried to normalize")]
    fn test_reject_normalize_todo() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.normalize(p("todo N"));
    }

    #[test]
    #[should_panic(expected = "not equal")]
    fn test_reject_rec_self_mismatch() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("M", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.add_uninterpreted("m", p("M"));
        ctx.add_val("T", p("{ a: Type(0), b: Type(0), eq: self.a == self.b }"));
        ctx.infer_type(p("make (T) { a = N, b = M, eq = refl N }"));
    }

    #[test]
    fn test_traits() {
        let mut ctx = Context::default();
        ctx.add_val(
            "Clone",
            p(r"\(t: Type(0)) -> {
                clone_method: fn(_: t) -> t,
            }"),
        );
        ctx.add_val(
            "Copy",
            p(r"\(t: Type(0)) -> {
                clone_supertrait: Clone t,
            }"),
        );
        ctx.add_val(
            "Iterator",
            p(r"\(t: Type(0)) -> {
                item_ty: Type(0),
                next_method: fn(t) -> self.item_ty,
            }"),
        );
        ctx.add_val(
            "IntoIterator",
            p(r"\(t: Type(0)) -> {
                item_ty: Type(0),
                into_iter_ty: Type(0),
                iterator_bound: Iterator self.into_iter_ty,
                type_eq: self.item_ty == self.iterator_bound.item_ty,
            }"),
        );
    }

    #[test]
    fn test_unsound_traits() {
        // Reproduce https://github.com/rust-lang/rust/issues/135246#issuecomment-4066328421
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.normalize(p(
            r"
            // Helpers
            let symmetry: fn(a: Type(0)) -> fn(b: Type(0)) -> fn(a == b) -> b == a =
                \(a: Type(0)) ->
                \(b: Type(0)) ->
                \(ab: a == b) ->
                transport ab (\(x: Type(0)) -> x == a) (refl a)
            in
            let transitivity: fn(a: Type(0)) -> fn(b: Type(0)) -> fn(c: Type(0)) -> fn(a == b) -> fn(b == c) -> a == c =
                \(a: Type(0)) ->
                \(b: Type(0)) ->
                \(c: Type(0)) ->
                \(ab: a == b) ->
                \(bc: b == c) ->
                transport bc (\(x: Type(0)) -> a == x) ab
            in

            // trait Trait<R>: Sized {
            //     type Proof: Trait<R, Proof = Self>;
            // }
            let rec Trait: fn(Type(0)) -> fn(Type(0)) -> Type(1) = \(t: Type(0)) -> \(r: Type(0)) -> {
                proof: Type(0),
                proof_impl: Trait self.proof r,
                proof_impl_constraint: self.proof_impl.proof == t,
            } in

            // impl<L, R> Trait<R> for L
            // where
            //     L: Trait<R>, // unsound if all trait bounds are coinductive
            //     // unsoundness: in impl, use item bounds to normalize
            //     // `<L::Proof as Trait<R>>::Proof = L`
            //     R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>,
            // {
            //     type Proof = R;
            // }
            let TraitImpl =
                \(l: Type(0)) ->
                \(r: Type(0)) ->
                \(l_trait: Trait l r) ->
                \(r_trait: Trait r r) ->
                \(r_trait_constraint: r_trait.proof == l_trait.proof_impl.proof) ->
            make (Trait l r) {
                proof = r,
                proof_impl = r_trait,
                proof_impl_constraint =
                    let eq1: (l_trait.proof_impl.proof == l) = l_trait.proof_impl_constraint in
                    let eq2: (r_trait.proof == l) = transitivity r_trait.proof l_trait.proof_impl.proof l r_trait_constraint eq1 in
                    eq2
            }
            in

            // First coinductive impl dictionary.
            let IdTraitImpl: fn(r: Type(0)) -> Trait r r =
                \(r: Type(0)) ->
                let rec Impl: Trait r r = TraitImpl r r Impl Impl (refl Impl.proof_impl.proof)
                in Impl
            in
            // Second coinductive impl dictionary.
            let GeneralTraitImpl: fn(l: Type(0)) -> fn(r: Type(0)) -> Trait l r =
                \(l: Type(0)) ->
                \(r: Type(0)) ->
                let rec Impl: Trait l r =
                    let l_trait: Trait l r = Impl in
                    let r_trait: Trait r r = IdTraitImpl r in
                    let r_trait_constraint: (r_trait.proof == l_trait.proof_impl.proof) = refl (l_trait.proof_impl.proof) in
                    TraitImpl l r l_trait r_trait r_trait_constraint
                in Impl
            in
            // Boom!
            let transmute: fn(l: Type(0)) -> fn(r: Type(0)) -> l == r =
                \(l: Type(0)) ->
                \(r: Type(0)) ->
                let l_impl: Trait l r = GeneralTraitImpl l r in
                symmetry r l (l_impl.proof_impl_constraint)
            in

            // this creates a value of type `N` which is uninterpreted hihi (and stack overflows)
            // transport (transmute {} N) (\(x: Type(0)) -> x) {=}
            {=}
            "
        ));
    }

    // --- Rejection tests ---

    #[test]
    #[should_panic(expected = "Function expected")]
    fn test_reject_apply_non_function() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.infer_type(p("z z"));
    }

    #[test]
    #[should_panic(expected = "not equal")]
    fn test_reject_arg_type_mismatch() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("M", Type(0));
        ctx.add_uninterpreted("f", p("fn(_: N) -> N"));
        ctx.add_uninterpreted("m", p("M"));
        // f expects N but gets M
        ctx.infer_type(p("f m"));
    }

    #[test]
    #[should_panic(expected = "Type expected")]
    fn test_reject_value_as_type() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        // z is a value, not a type — can't use as binder type
        ctx.infer_type(p(r"\(x: z) -> x"));
    }

    #[test]
    #[should_panic(expected = "Struct type expected")]
    fn test_reject_field_on_non_struct() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.infer_type(p("z.a"));
    }

    #[test]
    #[should_panic(expected = "Field b not found")]
    fn test_reject_missing_field() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.infer_type(p("{ a = z }.b"));
    }

    #[test]
    #[should_panic(expected = "not equal")]
    fn test_reject_eq_different_types() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        // z : N and N : Type(0) — different types
        ctx.infer_type(p("z == N"));
    }

    #[test]
    #[should_panic(expected = "Equality type expected")]
    fn test_reject_transport_non_eq() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("z", p("N"));
        ctx.add_uninterpreted("f", p("fn(_: N) -> N"));
        ctx.infer_type(p("transport z f"));
    }

    #[test]
    #[should_panic(expected = "Function expected for transport")]
    fn test_reject_transport_non_function() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("x", p("N"));
        ctx.add_uninterpreted("eq", p("x == x"));
        // second arg must be a function
        ctx.infer_type(p("transport eq x"));
    }

    #[test]
    #[should_panic(expected = "not equal")]
    fn test_reject_transport_domain_mismatch() {
        let mut ctx = Context::default();
        ctx.add_uninterpreted("N", Type(0));
        ctx.add_uninterpreted("M", Type(0));
        ctx.add_uninterpreted("x", p("N"));
        ctx.add_uninterpreted("eq", p("x == x"));
        ctx.add_uninterpreted("f", p("fn(_: M) -> M"));
        // eq proves x == x where x: N, but f expects M
        ctx.infer_type(p("transport eq f"));
    }
}
