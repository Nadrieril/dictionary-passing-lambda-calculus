use crate::*;
use std::collections::HashMap;

use Expr::*;

impl Expr {
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

#[derive(Debug, Clone, Copy)]
pub struct Binding {
    /// `None` for uninterpreted symbols and normalizing under binders.
    value: Option<Expr>,
    ty: Expr,
    /// Nominal variables are not unfolded by whnf. These come from `let rec` binders.
    nominal: bool,
}

impl Binding {
    /// Create a binding whose only info we know is its type.
    pub fn with_ty(ty: Expr) -> Self {
        Self {
            value: None,
            ty,
            nominal: false,
        }
    }
    pub fn with_value(value: Expr, ty: Expr) -> Self {
        Self {
            value: Some(value),
            ty,
            nominal: false,
        }
    }
    pub fn nominal(value: Expr, ty: Expr) -> Self {
        Self {
            value: Some(value),
            ty,
            nominal: true,
        }
    }
}

#[derive(Debug, Default)]
pub struct EvalContext {
    bindings: Vec<(Variable, Binding)>,
}

impl EvalContext {
    fn lookup_binding(&self, x: Variable) -> Option<Binding> {
        self.bindings
            .iter()
            .rev()
            .find(|elem| x == elem.0)
            .map(|b| b.1)
    }

    fn push_binding(&mut self, x: Variable, b: Binding) {
        self.bindings.push((x, b));
    }
    /// Add a new uninterpreted term to the environment. Used in tests.
    pub fn add_uninterpreted(&mut self, x: &'static str, t: Expr) {
        let x = Variable::User(x);
        self.push_binding(x, Binding::with_ty(t));
    }
    /// Add a value to the environment. Used in tests.
    pub fn add_val(&mut self, x: &'static str, value: Expr) {
        let x = Variable::User(x);
        let t = self.infer_type(value);
        self.push_binding(x, Binding::with_value(value, t));
    }
    /// Run `f` with a temporary scope where the given binding is declared.
    fn with_binding_in_scope<T>(
        &mut self,
        x: Variable,
        b: Binding,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.push_binding(x, b);
        let result = f(self);
        self.bindings.pop().unwrap();
        result
    }

    /// Infers the type of an expression. Also typechecks that expression.
    pub fn infer_type(&mut self, e: Expr) -> Expr {
        let ty = match e {
            Var(x) => {
                return self
                    .lookup_binding(x)
                    .expect(&format!("Failed to find variable {x}!"))
                    .ty;
            }
            Type(k) => return Type(k + 1),
            Pi(x, t1, t2) => {
                let k1 = self.infer_universe(*t1);
                let k2 = self
                    .with_binding_in_scope(x, Binding::with_ty(*t1), |ctx| ctx.infer_universe(*t2));
                Type(k1.max(k2))
            }
            Lambda(x, t, e) => {
                let _ = self.infer_universe(*t);
                let te =
                    self.with_binding_in_scope(x, Binding::with_ty(*t), |ctx| ctx.infer_type(*e));
                Pi(x, t, __(te))
            }
            App(f, arg) => {
                let f_ty = self.infer_type(*f);
                let Pi(x, s, t) = self.whnf_unfold(f_ty) else {
                    panic!("Function expected.")
                };
                let arg_ty = self.infer_type(*arg);
                self.assert_equal(*s, arg_ty);
                t.subst1(x, *arg)
            }
            StructTy(x, fields) => {
                let k = self.with_binding_in_scope(x, Binding::with_ty(e), |ctx| {
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
                let te1 = self.infer_type(*e1);
                return self.with_binding_in_scope(x, Binding::with_value(*e1, te1), |ctx| {
                    ctx.infer_type(*e2)
                });
            }
            LetRec(x, ty, e1, e2) => {
                let _ = self.infer_universe(*ty);
                // Push x with value immediately so it can reduce during its own typechecking
                // (needed for self-referential types like `Trait` whose fields reference `Trait`
                // applied to args). Marked nominal so whnf doesn't unfold it.
                let binding = Binding::nominal(*e1, *ty);
                return self.with_binding_in_scope(x, binding, |ctx| {
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
                Pi(Variable::User("_"), __(App(f, a)), __(App(f, b)))
            }
            Todo(t) => {
                let _ = self.infer_universe(*t);
                return *t;
            }
        };
        // Recursively check the type is well-formed.
        let _ = self.infer_type(ty);
        self.whnf(ty)
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
            Var(x) => match self.lookup_binding(x) {
                Some(binding)
                    if let Some(val) = binding.value
                        && (unfold_nominal || !binding.nominal) =>
                {
                    self.whnf_inner(val, unfold_nominal)
                }
                _ => Var(x),
            },
            App(e1, e2) => match self.whnf_inner(*e1, unfold_nominal) {
                Lambda(x, _, body) => self.whnf_inner(body.subst1(x, *e2), unfold_nominal),
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
                        Lambda(y, __(App(f, x)), __(Var(y)))
                    }
                    eq => Transport(__((eq, *f))),
                }
            }
            Todo(t) => panic!("tried to normalize `todo {t}`"),
            _ => e,
        }
    }

    /// Typecheck then fully normalize the value.
    pub fn normalize(&mut self, e: Expr) -> Expr {
        struct Normalizer<'a>(&'a mut EvalContext);

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
                self.0
                    .with_binding_in_scope(*var, Binding::with_ty(ty), |ctx| {
                        f(&mut Normalizer(ctx))
                    })
            }
        }

        let _ = self.infer_type(e);
        Normalizer(self).map_expr(e)
    }

    pub fn assert_equal(&mut self, e1: Expr, e2: Expr) {
        if !self.equal(e1, e2) {
            panic!(
                "\nassertion `left == right` failed\n  \
                 left: {e1}\n \
                 right: {e2}"
            );
        }
    }
    pub fn equal(&mut self, e1: Expr, e2: Expr) -> bool {
        let e1 = self.whnf(e1);
        let e2 = self.whnf(e2);
        // Recurse into sub-expressions, applying whnf at each level.
        match (e1, e2) {
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            (Lambda(x, t1, e1), Lambda(y, t2, e2)) => {
                // A little bit of alpha-equivalence.
                let z = x.refresh();
                self.equal(*t1, *t2) && self.equal(e1.subst1(x, Var(z)), e2.subst1(y, Var(z)))
            }
            (Pi(x, t1, e1), Pi(y, t2, e2)) => {
                let z = x.refresh();
                self.equal(*t1, *t2) && self.equal(e1.subst1(x, Var(z)), e2.subst1(y, Var(z)))
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
                    f2.iter().any(|(n2, e2)| {
                        n == n2 && self.equal(e.subst1(x1, Var(z)), e2.subst1(x2, Var(z)))
                    })
                })
            }
            (Field(e1, n1), Field(e2, n2)) => n1 == n2 && self.equal(*e1, *e2),
            (Eq(a1, b1), Eq(a2, b2)) => self.equal(*a1, *a2) && self.equal(*b1, *b2),
            (Refl(a1), Refl(a2)) => self.equal(*a1, *a2),
            (Transport((eq1, f1)), Transport((eq2, f2))) => {
                self.equal(*eq1, *eq2) && self.equal(*f1, *f2)
            }
            (Todo(t1), Todo(t2)) => self.equal(*t1, *t2),
            _ => false,
        }
    }
}
