use crate::*;
use ustr::Ustr;

use Expr::*;

impl Expr {
    fn subst1(&self, x: Variable, e: &Expr) -> Expr {
        self.subst(vec![(x, e.clone())])
    }
    fn subst(&self, s: Vec<(Variable, Expr)>) -> Expr {
        struct Substituter(Vec<(Variable, Expr)>);

        impl Substituter {
            fn lookup(&self, x: Variable) -> Option<&Expr> {
                self.0.iter().rev().find(|(v, _)| *v == x).map(|(_, e)| e)
            }
            fn subst(&mut self, e: &Expr) -> Expr {
                match e {
                    Var(x) => self.lookup(*x).unwrap_or(e).clone(),
                    _ => e.map(self),
                }
            }
        }
        impl ExprMapper for Substituter {
            fn map_expr(&mut self, e: &Expr) -> Expr {
                self.subst(e)
            }

            type SelfWithNewLifetime<'a> = Self;
            fn under_abstraction<T>(
                &mut self,
                x: &mut Variable,
                _ty: Option<&Expr>,
                f: impl FnOnce(&mut Self) -> T,
            ) -> T {
                let x_fresh = x.refresh();
                self.0.push((*x, Var(x_fresh)));
                *x = x_fresh;
                let result = f(self);
                self.0.pop();
                result
            }
        }

        Substituter(s).subst(self)
    }
}

#[derive(Debug, Clone)]
pub enum BindingKind {
    /// The value is known and is observed freely.
    Normal(Expr),
    /// The value is known but is only inspected when deconstructing it. Helps with inference.
    Nominal(Expr),
    /// The value is never inspected, only its type is known.
    Abstract,
}

#[derive(Debug, Clone)]
pub struct Binding {
    kind: BindingKind,
    ty: Expr,
}

impl Binding {
    /// Create a binding whose only info we know is its type.
    /// (`abstract` is a reserved keyword).
    pub fn abstrakt(ty: &Expr) -> Self {
        Self {
            kind: BindingKind::Abstract,
            ty: ty.clone(),
        }
    }
    pub fn with_value(value: &Expr, ty: &Expr) -> Self {
        Self {
            kind: BindingKind::Normal(value.clone()),
            ty: ty.clone(),
        }
    }
    pub fn nominal(value: &Expr, ty: &Expr) -> Self {
        Self {
            kind: BindingKind::Nominal(value.clone()),
            ty: ty.clone(),
        }
    }
    pub fn value(&self, unfold_nominal: bool) -> Option<&Expr> {
        match &self.kind {
            BindingKind::Normal(expr) => Some(expr),
            BindingKind::Nominal(expr) if unfold_nominal => Some(expr),
            BindingKind::Nominal(..) | BindingKind::Abstract => None,
        }
    }
}

/// Describes which sub-expression position we are in within the expression tree.
/// One variant per nested `Expr` location inside an `Expr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathElem {
    // Let / LetRec
    LetVal,
    LetTy,
    LetBody,
    LetRecTy,
    LetRecVal(Variable),
    LetRecBody,
    // Pi / Lambda
    PiType,
    PiBody,
    LambdaType,
    LambdaBody,
    // App
    AppFn,
    AppArg,
    // Struct / StructTy
    StructAnnot,
    StructField(Ustr),
    StructTyField(Ustr),
    // Field
    FieldBase,
    // Eq / Refl / Transport
    EqArg,
    ReflArg,
    TransportEq,
    TransportFn,
    // Todo
    TodoArg,
    // Whenever we traverse the type of a subexpression.
    HigherTy,
}

#[derive(Debug, Default)]
pub struct EvalContext {
    /// The bindings in scope.
    bindings: Vec<(Variable, Binding)>,
    /// The path through the initial expression to the subexpression we're in the process of
    /// typechecking.
    path: Vec<PathElem>,
}

impl EvalContext {
    fn lookup_binding(&self, x: Variable) -> Option<&Binding> {
        self.bindings
            .iter()
            .rev()
            .find(|elem| x == elem.0)
            .map(|b| &b.1)
    }

    fn push_binding(&mut self, x: Variable, b: Binding) {
        self.bindings.push((x, b));
    }
    /// Add a new uninterpreted term to the environment. Used in tests.
    pub fn add_uninterpreted(&mut self, x: &str, t: Expr) {
        let x = Variable::user(x);
        self.push_binding(x, Binding::abstrakt(&t));
    }
    /// Add a value to the environment. Used in tests.
    pub fn add_val(&mut self, x: &str, value: Expr) {
        let x = Variable::user(x);
        let t = self.infer_type_inner(PathElem::LetVal, &value);
        self.push_binding(x, Binding::with_value(&value, &t));
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

    /// Typecheck a sub-expression, tracking its position in the expression tree.
    fn infer_type_inner(&mut self, loc: PathElem, e: &Expr) -> Expr {
        self.path.push(loc);
        let ty = self.infer_type(e);
        self.path.pop();
        ty
    }
    /// Infers the type of an expression. Also typechecks that expression.
    pub fn infer_type(&mut self, e: &Expr) -> Expr {
        let ty = match e {
            Var(x) => {
                return self
                    .lookup_binding(*x)
                    .expect(&format!("Failed to find variable {x}!"))
                    .ty
                    .clone();
            }
            Type(k) => return Type(k + 1),
            Pi(x, t1, t2) => {
                let k1 = self.infer_universe(PathElem::PiType, t1);
                let k2 = self.with_binding_in_scope(*x, Binding::abstrakt(t1), |ctx| {
                    ctx.infer_universe(PathElem::PiBody, t2)
                });
                Type(k1.max(k2))
            }
            Lambda(x, t, e) => {
                let _ = self.infer_universe(PathElem::LambdaType, t);
                let te = self.with_binding_in_scope(*x, Binding::abstrakt(t), |ctx| {
                    ctx.infer_type_inner(PathElem::LambdaBody, e)
                });
                Pi(*x, t.clone(), __(te))
            }
            App(f, arg) => {
                let f_ty = self.infer_type_inner(PathElem::AppFn, f);
                let Pi(x, s, t) = self.whnf_unfold(&f_ty) else {
                    panic!("Function expected.")
                };
                let arg_ty = self.infer_type_inner(PathElem::AppArg, arg);
                self.assert_equal(&s, &arg_ty);
                t.subst1(x, arg)
            }
            StructTy(x, fields) => {
                let k = self.with_binding_in_scope(*x, Binding::abstrakt(e), |ctx| {
                    fields
                        .iter()
                        .map(|(&f, t)| ctx.infer_universe(PathElem::StructTyField(f), t))
                        .max()
                        .unwrap_or(0)
                });
                Type(k)
            }
            Struct(None, fields) => {
                let ty_fields = fields
                    .iter()
                    .map(|(&n, e)| (n, self.infer_type_inner(PathElem::StructField(n), e)))
                    .collect();
                StructTy(Variable::user("self"), __(ty_fields))
            }
            Struct(Some(ty), fields) => {
                let _ = self.infer_universe(PathElem::StructAnnot, ty);
                let StructTy(self_var, field_tys) = self.whnf_unfold(ty) else {
                    panic!("Struct type expected for rec")
                };
                // Check each field against the expected type, with self = the rec expression.
                for (&name, val) in fields.iter() {
                    let expected = field_tys
                        .get(&name)
                        .unwrap_or_else(|| panic!("Field {name} not found in type"))
                        .clone();
                    let expected = expected.subst1(self_var, e);
                    let actual = self.infer_type_inner(PathElem::StructField(name), val);
                    self.assert_equal(&expected, &actual);
                }
                (**ty).clone()
            }
            Let(x, ty, e1, e2) => {
                let te1 = self.infer_type_inner(PathElem::LetVal, e1);
                if let Some(ty) = ty {
                    let _ = self.infer_universe(PathElem::LetTy, ty);
                    self.assert_equal(ty, &te1);
                }
                return self.with_binding_in_scope(*x, Binding::with_value(e1, &te1), |ctx| {
                    ctx.infer_type_inner(PathElem::LetBody, e2)
                });
            }
            LetRec(x, ty, e1, e2) => {
                let _ = self.infer_universe(PathElem::LetRecTy, ty);
                // Push x with value immediately so it can reduce during its own typechecking
                // (needed for self-referential types like `Trait` whose fields reference `Trait`
                // applied to args). Marked nominal so whnf doesn't unfold it.
                let binding = Binding::nominal(e1, ty);
                return self.with_binding_in_scope(*x, binding, |ctx| {
                    let t1 = ctx.infer_type_inner(PathElem::LetRecVal(*x), e1);
                    ctx.assert_equal(ty, &t1);
                    ctx.infer_type_inner(PathElem::LetRecBody, e2)
                });
            }
            Field(e, name) => {
                let te = self.infer_type_inner(PathElem::FieldBase, e);
                let te = self.whnf_unfold(&te);
                let StructTy(self_var, fields) = te else {
                    panic!("Struct type expected for field access, got `{te}`")
                };
                let field_ty = fields
                    .get(name)
                    .unwrap_or_else(|| panic!("Field {name} not found"))
                    .clone();
                field_ty.subst1(self_var, e)
            }
            Eq(a, b) => {
                let ta = self.infer_type_inner(PathElem::EqArg, a);
                let tb = self.infer_type_inner(PathElem::EqArg, b);
                self.assert_equal(&ta, &tb);
                let k = self.infer_universe(PathElem::HigherTy, &ta);
                Type(k)
            }
            Refl(a) => {
                let _ = self.infer_type_inner(PathElem::ReflArg, a);
                Eq(a.clone(), a.clone())
            }
            Transport(eq, f) => {
                let eq_ty = self.infer_type_inner(PathElem::TransportEq, eq);
                let Eq(a, b) = self.whnf_unfold(&eq_ty) else {
                    panic!("Equality type expected for transport")
                };
                let f_ty = self.infer_type_inner(PathElem::TransportFn, f);
                let Pi(..) = self.whnf_unfold(&f_ty) else {
                    panic!("Function expected for transport's second argument")
                };
                Pi(
                    Variable::anon(),
                    __(App(f.clone(), a)),
                    __(App(f.clone(), b)),
                )
            }
            Todo(t) => {
                let _ = self.infer_universe(PathElem::TodoArg, t);
                return (**t).clone();
            }
        };
        // Recursively check the type is well-formed.
        let _ = self.infer_type_inner(PathElem::HigherTy, &ty);
        self.whnf(&ty)
    }
    fn infer_universe(&mut self, loc: PathElem, t: &Expr) -> usize {
        match self.infer_type_inner(loc, t) {
            Type(k) => k,
            t => panic!("Type expected, got {t:?}."),
        }
    }

    /// Weak head normal form. Does not unfold nominal variables,
    /// giving them nominal equality semantics.
    fn whnf(&mut self, e: &Expr) -> Expr {
        self.whnf_inner(e, false)
    }
    /// Weak head normal form, unfolding nominal variables too.
    /// Used in `infer_type` where we need to see through nominal types
    /// (e.g. to find StructTy for field access, Pi for application).
    fn whnf_unfold(&mut self, e: &Expr) -> Expr {
        self.whnf_inner(e, true)
    }
    fn whnf_inner(&mut self, e: &Expr, unfold_nominal: bool) -> Expr {
        match e {
            Var(x) => match self.lookup_binding(*x) {
                Some(binding) if let Some(val) = binding.value(unfold_nominal) => {
                    self.whnf_inner(&val.clone(), unfold_nominal)
                }
                _ => Var(*x),
            },
            App(e1, e2) => match self.whnf_inner(e1, unfold_nominal) {
                Lambda(x, _, body) => self.whnf_inner(&body.subst1(x, e2), unfold_nominal),
                e1 => App(__(e1), e2.clone()),
            },
            Field(e, name) => match self.whnf_inner(e, true) {
                Struct(_, fields) => {
                    let val = fields
                        .get(name)
                        .unwrap_or_else(|| panic!("Field {name} not found"));
                    self.whnf_inner(val, unfold_nominal)
                }
                e => Field(__(e), *name),
            },
            Let(x, _, e1, e2) => self.whnf_inner(&e2.subst1(*x, e1), unfold_nominal),
            LetRec(x, ty, e1, e2) => {
                let fixpoint = LetRec(*x, ty.clone(), e1.clone(), __(Var(*x)));
                let e1_unrolled = e1.subst1(*x, &fixpoint);
                self.whnf_inner(&e2.subst1(*x, &e1_unrolled), unfold_nominal)
            }
            Transport(eq, f) => {
                let eq_whnf = self.whnf_inner(eq, unfold_nominal);
                match eq_whnf {
                    // transport (refl x) f : fn(f x) -> f x  reduces to identity
                    Refl(x) => {
                        let y = Variable::anon().refresh();
                        Lambda(y, __(App(f.clone(), x.clone())), __(Var(y)))
                    }
                    eq => Transport(__(eq), f.clone()),
                }
            }
            Todo(t) => panic!("tried to normalize `todo {t}`"),
            _ => e.clone(),
        }
    }

    /// Typecheck then fully normalize the value.
    pub fn normalize(&mut self, e: &Expr) -> Expr {
        let _ = self.infer_type(e);
        self.normalize_no_typeck(e)
    }
    /// Recursively normalize the value.
    fn normalize_no_typeck(&mut self, e: &Expr) -> Expr {
        struct Normalizer<'a>(&'a mut EvalContext);

        impl<'a> ExprMapper for Normalizer<'a> {
            fn map_expr(&mut self, e: &Expr) -> Expr {
                self.0.whnf(e).map(self)
            }

            type SelfWithNewLifetime<'b> = Normalizer<'b>;
            fn under_abstraction<T>(
                &mut self,
                var: &mut Variable,
                ty: Option<&Expr>,
                f: impl for<'b> FnOnce(&mut Normalizer<'b>) -> T,
            ) -> T {
                let ty = ty.expect("found a `let` after whnf");
                self.0
                    .with_binding_in_scope(*var, Binding::abstrakt(ty), |ctx| {
                        f(&mut Normalizer(ctx))
                    })
            }
        }

        Normalizer(self).map_expr(e)
    }

    pub fn assert_equal(&mut self, e1: &Expr, e2: &Expr) {
        if !self.equal(e1, e2) {
            panic!(
                "\nassertion `left == right` failed\n  \
                 left: {e1}\n \
                 right: {e2}"
            );
        }
    }
    pub fn equal(&mut self, e1: &Expr, e2: &Expr) -> bool {
        let e1 = self.whnf(e1);
        let e2 = self.whnf(e2);
        // Recurse into sub-expressions, applying whnf at each level.
        match (&e1, &e2) {
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            (Lambda(x, t1, body1), Lambda(y, t2, body2)) => {
                // A little bit of alpha-equivalence.
                let z = x.refresh();
                self.equal(t1, t2)
                    && self.equal(&body1.subst1(*x, &Var(z)), &body2.subst1(*y, &Var(z)))
            }
            (Pi(x, t1, body1), Pi(y, t2, body2)) => {
                let z = x.refresh();
                self.equal(t1, t2)
                    && self.equal(&body1.subst1(*x, &Var(z)), &body2.subst1(*y, &Var(z)))
            }
            (App(f1, a1), App(f2, a2)) => self.equal(f1, f2) && self.equal(a1, a2),
            (Struct(_, f1), Struct(_, f2)) => {
                f1.len() == f2.len()
                    && f1
                        .iter()
                        .all(|(n, e)| f2.get(n).is_some_and(|e2| self.equal(e, e2)))
            }
            (StructTy(x1, f1), StructTy(x2, f2)) => {
                if f1.len() != f2.len() {
                    return false;
                }
                // Fields are under the self-binder; compare syntactically.
                let z = x1.refresh();
                f1.iter().all(|(n, e)| {
                    f2.get(n).is_some_and(|e2| {
                        self.equal(&e.subst1(*x1, &Var(z)), &e2.subst1(*x2, &Var(z)))
                    })
                })
            }
            (Field(e1, n1), Field(e2, n2)) => n1 == n2 && self.equal(e1, e2),
            (Eq(a1, b1), Eq(a2, b2)) => self.equal(a1, a2) && self.equal(b1, b2),
            (Refl(a1), Refl(a2)) => self.equal(a1, a2),
            (Transport(eq1, f1), Transport(eq2, f2)) => self.equal(eq1, eq2) && self.equal(f1, f2),
            (Todo(t1), Todo(t2)) => self.equal(t1, t2),
            _ => false,
        }
    }
}
