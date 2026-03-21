use std::{
    collections::{HashMap, VecDeque},
    fmt::{Display, Write},
};

use enum_as_inner::EnumAsInner;
use internment::Intern;
use itertools::Itertools;
use petgraph::{algo::toposort, prelude::DiGraphMap};
use ustr::Ustr;

use crate::*;
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

/// Term constructors. Some of these have a corresponding destructor (e.g. field access destructs
/// field construction), but not all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Constructor {
    Pi,
    Lambda,
    StructTyField(Ustr),
    StructField(Ustr),
    EqLeft,
    EqRight,
    Refl,
    TypeOf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, EnumAsInner)]
enum ConstructorPath {
    Empty,
    Cons(Intern<(ConstructorPath, Constructor)>),
}

impl ConstructorPath {
    fn new(ctors: impl IntoIterator<Item = Constructor>) -> Self {
        ctors
            .into_iter()
            .fold(Self::Empty, |acc, c| Self::Cons(Intern::new((acc, c))))
    }

    fn concat(self, other: Self) -> Self {
        other
            .iter()
            .fold(self, |acc, c| Self::Cons(Intern::new((acc, c))))
    }

    fn iter(&self) -> impl Iterator<Item = Constructor> {
        self.iter_prefixes().map(|(_, c)| c)
    }
    fn iter_prefixes(&self) -> impl Iterator<Item = (Self, Constructor)> {
        let mut elems = VecDeque::new();
        let mut cur = *self;
        while let Self::Cons(pair) = cur {
            elems.push_front(*pair);
            cur = pair.0;
        }
        elems.into_iter()
    }
    /// Iterates over all ways to split `self` into `(prefix, suffix)` such that
    /// `prefix.concat(suffix) == self`. Yields `len + 1` pairs.
    fn splits(&self) -> impl Iterator<Item = (Self, Self)> {
        let mut splits = vec![(*self, Self::new([]))];
        let mut ctors = VecDeque::new();
        let mut cur = *self;
        while let Self::Cons(pair) = cur {
            let (prefix, ctor) = *pair;
            ctors.push_front(ctor);
            splits.push((prefix, Self::new(ctors.iter().copied())));
            cur = prefix;
        }
        splits.into_iter()
    }

    fn display_on(&self, var: Variable) -> impl Display {
        let mut parts = vec![var.to_string()];
        let mut arg_count = 0usize;
        let n_args = |n| format!("({})", std::iter::repeat_n("_", n).format(", "));
        for ctor in self.iter() {
            match ctor {
                Constructor::Lambda | Constructor::Pi => {
                    arg_count += 1;
                }
                other => {
                    if arg_count > 0 {
                        parts.push(n_args(arg_count));
                        arg_count = 0;
                    }
                    parts.push(match other {
                        Constructor::Lambda | Constructor::Pi => unreachable!(),
                        Constructor::StructField(f) | Constructor::StructTyField(f) => {
                            format!(".{f}")
                        }
                        Constructor::TypeOf => format!(".value_of"),
                        Constructor::EqLeft => format!(".eq_left"),
                        Constructor::EqRight => format!(".eq_right"),
                        Constructor::Refl => format!(".refl_arg"),
                    });
                }
            }
        }
        if arg_count > 0 {
            parts.push(n_args(arg_count));
        }
        parts.into_iter().format("")
    }
}

/// Describes which sub-expression position we are in within the expression tree.
/// One variant per nested `Expr` location inside an `Expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumAsInner)]
pub enum PathElem {
    /// We're inside the given destructor.
    Construct(Constructor),
    /// We applied a destructor corresponding to this constructor.
    Destruct(Constructor),
    // Let / LetRec
    LetVal,
    LetTy,
    LetBody,
    LetRecTy,
    LetRecVal(Variable),
    LetRecBody,
    // Pi / Lambda
    PiType,
    LambdaType,
    // App
    AppArg,
    // Struct / StructTy
    StructAnnot,
    // Eq / Refl / Transport
    TransportFn,
    // Todo
    TodoArg,
}

#[derive(Debug, Default)]
pub struct EvalContext {
    /// The bindings in scope.
    bindings: Vec<(Variable, Binding)>,
    /// The path through the initial expression to the subexpression we're in the process of
    /// typechecking.
    path: Vec<PathElem>,
    /// For each `let rec val` we're inside of, compute a map of which constructor paths depend on
    /// each other. If this has no cycles, progress is guaranteed.
    /// A `x -> y` path in the graph means that we know the value of `val.x` to be `val.y`. At the
    /// end, the lhs of edges will be all the subplaces of `val` that recursively depend on `val`.
    progress_graphs: HashMap<Variable, DiGraphMap<ConstructorPath, ()>>,
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
                let binding = self
                    .lookup_binding(*x)
                    .expect(&format!("Failed to find variable {x}!"));
                let binding_ty = binding.ty.clone();
                if matches!(binding.kind, BindingKind::Nominal(..))
                    && let mut subpath = self
                        .path
                        .iter()
                        .copied()
                        .skip_while(|e| !matches!(e, PathElem::LetRecVal(v) if v == x))
                        .peekable()
                    && subpath.next().is_some()
                {
                    // We're inside a `let rec` definition, and we found a recursive reference.
                    let mut ctor_path = vec![];
                    while let Some(ctor) = subpath.next_if_map(|e| e.into_construct()) {
                        ctor_path.push(ctor);
                    }

                    let mut dtor_path = vec![];
                    while let Some(ctor) = subpath.next_if_map(|e| e.into_destruct()) {
                        dtor_path.push(ctor);
                    }
                    dtor_path.reverse();

                    let ctor_path = ConstructorPath::new(ctor_path);
                    let dtor_path = ConstructorPath::new(dtor_path);
                    if let Some(pe) = subpath.next() {
                        panic!(
                            "failed to prove progress of {x}: \
                            recursive mention found under a {pe:?}\n  \
                            location: {}",
                            ctor_path.display_on(*x),
                        );
                    } else {
                        // Here, the path was a series of constructors followed by a series of
                        // destructors. Iow, we're accessing the `dtor_path` projection of the
                        // current value and putting the result inside `ctor_path`. We record that
                        // dependency in the graph.
                        let graph = self.progress_graphs.entry(*x).or_default();
                        graph.add_edge(ctor_path, dtor_path, ());
                    }
                }
                return binding_ty;
            }
            Type(k) => return Type(k + 1),
            Pi(x, t1, t2) => {
                let k1 = self.infer_universe(PathElem::PiType, t1);
                let k2 = self.with_binding_in_scope(*x, Binding::abstrakt(t1), |ctx| {
                    ctx.infer_universe(PathElem::Construct(Constructor::Pi), t2)
                });
                Type(k1.max(k2))
            }
            Lambda(x, t, e) => {
                let _ = self.infer_universe(PathElem::LambdaType, t);
                let te = self.with_binding_in_scope(*x, Binding::abstrakt(t), |ctx| {
                    ctx.infer_type_inner(PathElem::Construct(Constructor::Lambda), e)
                });
                Pi(*x, t.clone(), __(te))
            }
            App(f, arg) => {
                let f_ty = self.infer_type_inner(PathElem::Destruct(Constructor::Lambda), f);
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
                        .map(|(&f, t)| {
                            let loc = PathElem::Construct(Constructor::StructTyField(f));
                            ctx.infer_universe(loc, t)
                        })
                        .max()
                        .unwrap_or(0)
                });
                Type(k)
            }
            Struct(None, fields) => {
                let ty_fields = fields
                    .iter()
                    .map(|(&n, e)| {
                        let loc = PathElem::Construct(Constructor::StructField(n));
                        (n, self.infer_type_inner(loc, e))
                    })
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
                    let loc = PathElem::Construct(Constructor::StructField(name));
                    let actual = self.infer_type_inner(loc, val);
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
                    // Progress means that all the subplaces of our coinductive value can be
                    // reduced to whnf. In the graph we have exactly which subplaces depend on
                    // which other one, which is enough information to virtually check all possible
                    // subplaces by looking for loops in a graph.
                    let mut graph = ctx.progress_graphs.remove(x).unwrap_or_default();
                    // If val.a = val.b and val.c = val.a.x, then we add val.c = val.b.x to the
                    // graph.
                    for (_, val) in graph.all_edges().map(|(p, v, ())| (p, v)).collect_vec() {
                        for (prefix, suffix) in val.splits() {
                            for prefix_val in graph.neighbors(prefix).collect_vec() {
                                graph.add_edge(val, prefix_val.concat(suffix), ());
                            }
                        }
                    }
                    let mut s = String::new();
                    for node in graph.nodes().sorted() {
                        for neighbor in graph.neighbors(node).sorted() {
                            let _ = writeln!(
                                &mut s,
                                "- {} <- {}",
                                node.display_on(*x),
                                neighbor.display_on(*x)
                            );
                        }
                    }
                    if toposort(&graph, None).is_err() {
                        panic!(
                            "failed to prove progress of {x}: \
                            recursive uses are not productive.\n\
                            dependency graph:\n{s}"
                        );
                    } else {
                        eprintln!("dependency graph for {x}:\n{s}");
                    }
                    ctx.infer_type_inner(PathElem::LetRecBody, e2)
                });
            }
            Field(e, name) => {
                let loc = PathElem::Destruct(Constructor::StructField(*name));
                let te = self.infer_type_inner(loc, e);
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
                let ta = self.infer_type_inner(PathElem::Construct(Constructor::EqLeft), a);
                let tb = self.infer_type_inner(PathElem::Construct(Constructor::EqRight), b);
                self.assert_equal(&ta, &tb);
                let k = self.infer_universe(PathElem::Destruct(Constructor::TypeOf), &ta);
                Type(k)
            }
            Refl(a) => {
                let _ = self.infer_type_inner(PathElem::Construct(Constructor::Refl), a);
                Eq(a.clone(), a.clone())
            }
            Transport(eq, f) => {
                let eq_ty = self.infer_type_inner(PathElem::Destruct(Constructor::Refl), eq);
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
        let _ = self.infer_type_inner(PathElem::Destruct(Constructor::TypeOf), &ty);
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
