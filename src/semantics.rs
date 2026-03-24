use std::{
    collections::{HashMap, VecDeque},
    convert::Infallible,
    fmt::{Debug, Display, Write},
};

use enum_as_inner::EnumAsInner;
use fallible_iterator::{FallibleIterator, IteratorExt};
use internment::Intern;
use itertools::{Either, Itertools};
use petgraph::prelude::DiGraphMap;
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
    Abstract {
        /// Paths leading to uses of that variable.
        paths: Vec<Vec<PathElem>>,
    },
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
            kind: BindingKind::Abstract { paths: vec![] },
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
            BindingKind::Nominal(..) | BindingKind::Abstract { .. } => None,
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

/// A series of constructors.
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
    fn cons(self, c: Constructor) -> Self {
        Self::Cons(Intern::new((self, c)))
    }
    fn push(&mut self, c: Constructor) {
        *self = self.cons(c)
    }

    fn concat(self, other: Self) -> Self {
        other
            .iter()
            .fold(self, |acc, c| Self::Cons(Intern::new((acc, c))))
    }

    fn iter(self) -> impl Iterator<Item = Constructor> {
        self.iter_prefixes().map(|(_, c)| c)
    }
    fn iter_prefixes(self) -> impl Iterator<Item = (Self, Constructor)> {
        let mut elems = VecDeque::new();
        let mut cur = self;
        while let Self::Cons(pair) = cur {
            elems.push_front(*pair);
            cur = pair.0;
        }
        elems.into_iter()
    }
    /// Whether `self` starts with `prefix`, i.e. `self == prefix.concat(something)`.
    fn starts_with(self, prefix: Self) -> bool {
        self == prefix || self.iter_prefixes().any(|(p, _)| p == prefix)
    }

    fn rev_iter(self) -> impl Iterator<Item = Constructor> {
        let mut cur = self;
        std::iter::from_fn(move || {
            let (prefix, ctor) = **cur.as_cons()?;
            cur = prefix;
            Some(ctor)
        })
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

/// The path to a mention of a variable in a body. We only represent a simple kind of path: those
/// where a projection of the value (e.g. `(x a).foo.bar`) is stored directly inside a series of
/// constructors. E.g.:
///   { foo = |a: u32| (x a).foo.bar }
/// gives paths:
///   ctor_path = [Field(foo), Lambda]
///   dtor_path = [Lambda, Field(foo), Field(bar)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct MentionPath {
    ctor_path: ConstructorPath,
    dtor_path: ConstructorPath,
}

/// The shape of a function: the exhaustive set of locations where the input variable is used in
/// the function body. Used for progress checking.
pub type FunctionShape = __<[MentionPath]>;

impl MentionPath {
    /// The shape of the identity function: the variable is mentioned directly, with no
    /// projections nor constructors.
    fn identity() -> Self {
        MentionPath {
            ctor_path: ConstructorPath::Empty,
            dtor_path: ConstructorPath::Empty,
        }
    }

    /// Convert a location to a number of `MentionPath`s. There can be several if we encounter a
    /// function application that uses its argument several times.
    fn from_path<'a>(
        path: impl IntoIterator<Item = &'a PathElem> + Clone,
    ) -> Result<Vec<Self>, (ConstructorPath, PathElem)> {
        if path
            .clone()
            .into_iter()
            .any(|pe| matches!(pe, PathElem::AppArg(..) | PathElem::LetVal))
        {
            // Compute all the possible combinations of paths.
            path.into_iter()
                .map(|pe| match pe {
                    PathElem::AppArg(Some(mentions)) => {
                        // Each item here is a possible path we can take.
                        mentions.iter().map(|m| Either::Left(*m)).collect_vec()
                    }
                    // We skip paths bound to a `let` because we'll explore them when we encounter
                    // the binding instead.
                    PathElem::LetVal => vec![],
                    pe => vec![Either::Right(pe.clone())],
                })
                .multi_cartesian_product()
                .map(|vv: Vec<Either<MentionPath, PathElem>>| {
                    let path: Vec<PathElem> = vv
                        .into_iter()
                        .flat_map(|either| match either {
                            Either::Left(m) => Either::Left(m.to_path()),
                            Either::Right(pe) => Either::Right([pe].into_iter()),
                        })
                        .collect_vec();
                    Self::from_single_path(&path)
                })
                .try_collect()
        } else {
            Self::from_single_path(path).map(|x| vec![x])
        }
    }
    /// `from_path` but without support for function application.
    fn from_single_path<'a>(
        path: impl IntoIterator<Item = &'a PathElem> + Clone,
    ) -> Result<Self, (ConstructorPath, PathElem)> {
        let mut ctor_path = ConstructorPath::Empty;
        let mut dtor_path = vec![];
        for pe in path.into_iter().cloned() {
            match pe {
                PathElem::Construct(ctor) if dtor_path.is_empty() => {
                    ctor_path.push(ctor);
                }
                PathElem::Construct(ctor) if dtor_path.last() == Some(&ctor) => {
                    dtor_path.pop();
                }
                PathElem::Destruct(ctor) => {
                    dtor_path.push(ctor);
                }
                _ => return Err((ctor_path, pe)),
            }
        }

        dtor_path.reverse();
        let dtor_path = ConstructorPath::new(dtor_path);
        Ok(Self {
            ctor_path,
            dtor_path,
        })
    }
    fn to_path(self) -> impl Iterator<Item = PathElem> {
        let ctors = self.ctor_path.iter().map(PathElem::Construct);
        let dtors = self.dtor_path.rev_iter().map(PathElem::Destruct);
        ctors.chain(dtors)
    }
}

impl Debug for MentionPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "MentionPath({} = {})",
            self.ctor_path.display_on(Variable::user("output")),
            self.dtor_path.display_on(Variable::user("input")),
        )
    }
}

/// Describes which sub-expression position we are in within the expression tree.
/// One variant per nested `Expr` location inside an `Expr`.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum PathElem {
    /// We're inside the given destructor.
    Construct(Constructor),
    /// We applied a destructor corresponding to this constructor.
    Destruct(Constructor),
    // Let / LetRec
    LetVal,
    LetTy,
    LetRecTy,
    LetRecVal(Variable),
    LetRecBody,
    // Pi / Lambda
    PiType,
    LambdaType,
    // Argument of a function application. If known, stores the shape of the function.
    AppArg(Option<FunctionShape>),
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
    fn lookup_binding(&mut self, x: Variable) -> Option<&Binding> {
        let b = &mut self.bindings.iter_mut().rev().find(|elem| x == elem.0)?.1;
        if let BindingKind::Abstract { paths } = &mut b.kind {
            paths.push(self.path.clone());
        }
        Some(b)
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
        self.with_binding_in_scope_keep_binding(x, b, f).0
    }
    /// Like `with_binding_in_scope` and also returns the binding.
    fn with_binding_in_scope_keep_binding<T>(
        &mut self,
        x: Variable,
        b: Binding,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, Binding) {
        self.push_binding(x, b);
        let result = f(self);
        let (_, b) = self.bindings.pop().unwrap();
        (result, b)
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
                    .expect(&format!("Failed to find variable {x}!"))
                    .clone();
                let binding_ty = binding.ty;
                match binding.kind {
                    BindingKind::Normal(v) => {
                        if self
                            .path
                            .iter()
                            .any(|e| matches!(e, PathElem::LetRecVal(..)))
                        {
                            // A let-binding may contain recursive mentions of a recursive
                            // variable, so we re-typecheck it here.
                            let _ = self.infer_type(&v);
                        }
                    }
                    BindingKind::Nominal(..) => {
                        if let mut subpath = self.path.iter()
                            && subpath
                                .by_ref()
                                .find(|e| matches!(e, PathElem::LetRecVal(v) if v == x))
                                .is_some()
                        {
                            // We're inside a `let rec val` definition, and we found a recursive reference
                            // to `val`.
                            match MentionPath::from_path(subpath) {
                                Ok(mention_paths) => {
                                    // We can handle all the paths from the start of the `let rec` to here;
                                    // add them to the graph.
                                    for mention_path in mention_paths {
                                        let graph = self.progress_graphs.entry(*x).or_default();
                                        graph.add_edge(
                                            mention_path.ctor_path,
                                            mention_path.dtor_path,
                                            (),
                                        );
                                    }
                                }
                                Err((ctor_path, pe)) => {
                                    panic!(
                                        "failed to prove progress of {x}: \
                                        recursive mention found under a {pe:?}\n  \
                                        location: {}",
                                        ctor_path.display_on(*x),
                                    );
                                }
                            }
                        }
                    }
                    _ => (),
                }
                return binding_ty;
            }
            Type(k) => return Type(k + 1),
            Pi(x, t1, t2, _) => {
                let k1 = self.infer_universe(PathElem::PiType, t1);
                let k2 = self.with_binding_in_scope(*x, Binding::abstrakt(t1), |ctx| {
                    ctx.infer_universe(PathElem::Construct(Constructor::Pi), t2)
                });
                Type(k1.max(k2))
            }
            Lambda(x, t, e) => {
                let _ = self.infer_universe(PathElem::LambdaType, t);
                let (te, b) =
                    self.with_binding_in_scope_keep_binding(*x, Binding::abstrakt(t), |ctx| {
                        ctx.infer_type_inner(PathElem::Construct(Constructor::Lambda), e)
                    });
                let mentions = {
                    let BindingKind::Abstract { paths } = b.kind else {
                        unreachable!()
                    };
                    let cur_path_len = self.path.len() + 1;
                    // Each path is one location where the input variable is mentioned in the body.
                    // Each such location may give rise to several `MentionPath`s because of other
                    // function calls. We flatten everything here. If any of the locations could
                    // not be transformed to a `MentionPath`, we get `None` to ensure that the set
                    // of paths is always exhaustive..
                    paths
                        .into_iter()
                        .map(|p| MentionPath::from_path(&p[cur_path_len..]))
                        .transpose_into_fallible()
                        .map(|vec| {
                            Ok(vec
                                .into_iter()
                                .into_fallible()
                                .map_err(|x: Infallible| match x {}))
                        })
                        .flatten()
                        .collect()
                        .ok()
                };
                Pi(*x, t.clone(), __(te), mentions)
            }
            App(f, arg) => {
                let f_ty = self.infer_type_inner(PathElem::Destruct(Constructor::Lambda), f);
                let Pi(x, s, t, mentions) = self.whnf_unfold(&f_ty) else {
                    panic!("Function expected.")
                };
                let arg_ty = self.infer_type_inner(PathElem::AppArg(mentions), arg);
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
            Struct(ty, fields) => {
                let ty_fields = fields
                    .iter()
                    .map(|(&n, e)| {
                        let loc = PathElem::Construct(Constructor::StructField(n));
                        (n, self.infer_type_inner(loc, e))
                    })
                    .collect();
                let actual = StructTy(Variable::user("self"), __(ty_fields));
                if let Some(ty) = ty {
                    let _ = self.infer_universe(PathElem::StructAnnot, ty);
                    let StructTy(self_var, field_tys) = self.whnf_unfold(ty) else {
                        panic!("Struct type expected for rec")
                    };
                    let expected = StructTy(self_var.refresh(), field_tys).subst1(self_var, e);
                    self.assert_equal(&expected, &actual);
                    ty.as_ref().clone()
                } else {
                    actual
                }
            }
            Let(x, ty, e1, e2) => {
                let te1 = self.infer_type_inner(PathElem::LetVal, e1);
                if let Some(ty) = ty {
                    let _ = self.infer_universe(PathElem::LetTy, ty);
                    self.assert_equal(ty, &te1);
                }
                return self.with_binding_in_scope(*x, Binding::with_value(e1, &te1), |ctx| {
                    // No `PathElem` here: a `let` body doesn't count wrt constructors.
                    ctx.infer_type(e2)
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
                    // Progress means that all the subplaces (i.e. repeated destructor
                    // applications) of our coinductive value can be reduced to whnf. In the graph
                    // we computed which subplaces depend on which other ones.
                    //
                    // Call `g` our graph. Its nodes are constructor paths (that's not just field
                    // accesses, see `ConstructorPath`), and there's an edge `n -> m` if we could
                    // determine that `val.n` evaluates to `val.m` in finite steps.
                    //
                    // Build an infinite graph `G` as follows:
                    // for every `n` in `g` and suffix `s`, `n.s` is a node in `G`; `G` has an edge
                    // `n -> m` whenever `n = n'.s`, `m = m'.s`, and `n' -> m'` in `g`.
                    //
                    // The core property of our graph is that all the self-references of `val` on
                    // itself are of the form `val.path1 = val.path2`, where `path1 -> path2` is an
                    // edge in `G`.
                    //
                    // `g` has one more important property: if a -> b in `g` then a.x is not the
                    // source of another edge for any `x` even empty (iow, sources form an
                    // anti-chain under prefix ordering). This is equivalent to the statement that
                    // walking through `G` is deterministic, and that evaluation is deterministic.
                    //
                    // Lemma: If `n -> m` in `G`, then `val.n` evaluates to `val.m` in a finite
                    // number of steps.
                    // Proof: By construction, let `n = n'.s`, `m = m'.s` such that `n' -> m'` is
                    // an edge in `g`. From how we built `g`, evaluating `val.n'` gives `val.m'` in
                    // finite steps; adding extra projections on top doesn't change anything since
                    // we evaluate the subexpressions first.
                    //
                    // Claim: the expression is productive iff `G` has no infinite paths.
                    //
                    // Proof: The only recursion in our language is this coinduction (well, except
                    // dependent records, gotta fix that), and every binding in scope has been
                    // checked to be productive. Hence if the current expression does not involve
                    // `val`, it reduces to whnf. So wlog assume the current expression is of the
                    // form `val.path` (`path` isn't just field accesses, see `ConstructorPath`).
                    // Evaluating `val.path` involves evaluating all the `val.subpath` prefixes to
                    // whnf, then evaluating the final projection. Wlog assume that the prefixes
                    // reduced to whnf. Consider the expression we're left with. If it contains no
                    // mention of `val`, per previous argument it evaluates; hence wlog it mentions
                    // `val`. Per the property of our graph, `G` has an edge `path -> next`, and
                    // per the lemma evaluating `val.path` gives `val.next`, which must then be
                    // tried for whnf again. In summary, we have: if `path` is in the `G`,
                    // evaluating `val.path` takes an edge in that graph. If there is no edge, then
                    // we can reach whnf. So if `path` doesn't lead to an infinite path, `val.path`
                    // has a whnf.
                    let graph = ctx.progress_graphs.remove(x).unwrap_or_default();
                    // Let `W(n)` denote the walk starting from node `n`. Let `W(n).s` denote that
                    // same walk but with suffix `s` added to every node.
                    //
                    // Lemma: `W(n.s)` starts with `W(n).s`.
                    // Proof: By construction of `G`, all the edges taken in `W(n).s` are valid for
                    // `W(n.s)`. We conclude by determinism of walks in `G`.
                    //
                    // Lemma: If the last node of `W(n)` is not the prefix of a node in `g`, then
                    // `W(n.s) = W(n).s` for any `s`.
                    // Proof: The only way for `W(n.s)` to progress further than `W(n).s` is if the
                    // last node of `W(n).s` can take an edge that `W(n)` couldn't, hence there's
                    // some `s'` such that the last node of `W(n).s'` is in `g`.
                    //
                    // Lemma: Let `W(n)` be a walk in `G`. `n` can be written `m.s` such that `W(n)
                    // = W(m).s` and at least one node of `W(m)` is in `g`.
                    // Proof: We inductively construct `s`: if `W(n)` contains a node in `g`, we're
                    // done. Otherwise write `n = m.s` where `s` has length 1. By the previous
                    // lemmas, `W(m).s` is a prefix of `W(n)`. The last node `p` of `W(m)` is a
                    // prefix of a node in `g` iff `p.s` is in `g` or the prefix of a node in `g`.
                    // `p.s` is in `W(n)` hence not in `g`. If it's the prefix of a node in `g`
                    // then it must also be the last node of `W(n)`. Either way `W(m.s) = W(m).s`
                    // and we continue the induction with `W(m)`.
                    //
                    // Corollary: If there is an infinite path, then there is an infinite path that
                    // starts with a node of `g`.
                    // Proof: Assume there's an infinite path. By previous lemma we can wlog
                    // assume it contains a node `n` of `g`. By determinism, `W(n)` is infinite
                    // too and concludes the proof.
                    //
                    // Let `n` be a node in `g`. Define `f(n, s)` to be, if it exists, the first
                    // `t` such that `n.t` is in `W(n.s)`.
                    //
                    // Lemma: If `f(n, s)` is defined and `W(n.s)` is infinite, `f(n, s.x) = f(n,
                    // s).x` for any `x`.
                    // Proof: `W(n.s.x)` starts with `W(n.s).x` by the lemma, and the latter is
                    // infinite, so they're equal.
                    //
                    // What I know: every infinite path has at least one `(n, s)` such that `f(n,
                    // s)` is defined. If ever `f(n, s) >= s` then we have an infinite path. Is
                    // that a sufficient condition?
                    //
                    // Conjecture: A path is infinite iff it has a node `n.s` with `f(n, s) >= s`.
                    //
                    // Conjecture: An infinite path eventually repeats modulo suffixes.

                    // Print the graph for debugging.
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
                    eprintln!("dependency graph for {x}:\n{s}");

                    // Algorithm: start with a node of `g`, and take steps in `G` recording which
                    // `g`-edges are used and with what suffix. If this reaches a node without
                    // outgoing edges, all good. Otherwise we will eventually reuse the same
                    // `g`-edge. Compare the suffixes used: if an old suffix is a prefix of (or
                    // equal to) the new suffix, that's an infinite path. Otherwise keep going;
                    // since there are finitely many constructors, this cannot go on infinitely
                    // without hitting our infinite path detection case.
                    // Do this for every node of `g`. Total complexity: N*E² probably.
                    for start in graph.nodes().collect_vec() {
                        let mut current = start;
                        // For each g-edge (identified by its source) we've traversed, record the
                        // last suffix we used.
                        let mut used_edges: HashMap<ConstructorPath, ConstructorPath> =
                            HashMap::new();
                        loop {
                            // Find the unique split of `current` where the prefix is the source
                            // of an edge in `g`. By the property "if a -> b then a.x is not a
                            // source", at most one split matches.
                            let step = current.splits().find_map(|(prefix, suffix)| {
                                graph
                                    .neighbors(prefix)
                                    .next()
                                    .map(|next| (prefix, suffix, next))
                            });
                            let Some((edge_src, suffix, next)) = step else {
                                break; // No outgoing edge in G, all good.
                            };
                            if let Some(&prev_suffix) = used_edges.get(&edge_src) {
                                if suffix.starts_with(prev_suffix) {
                                    // The old suffix is a prefix of the new one — infinite path.
                                    panic!(
                                        "failed to prove progress of {x}: \
                                        recursive uses are not productive.\n\
                                        dependency graph:\n{s}"
                                    );
                                }
                                // Otherwise keep going; finitely many constructors means we'll
                                // eventually hit the detection case or terminate.
                            } else {
                                used_edges.insert(edge_src, suffix);
                            }
                            current = next.concat(suffix);
                        }
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
                    Some(__([MentionPath::identity()])), // it's an identity function
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
            t => panic!("Type expected, got {t}."),
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
                Some(binding) if let Some(val) = binding.value(unfold_nominal).cloned() => {
                    self.whnf_inner(&val, unfold_nominal)
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
            (Pi(x, t1, body1, _), Pi(y, t2, body2, _)) => {
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
