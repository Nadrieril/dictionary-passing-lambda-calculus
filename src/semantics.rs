use std::{
    collections::{HashMap, HashSet, VecDeque},
    convert::Infallible,
    fmt::{Debug, Display},
    sync::Arc,
};

use enum_as_inner::EnumAsInner;
use fallible_iterator::{FallibleIterator, IteratorExt};
use internment::Intern;
use itertools::{Either, Itertools};
use ustr::Ustr;

use crate::*;
use ExprKind::*;

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
                match e.kind() {
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
                self.0.push((*x, Var(x_fresh).into_expr()));
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
    pub fn with_value(value: &Expr) -> Self {
        Self {
            kind: BindingKind::Normal(value.clone()),
            ty: value.ty().clone(),
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
    // The `usize` is the length of this path.
    Cons(Intern<(ConstructorPath, Constructor, usize)>),
}

impl ConstructorPath {
    fn new(ctors: impl IntoIterator<Item = Constructor>) -> Self {
        ctors.into_iter().fold(Self::Empty, |acc, c| acc.cons(c))
    }
    fn cons(self, c: Constructor) -> Self {
        Self::Cons(Intern::new((self, c, self.len() + 1)))
    }
    fn push(&mut self, c: Constructor) {
        *self = self.cons(c)
    }

    fn concat(self, other: Self) -> Self {
        other.iter().fold(self, |acc, c| acc.cons(c))
    }

    fn len(self) -> usize {
        match self {
            ConstructorPath::Empty => 0,
            ConstructorPath::Cons(intern) => intern.2,
        }
    }
    /// Return the prefix of size `n` of `self`, or `None` if `self` is too small.
    fn truncate(self, n: usize) -> Option<Self> {
        if self.len() >= n {
            Some(if self.len() > n {
                self.iter_prefixes()
                    .map(|(p, _)| p)
                    .find(|p| p.len() == n)
                    .unwrap()
            } else {
                self
            })
        } else {
            None
        }
    }

    fn iter(self) -> impl Iterator<Item = Constructor> {
        self.iter_prefixes().map(|(_, c)| c)
    }
    fn iter_prefixes(self) -> impl Iterator<Item = (Self, Constructor)> {
        let mut elems = VecDeque::new();
        let mut cur = self;
        while let Self::Cons(intern) = cur {
            let (prefix, ctor, _) = *intern;
            elems.push_front((prefix, ctor));
            cur = prefix;
        }
        elems.into_iter()
    }
    fn rev_iter(self) -> impl Iterator<Item = Constructor> {
        let mut cur = self;
        std::iter::from_fn(move || {
            let (prefix, ctor, _) = **cur.as_cons()?;
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
        while let Self::Cons(intern) = cur {
            let (prefix, ctor, _) = *intern;
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
pub type FunctionShape = Arc<[MentionPath]>;

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

/// Records the dependency map of constructor paths of a given coinductive value.
/// A `x -> y` path in the graph means that we know the value of `val.x` to be `val.y`. At the
/// end, the lhs of edges will be all the subplaces of `val` that recursively depend on `val`.
#[derive(Debug)]
struct ProgressGraph {
    variable: Variable,
    nodes: HashSet<ConstructorPath>,
    next: HashMap<ConstructorPath, ConstructorPath>,
}

impl ProgressGraph {
    fn new(variable: Variable) -> Self {
        Self {
            variable,
            nodes: Default::default(),
            next: Default::default(),
        }
    }

    fn insert(&mut self, mention: MentionPath) {
        self.nodes.insert(mention.ctor_path);
        self.nodes.insert(mention.dtor_path);
        self.next.insert(mention.ctor_path, mention.dtor_path);
    }

    fn check_progress(&self) {
        // Progress means that all the subplaces (i.e. repeated destructor applications) of our
        // coinductive value can be reduced to whnf. In the graph we computed which subplaces
        // depend on which other ones.
        //
        // Call `g` our graph. Its nodes are constructor paths (that's not just field accesses, see
        // `ConstructorPath`), and there's an edge `n -> m` if we could determine that `val.n`
        // evaluates to `val.m` in finite steps.
        //
        // Build an infinite graph `G` as follows: for every `n` in `g` and suffix `s`, `n.s` is a
        // node in `G`; `G` has an edge `n -> m` whenever `n = n'.s`, `m = m'.s`, and `n' -> m'` in
        // `g`.
        //
        // The core property of our graph is that all the self-references of `val` on itself are of
        // the form `val.path1 = val.path2`, where `path1 -> path2` is an edge in `G`.
        //
        // `g` has one more important property: if a -> b in `g` then a.x is not the source of
        // another edge for any `x` even empty (iow, sources form an anti-chain under prefix
        // ordering). This is equivalent to the statement that walking through `G` is
        // deterministic, and that evaluation is deterministic.
        //
        // Lemma: If `n -> m` in `G`, then `val.n` evaluates to `val.m` in a finite number of
        // steps.
        // Proof: By construction, let `n = n'.s`, `m = m'.s` such that `n' -> m'` is an edge in
        // `g`. From how we built `g`, evaluating `val.n'` gives `val.m'` in finite steps; adding
        // extra projections on top doesn't change anything since we evaluate the subexpressions
        // first.
        //
        // Claim: the expression is productive iff `G` has no infinite paths.
        //
        // Proof: The only recursion in our language is this coinduction (well, except dependent
        // records, gotta fix that), and every binding in scope has been checked to be productive.
        // Hence if the current expression does not involve `val`, it reduces to whnf. So wlog
        // assume the current expression is of the form `val.path` (`path` isn't just field
        // accesses, see `ConstructorPath`). Evaluating `val.path` involves evaluating all the
        // `val.subpath` prefixes to whnf, then evaluating the final projection. Wlog assume that
        // the prefixes reduced to whnf. Consider the expression we're left with. If it contains no
        // mention of `val`, per previous argument it evaluates; hence wlog it mentions `val`. Per
        // the property of our graph, `G` has an edge `path -> next`, and per the lemma evaluating
        // `val.path` gives `val.next`, which must then be tried for whnf again. In summary, we
        // have: if `path` is in the `G`, evaluating `val.path` takes an edge in that graph. If
        // there is no edge, then we can reach whnf. So if `path` doesn't lead to an infinite path,
        // `val.path` has a whnf.
        //
        // We'll use the results from "Object-Oriented Data as Prefix Rewriting Systems"
        // (http://old.math.nsc.ru/LBRT/g2/files/OOD_as_PRS.pdf) .
        //
        // The walk in `G` is a deterministic longest-prefix rewriting system: each g-edge `src ->
        // tgt` is a rewrite rule that replaces prefix `src` with `tgt`, carrying the suffix
        // unchanged. By the anti-chain property longest-prefix = unique-prefix matching. Hence we
        // can use the results from the paper.
        //
        // Lemma: `W(n.s)` starts with `W(n).s`.
        // Proof: All edges taken in `W(n).s` are valid for `W(n.s)` by construction of `G`. We
        // conclude by determinism.
        //
        // Corollary: If there is an infinite path, then there is one starting from a node of `g`.
        // Proof sketch: Any walk can be decomposed as `W(m).s` where `W(m)` contains a g-node. An
        // infinite walk implies `W(m)` is infinite (or extends to one).
        // See Gutman, "OOD as PRS", Theorem 7.
        //
        // Theorem (Gutman, Theorem 22): Let `μ = max |src|` over all g-edges. A word
        // `X` is infinitely rewritable iff one of:
        // (a) Pure cycle: `X(n) = X(n+r)` for some `n ≥ 0`, `r > 0`.
        // (b) Growing cycle: there exist `n ≥ 0`, `r > 0` such that
        //     `μ ≤ |X(n)| ≤ ... ≤ |X(n+r)|`, and
        //     `X(n)↾μ = X(n+r)↾μ` (the μ-length prefix repeats).
        //     In this case `X(n+kr) = Y.R^k.S` for fixed `Y`, `R`, `S`.
        //
        // By the corollary and Theorem 7 of Gutman, it suffices to check only the paths starting
        // from nodes in `g`.
        //
        // Algorithm (Gutman, Algorithm 24): Compute the rewriting sequence from each g-node. At
        // each step, check for conditions (a) and (b). Guaranteed to terminate: pure cycles are
        // detected within C^μ short-word states; growing cycles are detected when the μ-prefix
        // repeats with non-decreasing lengths.
        let var = self.variable;
        // μ = max length of any g-source.
        let mu = self.next.keys().map(|n| n.len()).max().unwrap_or(0);

        for &start in &self.nodes {
            // The nodes we've seen.
            let mut seen: HashSet<ConstructorPath> = [start].into();
            // For the last section of the path that is increasing in length and longer
            // than μ, keep the truncated-to-length-μ version of each node.
            let mut increasing_path: HashSet<ConstructorPath> =
                start.truncate(mu).into_iter().collect();
            let mut current = start;
            loop {
                // One rewriting step: find the unique source that's a prefix of
                // `current` and replace it with the target.
                let step = current.splits().find_map(|(prefix, suffix)| {
                    self.next.get(&prefix).map(|next| next.concat(suffix))
                });
                let Some(next) = step else {
                    break; // Not rewritable, walk terminates.
                };

                if !seen.insert(next) {
                    panic!(
                        "failed to prove progress of {var}: \
                        `{}` depends on itself",
                        next.display_on(var)
                    );
                }

                if let Some(next_trunc) = next.truncate(mu)
                    && current.len() <= next.len()
                {
                    if !increasing_path.insert(next_trunc) {
                        panic!(
                            "failed to prove progress of {var}: \
                            {} leads to a diverging cycle",
                            current.display_on(var)
                        );
                    }
                } else {
                    increasing_path.clear();
                }
                current = next;
            }
        }
    }
}

impl Display for ProgressGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for node in self.nodes.iter().sorted() {
            for neighbor in self.next.get(node).iter().sorted() {
                writeln!(
                    f,
                    "- {} <- {}",
                    node.display_on(self.variable),
                    neighbor.display_on(self.variable)
                )?;
            }
        }
        Ok(())
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
    /// each other. We use this to compute progress.
    progress_graphs: HashMap<Variable, ProgressGraph>,
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
        let value = self.typecheck_inner(PathElem::LetVal, &value);
        self.push_binding(x, Binding::with_value(&value));
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
    /// Returns the expression with type annotation added.
    fn typecheck_inner(&mut self, loc: PathElem, e: &Expr) -> Expr {
        self.path.push(loc);
        let e = self.typecheck(e);
        self.path.pop();
        e
    }
    /// Typechecks an expression and returns the expression with type annotations added.
    pub fn typecheck(&mut self, e: &Expr) -> Expr {
        let (kind, ty): (ExprKind, Expr) = match e.kind() {
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
                            let _ = self.typecheck(&v);
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
                                    let graph = self.progress_graphs.get_mut(x).unwrap();
                                    for mention_path in mention_paths {
                                        graph.insert(mention_path);
                                    }
                                }
                                Err((ctor_path, pe)) => {
                                    // Some paths are of a shape we can't handle; error.
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
                return Var(*x).with_ty(binding_ty);
            }
            Type(k) => {
                return Type(*k).with_ty(Type(k + 1).into_expr());
            }
            Pi(x, t1, t2, mentions) => {
                let (t1, k1) = self.typecheck_universe(PathElem::PiType, t1);
                let (t2, k2) = self.with_binding_in_scope(*x, Binding::abstrakt(&t1), |ctx| {
                    ctx.typecheck_universe(PathElem::Construct(Constructor::Pi), t2)
                });
                (
                    Pi(*x, t1, t2, mentions.clone()),
                    Type(k1.max(k2)).into_expr(),
                )
            }
            Lambda(x, t, body) => {
                let (t, _) = self.typecheck_universe(PathElem::LambdaType, t);
                let (body, binding) =
                    self.with_binding_in_scope_keep_binding(*x, Binding::abstrakt(&t), |ctx| {
                        ctx.typecheck_inner(PathElem::Construct(Constructor::Lambda), body)
                    });
                let mentions = {
                    let BindingKind::Abstract { paths } = binding.kind else {
                        unreachable!()
                    };
                    let cur_path_len = self.path.len() + 1;
                    // Each path is one location where the input variable is mentioned in the body.
                    // Each such location may give rise to several `MentionPath`s because of other
                    // function calls. We flatten everything here. If any of the locations could
                    // not be transformed to a `MentionPath`, we get `None` to ensure that the set
                    // of paths is always exhaustive.
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
                let body_ty = body.ty().clone();
                (
                    Lambda(*x, t.clone(), body),
                    Pi(*x, t, body_ty, mentions).into_expr(),
                )
            }
            App(f, arg) => {
                let f = self.typecheck_inner(PathElem::Destruct(Constructor::Lambda), f);
                let Pi(x, s, t, mentions) = self.whnf_unfold(f.ty()).kind().clone() else {
                    panic!("Function expected.")
                };
                let arg = self.typecheck_inner(PathElem::AppArg(mentions), arg);
                self.assert_equal(&s, arg.ty());
                let app_ty = t.subst1(x, &arg);
                (App(f, arg), app_ty)
            }
            StructTy(x, fields) => {
                let (fields, k) = self.with_binding_in_scope(*x, Binding::abstrakt(e), |ctx| {
                    let mut max_k = 0usize;
                    let fields: indexmap::IndexMap<Ustr, Expr> = fields
                        .iter()
                        .map(|(&f, t)| {
                            let loc = PathElem::Construct(Constructor::StructTyField(f));
                            let (t, k) = ctx.typecheck_universe(loc, t);
                            max_k = max_k.max(k);
                            (f, t)
                        })
                        .collect();
                    (Arc::new(fields), max_k)
                });
                (StructTy(*x, fields), Type(k).into_expr())
            }
            Struct(ty_ann, fields) => {
                let (field_tys, fields) = fields
                    .iter()
                    .map(|(&n, e)| {
                        let loc = PathElem::Construct(Constructor::StructField(n));
                        let e = self.typecheck_inner(loc, e);
                        ((n, e.ty().clone()), (n, e))
                    })
                    .collect();
                let actual = StructTy(Variable::user("self"), Arc::new(field_tys)).into_expr();
                let (ty_ann, ty) = if let Some(ty_ann) = ty_ann {
                    let (ty_ann, _) = self.typecheck_universe(PathElem::StructAnnot, ty_ann);
                    {
                        let StructTy(self_var, field_tys) =
                            self.whnf_unfold(&ty_ann).kind().clone()
                        else {
                            panic!("Struct type expected for `make`")
                        };
                        let expected = StructTy(self_var.refresh(), field_tys).into_expr();
                        let expected = expected.subst1(self_var, e);
                        self.assert_equal(&expected, &actual);
                    }
                    (Some(ty_ann.clone()), ty_ann)
                } else {
                    (None, actual)
                };
                (Struct(ty_ann, Arc::new(fields)), ty)
            }
            Let(x, ty_ann, e1, e2) => {
                let e1 = self.typecheck_inner(PathElem::LetVal, e1);
                let ty_ann = if let Some(ty) = ty_ann {
                    let (ty, _) = self.typecheck_universe(PathElem::LetTy, ty);
                    self.assert_equal(&ty, e1.ty());
                    Some(ty)
                } else {
                    None
                };
                let e2 = self.with_binding_in_scope(*x, Binding::with_value(&e1), |ctx| {
                    // No `PathElem` here: a `let` body doesn't count wrt constructors.
                    ctx.typecheck(e2)
                });
                let e2_ty = e2.ty().clone();
                return Let(*x, ty_ann, e1, e2).with_ty(e2_ty);
            }
            LetRec(var, ty, e1, e2) => {
                let (ty, _) = self.typecheck_universe(PathElem::LetRecTy, ty);
                // Push `var` with value immediately so it can reduce during its own typechecking
                // (needed for self-referential types like `Trait` whose fields reference `Trait`
                // applied to args). Marked nominal so whnf doesn't unfold it.
                let binding = Binding::nominal(e1, &ty);
                let (e1, e2) = self.with_binding_in_scope(*var, binding, |ctx| {
                    ctx.progress_graphs.insert(*var, ProgressGraph::new(*var));
                    let e1 = ctx.typecheck_inner(PathElem::LetRecVal(*var), e1);
                    ctx.assert_equal(&ty, e1.ty());

                    let graph = ctx.progress_graphs.remove(var).unwrap();
                    eprintln!("dependency graph for {var}:\n{graph}");
                    graph.check_progress();

                    let e2 = ctx.typecheck_inner(PathElem::LetRecBody, e2);
                    (e1, e2)
                });
                let e2_ty = e2.ty().clone();
                return LetRec(*var, ty, e1, e2).with_ty(e2_ty);
            }
            Field(e, name) => {
                let loc = PathElem::Destruct(Constructor::StructField(*name));
                let e = self.typecheck_inner(loc, e);
                let te = self.whnf_unfold(e.ty());
                let StructTy(self_var, fields) = te.kind().clone() else {
                    panic!("Struct type expected for field access, got `{te}`")
                };
                let field_ty = fields
                    .get(name)
                    .unwrap_or_else(|| panic!("Field {name} not found"))
                    .clone();
                let field_ty = field_ty.subst1(self_var, &e);
                (Field(e, *name), field_ty)
            }
            Eq(a, b) => {
                let a = self.typecheck_inner(PathElem::Construct(Constructor::EqLeft), a);
                let b = self.typecheck_inner(PathElem::Construct(Constructor::EqRight), b);
                self.assert_equal(a.ty(), b.ty());
                let k = self.infer_universe(PathElem::Destruct(Constructor::TypeOf), a.ty());
                (Eq(a, b), Type(k).into_expr())
            }
            Refl(a) => {
                let a = self.typecheck_inner(PathElem::Construct(Constructor::Refl), a);
                (Refl(a.clone()), Eq(a.clone(), a).into_expr())
            }
            Transport(eq, f) => {
                let eq = self.typecheck_inner(PathElem::Destruct(Constructor::Refl), eq);
                let Eq(a, b) = self.whnf_unfold(eq.ty()).kind().clone() else {
                    panic!("Equality type expected for transport")
                };
                let f = self.typecheck_inner(PathElem::TransportFn, f);
                let Pi(..) = self.whnf_unfold(f.ty()).kind() else {
                    panic!("Function expected for transport's second argument")
                };
                let transport_ty = Pi(
                    Variable::anon(),
                    App(f.clone(), a).into_expr(),
                    App(f.clone(), b).into_expr(),
                    Some(Arc::new([MentionPath::identity()])), // it's an identity function
                )
                .into_expr();
                (Transport(eq, f), transport_ty)
            }
            Todo(t) => {
                let t = self.typecheck_inner(PathElem::TodoArg, t);
                return Todo(t.clone()).with_ty(t);
            }
        };
        // Recursively check the type is well-formed.
        let _ = self.typecheck_inner(PathElem::Destruct(Constructor::TypeOf), &ty);
        let ty = self.whnf(&ty);
        kind.with_ty(ty)
    }
    /// Like `typecheck_inner` but also checks the result type is a universe and returns its level.
    fn typecheck_universe(&mut self, loc: PathElem, t: &Expr) -> (Expr, usize) {
        let t = self.typecheck_inner(loc, t);
        let k = match t.ty().kind() {
            Type(k) => *k,
            _ => panic!("Type expected, got {}.", t.ty()),
        };
        (t, k)
    }
    fn infer_universe(&mut self, loc: PathElem, t: &Expr) -> usize {
        self.typecheck_universe(loc, t).1
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
        match e.kind() {
            Var(x) => match self.lookup_binding(*x) {
                Some(binding) if let Some(val) = binding.value(unfold_nominal).cloned() => {
                    self.whnf_inner(&val, unfold_nominal)
                }
                _ => Var(*x).into_expr(),
            },
            App(e1, e2) => match self.whnf_inner(e1, unfold_nominal).kind() {
                Lambda(x, _, body) => {
                    let body = body.clone();
                    self.whnf_inner(&body.subst1(*x, e2), unfold_nominal)
                }
                _ => App(self.whnf_inner(e1, unfold_nominal), e2.clone()).into_expr(),
            },
            Field(e, name) => match self.whnf_inner(e, true).kind() {
                Struct(_, fields) => {
                    let val = fields
                        .get(name)
                        .unwrap_or_else(|| panic!("Field {name} not found"))
                        .clone();
                    self.whnf_inner(&val, unfold_nominal)
                }
                _ => Field(self.whnf_inner(e, true), *name).into_expr(),
            },
            Let(x, _, e1, e2) => self.whnf_inner(&e2.subst1(*x, e1), unfold_nominal),
            LetRec(x, ty, e1, e2) => {
                let fixpoint = LetRec(*x, ty.clone(), e1.clone(), Var(*x).into_expr()).into_expr();
                let e1_unrolled = e1.subst1(*x, &fixpoint);
                self.whnf_inner(&e2.subst1(*x, &e1_unrolled), unfold_nominal)
            }
            Transport(eq, f) => {
                match self.whnf_inner(eq, unfold_nominal).kind() {
                    // transport (refl x) f : fn(f x) -> f x  reduces to identity
                    Refl(x) => {
                        let x = x.clone();
                        let y = Variable::anon().refresh();
                        Lambda(y, App(f.clone(), x).into_expr(), Var(y).into_expr()).into_expr()
                    }
                    _ => Transport(self.whnf_inner(eq, unfold_nominal), f.clone()).into_expr(),
                }
            }
            Todo(t) => panic!("tried to normalize `todo {t}`"),
            _ => e.clone(),
        }
    }

    /// Typecheck then fully normalize the value.
    pub fn normalize(&mut self, e: &Expr) -> Expr {
        let e = self.typecheck(e);
        self.normalize_no_typeck(&e)
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
        match (e1.kind(), e2.kind()) {
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            (Lambda(x, t1, body1), Lambda(y, t2, body2)) => {
                // A little bit of alpha-equivalence.
                let z = x.refresh();
                let zv: Expr = Var(z).into_expr();
                self.equal(t1, t2) && self.equal(&body1.subst1(*x, &zv), &body2.subst1(*y, &zv))
            }
            (Pi(x, t1, body1, _), Pi(y, t2, body2, _)) => {
                let z = x.refresh();
                let zv: Expr = Var(z).into_expr();
                self.equal(t1, t2) && self.equal(&body1.subst1(*x, &zv), &body2.subst1(*y, &zv))
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
                let zv: Expr = Var(z).into_expr();
                f1.iter().all(|(n, e)| {
                    f2.get(n)
                        .is_some_and(|e2| self.equal(&e.subst1(*x1, &zv), &e2.subst1(*x2, &zv)))
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
