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
            fn map_expr(&mut self, _: SubExprLocation, e: &Expr) -> Expr {
                self.subst(e)
            }

            type SelfWithNewLifetime<'a> = Self;
            fn under_abstraction<T>(
                &mut self,
                span: &Span,
                x: &mut Variable,
                _val: Option<&Expr>,
                _ty: Option<&Expr>,
                f: impl FnOnce(&mut Self) -> T,
            ) -> T {
                let x_fresh = x.refresh();
                self.0.push((*x, Var(x_fresh).into_expr(span)));
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
        paths: Vec<Vec<SubExprLocation>>,
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
    /// Convert a location to a number of `MentionPath`s. There can be several if we encounter a
    /// function application that uses its argument several times.
    fn from_path<'a>(
        path: impl IntoIterator<Item = &'a SubExprLocation> + Clone,
    ) -> Result<Vec<Self>, (ConstructorPath, SubExprLocation)> {
        // Compute all the possible combinations of paths.
        path.into_iter()
            .map(|pe| match pe {
                SubExprLocation::AppArg(Some(mentions)) => {
                    // Each item here is a possible path we can take.
                    mentions.iter().map(|m| Either::Left(*m)).collect_vec()
                }
                // We skip paths bound to a `let` because we'll explore them when we encounter
                // the binding instead.
                SubExprLocation::LetVal => vec![],
                // A type annotation is not subject to projections.
                SubExprLocation::TypeAnnot(..) => vec![],
                pe => vec![Either::Right(pe.clone())],
            })
            .multi_cartesian_product()
            .map(|vv: Vec<Either<MentionPath, SubExprLocation>>| {
                let path: Vec<SubExprLocation> = vv
                    .into_iter()
                    .flat_map(|either| match either {
                        Either::Left(m) => Either::Left(m.to_path()),
                        Either::Right(pe) => Either::Right([pe].into_iter()),
                    })
                    .collect_vec();
                Self::from_single_path(&path)
            })
            .try_collect()
    }
    /// `from_path` but after function application etc have been inlined.
    fn from_single_path<'a>(
        path: impl IntoIterator<Item = &'a SubExprLocation> + Clone,
    ) -> Result<Self, (ConstructorPath, SubExprLocation)> {
        let mut ctor_path = ConstructorPath::Empty;
        let mut dtor_path = vec![];
        for pe in path.into_iter().cloned() {
            match pe {
                SubExprLocation::Construct(ctor) if dtor_path.is_empty() => {
                    ctor_path.push(ctor);
                }
                SubExprLocation::Construct(ctor) if dtor_path.last() == Some(&ctor) => {
                    dtor_path.pop();
                }
                SubExprLocation::Destruct(ctor) => {
                    dtor_path.push(ctor);
                }
                // A `let` body doesn't count wrt constructors
                SubExprLocation::LetBody => {}
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
    fn to_path(self) -> impl Iterator<Item = SubExprLocation> {
        let ctors = self.ctor_path.iter().map(SubExprLocation::Construct);
        let dtors = self.dtor_path.rev_iter().map(SubExprLocation::Destruct);
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

    fn check_progress(&self, span: &Span) {
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
                    span.error(&format!(
                        "failed to prove progress of {var}: \
                        `{}` depends on itself",
                        next.display_on(var)
                    ));
                }

                if let Some(next_trunc) = next.truncate(mu)
                    && current.len() <= next.len()
                {
                    if !increasing_path.insert(next_trunc) {
                        span.error(&format!(
                            "failed to prove progress of {var}: \
                            {} leads to a diverging cycle",
                            current.display_on(var)
                        ));
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

#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum TypeAnnotLocation {
    Let,
    LetRec,
    StructMake,
    /// A type constructed during typechecking.
    TypeOf,
}

/// Describes which sub-expression position we are in within the expression tree.
/// One variant per nested `Expr` location inside an `Expr`.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum SubExprLocation {
    /// We're inside the given destructor.
    Construct(Constructor),
    /// We applied a destructor corresponding to this constructor.
    Destruct(Constructor),
    /// We're checking a type annotation.
    TypeAnnot(TypeAnnotLocation),
    // Let / LetRec
    LetVal,
    LetBody,
    LetRecVal(Variable),
    LetRecBody,
    // Pi / Lambda
    PiType,
    LambdaType,
    // Argument of a function application. If known, stores the shape of the function.
    AppArg(Option<FunctionShape>),
    // Eq / Refl / Transport
    TransportFn,
    // Todo
    TodoArg,
    // Occasionally useful: represents the outermost expression, as opposed to a subexpression.
    Root,
}

#[derive(Debug, Default)]
pub struct EvalContext {
    /// The bindings in scope.
    bindings: Vec<(Variable, Binding)>,
    /// The path through the initial expression to the subexpression we're in the process of
    /// typechecking.
    path: Vec<SubExprLocation>,
    /// For each `let rec val` we're inside of, compute a map of which constructor paths depend on
    /// each other. We use this to compute progress.
    progress_graphs: HashMap<Variable, ProgressGraph>,
    /// Count the number of steps we're doing, and abort (instead of stack overflow) if we went too
    /// far.
    steps: u32,
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
        let value = self.typecheck(&value);
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

    pub fn step(&mut self, action: &str) {
        self.steps += 1;
        if self.steps > 10000 || self.path.len() > 500 {
            panic!("overflow encountered during {action}")
        }
    }

    /// Typecheck a sub-expression, tracking its position in the expression tree.
    /// Returns the expression with type annotation added.
    fn typecheck_inner(&mut self, loc: SubExprLocation, e: &Expr) -> Expr {
        self.path.push(loc);
        if self.path.len() > 500 {
            panic!("overflow encountered while typechecking")
        }
        let e = ensure_sufficient_stack(|| self.typecheck(e));
        self.path.pop();
        e
    }
    /// Typechecks an expression and returns the expression with type annotations added.
    pub fn typecheck(&mut self, e: &Expr) -> Expr {
        self.step("typechecking");
        // Typecheck and annotate all subexpressions. Also keep the binding used, if any.
        let (e, last_binding) = {
            struct TypeChecker<'a> {
                ctx: &'a mut EvalContext,
                // Little bit of a hack to get a hold of the last binding used, which may contain some
                // path info.
                last_binding: Option<Binding>,
            }

            impl<'a> TypeChecker<'a> {
                fn new(ctx: &'a mut EvalContext) -> Self {
                    Self {
                        ctx,
                        last_binding: None,
                    }
                }
                fn with_binding_in_scope<T>(
                    &mut self,
                    var: &mut Variable,
                    f: impl FnOnce(&mut <TypeChecker<'a> as ExprMapper>::SelfWithNewLifetime<'_>) -> T,
                    binding: Binding,
                ) -> T {
                    let (ret, binding) =
                        self.ctx
                            .with_binding_in_scope_keep_binding(*var, binding, |ctx| {
                                f(&mut TypeChecker::new(ctx))
                            });
                    self.last_binding = Some(binding);
                    ret
                }
            }

            impl<'a> ExprMapper for TypeChecker<'a> {
                fn map_expr(&mut self, l: SubExprLocation, e: &Expr) -> Expr {
                    self.ctx.typecheck_inner(l, e)
                }

                type SelfWithNewLifetime<'b> = TypeChecker<'b>;
                fn under_abstraction<T>(
                    &mut self,
                    _span: &Span,
                    var: &mut Variable,
                    val: Option<&Expr>,
                    ty: Option<&Expr>,
                    f: impl for<'b> FnOnce(&mut TypeChecker<'b>) -> T,
                ) -> T {
                    let binding = match val {
                        Some(val) => Binding::with_value(val),
                        None => Binding::abstrakt(ty.unwrap()),
                    };
                    self.with_binding_in_scope(var, f, binding)
                }
                fn under_recursive_abstraction<T>(
                    &mut self,
                    _span: &Span,
                    var: &mut Variable,
                    // The not-yet-mapped value of `var`, if any.
                    val: Option<&Expr>,
                    // The not-yet-mapped type of `var`.
                    ty: &Expr,
                    f: impl for<'b> FnOnce(&mut Self::SelfWithNewLifetime<'b>) -> T,
                ) -> T {
                    // Push `var` with value immediately so it can reduce during its own
                    // typechecking. Marked nominal so whnf doesn't unfold it .
                    let binding = match val {
                        Some(val) => Binding::nominal(val, ty),
                        None => Binding::abstrakt(ty),
                    };
                    self.with_binding_in_scope(var, f, binding)
                }
            }

            let mut type_checker_ctx = TypeChecker::new(self);
            let e = e.without_ty().map(&mut type_checker_ctx);
            (e, type_checker_ctx.last_binding)
        };

        let span = e.span();
        let ty = match e.kind() {
            Var(x) => {
                let binding = self
                    .lookup_binding(*x)
                    .unwrap_or_else(|| e.error(&format!("Failed to find variable `{x}`")))
                    .clone();
                return e.with_ty(binding.ty);
            }
            // `Expr::ty` already returns `Type(k+1)` for the type of this expression.
            Type(_) => return e.clone(),
            Let(_, ty, e1, e2) => {
                if let Some(ty) = ty {
                    ty.ty().unwrap_universe();
                    self.assert_equal(&ty, &e1.ty());
                }
                e2.ty().clone()
            }
            LetRec(_, ty, e1, e2) => {
                ty.ty().unwrap_universe();
                self.assert_equal(&ty, &e1.ty());
                e2.ty().clone()
            }
            Pi(_, t1, t2, _) => {
                let k1 = t1.ty().unwrap_universe();
                let k2 = t2.ty().unwrap_universe();
                Type(k1.max(k2)).into_expr(span)
            }
            Lambda(x, t, body) => {
                t.ty().unwrap_universe();
                let binding = last_binding.unwrap();
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
                Pi(*x, t.clone(), body_ty, mentions).into_expr(span)
            }
            App(f, arg) => {
                let Pi(x, s, t, _) = self.whnf_unfold(&f.ty()).kind().clone() else {
                    f.error("Function expected")
                };
                self.assert_equal(&s, &arg.ty());
                t.subst1(x, &arg)
            }
            StructTy(_, fields) => {
                let k = fields
                    .iter()
                    .map(|(_, t)| t.ty().unwrap_universe())
                    .max()
                    .unwrap_or(0);
                Type(k).into_expr(span)
            }
            Struct(ty_ann, fields) => {
                let field_tys = fields.iter().map(|(&n, e)| (n, e.ty().clone())).collect();
                let actual = StructTy(Variable::user("self"), Arc::new(field_tys)).into_expr(span);
                if let Some(ty_ann) = ty_ann {
                    ty_ann.ty().unwrap_universe();
                    {
                        let StructTy(self_var, field_tys) =
                            self.whnf_unfold(&ty_ann).kind().clone()
                        else {
                            ty_ann.error("Struct type expected for `make`")
                        };
                        let expected = StructTy(self_var.refresh(), field_tys).into_expr(span);
                        let expected = expected.subst1(self_var, &e);
                        self.assert_equal(&expected, &actual);
                    }
                    ty_ann.clone()
                } else {
                    actual
                }
            }
            Field(e, name) => {
                let te = self.whnf_unfold(&e.ty());
                let StructTy(self_var, fields) = te.kind().clone() else {
                    e.error(&format!(
                        "Struct type expected for field access, got `{te}`"
                    ))
                };
                let field_ty = fields
                    .get(name)
                    .unwrap_or_else(|| e.error(&format!("Field `{name}` not found")))
                    .clone();
                field_ty.subst1(self_var, &e)
            }
            Eq(a, b) => {
                self.assert_equal(&a.ty(), &b.ty());
                let a_ty = self.typecheck_inner(
                    SubExprLocation::TypeAnnot(TypeAnnotLocation::TypeOf),
                    &a.ty(),
                );
                let k = a_ty.ty().unwrap_universe();
                Type(k).into_expr(span)
            }
            Refl(a) => Eq(a.clone(), a.clone()).into_expr(span),
            Transport(eq, f) => {
                let Eq(a, b) = self.whnf_unfold(&eq.ty()).kind().clone() else {
                    eq.error("Equality type expected for transport")
                };
                let Pi(..) = self.whnf_unfold(&f.ty()).kind() else {
                    f.error("Function expected for transport's second argument")
                };
                Pi(
                    Variable::anon(),
                    App(f.clone(), a).into_expr(span),
                    App(f.clone(), b).into_expr(span),
                    None,
                )
                .into_expr(span)
            }
            Todo(t) => t.clone(),
        };

        // Recursively check the type is well-formed.
        let ty = self.typecheck_inner(SubExprLocation::TypeAnnot(TypeAnnotLocation::TypeOf), &ty);
        let ty = self.whnf(&ty);
        let e = e.with_ty(ty);

        // Progress-check starting from the top-level expression.
        if self.path.is_empty() {
            self.progress_check(&e);
        }

        e
    }

    fn progress_check_inner(&mut self, loc: SubExprLocation, e: &Expr) {
        self.path.push(loc);
        ensure_sufficient_stack(|| self.progress_check(e));
        self.path.pop();
    }
    pub fn progress_check(&mut self, e: &Expr) {
        self.step("progress checking");
        match e.kind() {
            Var(x) => {
                let binding = self
                    .lookup_binding(*x)
                    .unwrap_or_else(|| e.error(&format!("Failed to find variable `{x}`")))
                    .clone();
                match binding.kind {
                    BindingKind::Normal(v) => {
                        if self
                            .path
                            .iter()
                            .any(|e| matches!(e, SubExprLocation::LetRecVal(..)))
                        {
                            // A let-binding may contain recursive mentions of a recursive
                            // variable, so we re-progress-check it here.
                            self.progress_check(&v);
                        }
                    }
                    BindingKind::Nominal(..) => {
                        if let Some(graph) = self.progress_graphs.get_mut(x)
                            && let mut subpath = self.path.iter()
                            && subpath
                                .by_ref()
                                .find(|e| matches!(e, SubExprLocation::LetRecVal(v) if v == x))
                                .is_some()
                        {
                            // We're inside a `let rec val` definition, and we found a recursive reference
                            // to `val`.
                            match MentionPath::from_path(subpath.clone()) {
                                Ok(mention_paths) => {
                                    // We can handle all the paths from the start of the `let rec` to here;
                                    // add them to the graph.
                                    for mention_path in mention_paths {
                                        graph.insert(mention_path);
                                    }
                                }
                                Err((ctor_path, pe)) => {
                                    // Some paths are of a shape we can't handle; error.
                                    let location = match pe {
                                        SubExprLocation::AppArg(None) => {
                                            format!("an unknown function application")
                                        }
                                        _ => format!("a {pe:?}"),
                                    };
                                    e.error(&format!(
                                        "failed to prove progress of {x}: \
                                        recursive mention found under {location}\n  \
                                        location: {}",
                                        ctor_path.display_on(*x),
                                    ));
                                }
                            }
                        }
                    }
                    _ => (),
                }
                return;
            }
            // Avoid checking an infinite stack of types.
            Type(_) => return,
            _ => {}
        }

        struct ProgressChecker<'a> {
            ctx: &'a mut EvalContext,
        }

        impl<'a> ProgressChecker<'a> {
            fn new(ctx: &'a mut EvalContext) -> Self {
                Self { ctx }
            }
            fn with_binding_in_scope<T>(
                &mut self,
                var: &mut Variable,
                f: impl FnOnce(&mut <ProgressChecker<'a> as ExprMapper>::SelfWithNewLifetime<'_>) -> T,
                binding: Binding,
            ) -> T {
                self.ctx
                    .with_binding_in_scope(*var, binding, |ctx| f(&mut ProgressChecker::new(ctx)))
            }
        }

        impl<'a> ExprMapper for ProgressChecker<'a> {
            fn map_expr(&mut self, l: SubExprLocation, e: &Expr) -> Expr {
                if let SubExprLocation::LetRecVal(var) = l {
                    self.ctx
                        .progress_graphs
                        .insert(var, ProgressGraph::new(var));
                    self.ctx.progress_check_inner(l, e);

                    let graph = self.ctx.progress_graphs.remove(&var).unwrap();
                    eprintln!("dependency graph for {var}:\n{graph}");
                    graph.check_progress(e.span());
                } else {
                    self.ctx.progress_check_inner(l, e)
                }
                e.clone()
            }

            type SelfWithNewLifetime<'b> = ProgressChecker<'b>;
            fn under_abstraction<T>(
                &mut self,
                _span: &Span,
                var: &mut Variable,
                val: Option<&Expr>,
                ty: Option<&Expr>,
                f: impl for<'b> FnOnce(&mut ProgressChecker<'b>) -> T,
            ) -> T {
                let binding = match val {
                    Some(val) => Binding::with_value(val),
                    None => Binding::abstrakt(ty.unwrap()),
                };
                self.with_binding_in_scope(var, f, binding)
            }
            fn under_recursive_abstraction<T>(
                &mut self,
                _span: &Span,
                var: &mut Variable,
                // The not-yet-mapped value of `var`, if any.
                val: Option<&Expr>,
                // The not-yet-mapped type of `var`.
                ty: &Expr,
                f: impl for<'b> FnOnce(&mut Self::SelfWithNewLifetime<'b>) -> T,
            ) -> T {
                let binding = match val {
                    Some(val) => Binding::nominal(val, ty),
                    None => Binding::abstrakt(ty),
                };
                self.with_binding_in_scope(var, f, binding)
            }
        }

        // Recursively progress-check by lightly abusing the `map` function.
        e.map(&mut ProgressChecker::new(self));
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
        self.step("normalization");
        let span = e.span();
        match e.kind() {
            Var(x) => match self.lookup_binding(*x) {
                Some(binding) if let Some(val) = binding.value(unfold_nominal).cloned() => {
                    self.whnf_inner(&val, unfold_nominal)
                }
                _ => Var(*x).into_expr(span),
            },
            App(e1, e2) => match self.whnf_inner(e1, unfold_nominal).kind() {
                Lambda(x, _, body) => {
                    let body = body.clone();
                    self.whnf_inner(&body.subst1(*x, e2), unfold_nominal)
                }
                _ => App(self.whnf_inner(e1, unfold_nominal), e2.clone()).into_expr(span),
            },
            Field(e, name) => match self.whnf_inner(e, true).kind() {
                Struct(_, fields) => {
                    let val = fields
                        .get(name)
                        .unwrap_or_else(|| e.error(&format!("Field `{name}` not found")))
                        .clone();
                    self.whnf_inner(&val, unfold_nominal)
                }
                _ => Field(self.whnf_inner(e, true), *name).into_expr(span),
            },
            Let(x, _, e1, e2) => self.whnf_inner(&e2.subst1(*x, e1), unfold_nominal),
            LetRec(x, ty, e1, e2) => {
                let fixpoint =
                    LetRec(*x, ty.clone(), e1.clone(), Var(*x).into_expr(span)).into_expr(span);
                let e1_unrolled = e1.subst1(*x, &fixpoint);
                self.whnf_inner(&e2.subst1(*x, &e1_unrolled), unfold_nominal)
            }
            Transport(eq, f) => {
                match self.whnf_inner(eq, unfold_nominal).kind() {
                    // transport (refl x) f : fn(f x) -> f x  reduces to identity
                    Refl(x) => {
                        let x = x.clone();
                        let y = Variable::anon().refresh();
                        Lambda(y, App(f.clone(), x).into_expr(span), Var(y).into_expr(span))
                            .into_expr(span)
                    }
                    _ => Transport(self.whnf_inner(eq, unfold_nominal), f.clone()).into_expr(span),
                }
            }
            Todo(t) => e.error(&format!("tried to normalize `todo {t}`")),
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
            fn map_expr(&mut self, _: SubExprLocation, e: &Expr) -> Expr {
                self.0.whnf(e).map(self)
            }

            type SelfWithNewLifetime<'b> = Normalizer<'b>;
            fn under_abstraction<T>(
                &mut self,
                _span: &Span,
                var: &mut Variable,
                _val: Option<&Expr>,
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

        Normalizer(self).map_expr(SubExprLocation::Root, e)
    }

    pub fn assert_equal(&mut self, e1: &Expr, e2: &Expr) {
        if !self.equal(e1, e2) {
            e1.span().or(e2.span()).error(&format!(
                "assertion `left == right` failed\n  left: {e1}\n  right: {e2}"
            ));
        }
    }
    pub fn equal(&mut self, e1: &Expr, e2: &Expr) -> bool {
        self.step("equality checking");
        let e1 = self.whnf(e1);
        let e2 = self.whnf(e2);
        let span = e1.span();
        // Recurse into sub-expressions, applying whnf at each level.
        match (e1.kind(), e2.kind()) {
            (Var(x1), Var(x2)) => x1 == x2,
            (Type(k1), Type(k2)) => k1 == k2,
            (Lambda(x, t1, body1), Lambda(y, t2, body2)) => {
                // A little bit of alpha-equivalence.
                let z = x.refresh();
                let zv: Expr = Var(z).into_expr(span);
                self.equal(t1, t2) && self.equal(&body1.subst1(*x, &zv), &body2.subst1(*y, &zv))
            }
            (Pi(x, t1, body1, _), Pi(y, t2, body2, _)) => {
                let z = x.refresh();
                let zv: Expr = Var(z).into_expr(span);
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
                let zv: Expr = Var(z).into_expr(span);
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

/// Grows the stack on demand to prevent stack overflow. Call this in strategic locations to "break
/// up" recursive calls.
#[inline]
fn ensure_sufficient_stack<R>(f: impl FnOnce() -> R) -> R {
    // This is the amount of bytes that need to be left on the stack before increasing the size. It
    // must be at least as large as the stack required by any code that does not call
    // `ensure_sufficient_stack`.
    const RED_ZONE: usize = 100 * 1024; // 100k

    // Only the first stack that is pushed, grows exponentially (2^n * STACK_PER_RECURSION) from then
    // on. Values taken from rustc.
    const STACK_PER_RECURSION: usize = 1024 * 1024; // 1MB

    stacker::maybe_grow(RED_ZONE, STACK_PER_RECURSION, f)
}
