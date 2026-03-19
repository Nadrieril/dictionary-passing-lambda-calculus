use dictionary_passing_lambda_calculus::*;

use Expr::*;

fn p(s: &str) -> Expr {
    parse(s).unwrap()
}

#[test]
fn test_application() {
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));

    let sty = p("fn(_: fn(_: N) -> N) -> fn(_: N) -> N");
    assert_eq!(ctx.infer_type(sty).to_string(), "Type(0)");
}

#[test]
fn test_structs() {
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    ctx.assert_equal(
        p("ap (fn(N) -> N) (fn(N) -> N) (ap N N)"),
        p(r"\(x1: fn(N) -> N) -> \(x2: N) -> x1 x2"),
    );
}

#[test]
fn test_equality_capture() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("x", Type(0));

    let id_ty = p("fn(x: Type(0)) -> x");
    let const_ty = p("fn(y: Type(0)) -> x");
    assert!(!ctx.equal(id_ty, const_ty));
}

#[test]
fn test_rec() {
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.normalize(p("todo N"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_rec_self_mismatch() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.add_uninterpreted("m", p("M"));
    ctx.add_val("T", p("{ a: Type(0), b: Type(0), eq: self.a == self.b }"));
    ctx.infer_type(p("make (T) { a = N, b = M, eq = refl N }"));
}

#[test]
fn test_traits() {
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(p("z z"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_arg_type_mismatch() {
    let mut ctx = EvalContext::default();
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
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    // z is a value, not a type — can't use as binder type
    ctx.infer_type(p(r"\(x: z) -> x"));
}

#[test]
#[should_panic(expected = "Struct type expected")]
fn test_reject_field_on_non_struct() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(p("z.a"));
}

#[test]
#[should_panic(expected = "Field b not found")]
fn test_reject_missing_field() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(p("{ a = z }.b"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_eq_different_types() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    // z : N and N : Type(0) — different types
    ctx.infer_type(p("z == N"));
}

#[test]
#[should_panic(expected = "Equality type expected")]
fn test_reject_transport_non_eq() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.add_uninterpreted("f", p("fn(_: N) -> N"));
    ctx.infer_type(p("transport z f"));
}

#[test]
#[should_panic(expected = "Function expected for transport")]
fn test_reject_transport_non_function() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("x", p("N"));
    ctx.add_uninterpreted("eq", p("x == x"));
    // second arg must be a function
    ctx.infer_type(p("transport eq x"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_transport_domain_mismatch() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_uninterpreted("x", p("N"));
    ctx.add_uninterpreted("eq", p("x == x"));
    ctx.add_uninterpreted("f", p("fn(_: M) -> M"));
    // eq proves x == x where x: N, but f expects M
    ctx.infer_type(p("transport eq f"));
}
