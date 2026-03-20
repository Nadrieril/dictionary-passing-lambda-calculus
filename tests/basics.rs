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
    ctx.add_uninterpreted("s", p("N -> N"));
    ctx.add_val("three", p(r"|f: N -> N, x: N| f(f(f(x)))"));

    let expr = p("three(three(s), z)");
    let ty = ctx.infer_type(&expr);
    assert_eq!(ty.to_string(), "N");
    let normalized = ctx.normalize(&expr);
    assert_eq!(
        normalized.to_string(),
        "s (s (s (s (s (s (s (s (s z))))))))"
    );
}

#[test]
fn test_types() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));

    let sty = p("(N -> N) -> N -> N");
    assert_eq!(ctx.infer_type(&sty).to_string(), "Type");
}

#[test]
fn test_structs() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));

    // Struct type has a type
    let sty = p("{ a: N, b: N }");
    assert_eq!(ctx.infer_type(&sty).to_string(), "Type");

    // Struct value has a struct type
    let sval = p("{ a = z, b = z }");
    assert_eq!(ctx.infer_type(&sval).to_string(), "{ a: N, b: N }");

    // Field access
    let fa = p("{ a = z, b = z }.a");
    assert_eq!(ctx.infer_type(&fa).to_string(), "N");
    assert_eq!(ctx.normalize(&fa).to_string(), "z");

    // Field access via variable
    ctx.add_val("p", p("{ a = z, b = z }"));
    let fb = p("p.b");
    assert_eq!(ctx.infer_type(&fb).to_string(), "N");
    assert_eq!(ctx.normalize(&fb).to_string(), "z");
}

#[test]
fn test_equality() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_val("f", p(r"|t: Type| t == N"));

    // Eq type has a type
    let eq_ty = p("N == M");
    assert_eq!(ctx.infer_type(&eq_ty).to_string(), "Type(1)");

    // refl has an Eq type
    let r = p("refl N");
    assert_eq!(ctx.infer_type(&r).to_string(), "N == N");

    // transport type-checks: transport eq f : fn(f N) -> f M
    ctx.add_uninterpreted("eq", p("N == M"));
    let tr = p("transport eq f");
    let ty = ctx.infer_type(&tr);
    let ty = ctx.normalize(&ty);
    assert_eq!(ty.to_string(), "N == N -> M == N");

    // transport with refl reduces to identity
    assert_eq!(
        ctx.normalize(&p("(transport (refl N) f) (refl N)"))
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
    ctx.infer_type(&p(r"|x: M| x"));
    assert_eq!(ctx.infer_type(&p("x")).to_string(), "N");

    // Same for normalization
    ctx.normalize(&p(r"|x: M| x"));
    assert_eq!(ctx.infer_type(&p("x")).to_string(), "N");

    // A defined variable should still reduce after normalizing a shadowing binder
    ctx.add_val("y", p("x"));
    ctx.normalize(&p(r"|y: M| y"));
    assert_eq!(ctx.normalize(&p("y")).to_string(), "x");
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
        ctx.normalize(&p(r"(|y: N, x: N| y)(x, z)")).to_string(),
        "x"
    );
    assert_eq!(
        ctx.normalize(&p(r"(|x: N, x: N| x)(y, z)")).to_string(),
        "z"
    );
    assert_eq!(
        ctx.normalize(&p(r"(|x: N| (|y: N, x: N| y)(x))(z, y)"))
            .to_string(),
        "z"
    );
    assert_eq!(
        ctx.normalize(&p(r"(|f: fn(N) -> N| f(f(x)))(|x: N| s(x))"))
            .to_string(),
        "s (s x)"
    );

    ctx.add_val("ap", p(r"|t: Type, u: Type, f: fn(t) -> u, x: t| f(x)"));
    ctx.assert_equal(
        &p("ap(fn(N) -> N, fn(N) -> N, ap(N, N))"),
        &p(r"|x1: fn(N) -> N, x2: N| x1(x2)"),
    );
}

#[test]
fn test_equality_capture() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("x", Type(0));

    let id_ty = p("fn(x: Type) -> x");
    let const_ty = p("fn(y: Type) -> x");
    assert!(!ctx.equal(&id_ty, &const_ty));
}

#[test]
fn test_rec() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));

    let r = p("make ({ a: N }) { a = z }");
    assert_eq!(ctx.infer_type(&r).to_string(), "{ a: N }");
    assert_eq!(
        ctx.normalize(&p("make ({ a: N }) { a = z }.a")).to_string(),
        "z"
    );

    ctx.add_val("MyTy", p("{ val: N, same: self.val == self.val }"));
    let r = p("make (MyTy) { val = z, same = refl z }");
    assert_eq!(
        ctx.infer_type(&r).to_string(),
        "{ val: N, same: self.val == self.val }"
    );
}

#[test]
fn test_let() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.add_uninterpreted("s", p("fn(N) -> N"));

    // Basic let
    assert_eq!(ctx.normalize(&p("let x = z in s x")).to_string(), "s z");
    assert_eq!(ctx.infer_type(&p("let x = z in x")).to_string(), "N");

    // Nested let
    assert_eq!(
        ctx.normalize(&p("let x = z in let y = s x in s y"))
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
    assert_eq!(ctx.normalize(&expr).to_string(), "z");

    // let rec where a later field references an earlier one via self
    let expr = p(r"
        let rec x: { a: N, b: N } = { a = z, b = x.a }
        in x.b
    ");
    assert_eq!(ctx.normalize(&expr).to_string(), "z");
}

#[test]
fn test_todo() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));

    // todo has the declared type
    assert_eq!(ctx.infer_type(&p("todo N")).to_string(), "N");
    // todo works in larger expressions
    assert_eq!(
        ctx.infer_type(&p(r"|x: N| todo N")).to_string(),
        "fn(x: N) -> N"
    );
}

#[test]
#[should_panic(expected = "tried to normalize")]
fn test_reject_normalize_todo() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.normalize(&p("todo N"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_rec_self_mismatch() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.add_uninterpreted("m", p("M"));
    ctx.add_val("T", p("{ a: Type, b: Type, eq: self.a == self.b }"));
    ctx.infer_type(&p("make (T) { a = N, b = M, eq = refl N }"));
}

#[test]
#[should_panic(expected = "Function expected")]
fn test_reject_apply_non_function() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(&p("z z"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_arg_type_mismatch() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_uninterpreted("f", p("N -> N"));
    ctx.add_uninterpreted("m", p("M"));
    // f expects N but gets M
    ctx.infer_type(&p("f m"));
}

#[test]
#[should_panic(expected = "Type expected")]
fn test_reject_value_as_type() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    // z is a value, not a type — can't use as binder type
    ctx.infer_type(&p(r"|x: z| x"));
}

#[test]
#[should_panic(expected = "Struct type expected")]
fn test_reject_field_on_non_struct() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(&p("z.a"));
}

#[test]
#[should_panic(expected = "Field b not found")]
fn test_reject_missing_field() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.infer_type(&p("{ a = z }.b"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_eq_different_types() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    // z : N and N : Type — different types
    ctx.infer_type(&p("z == N"));
}

#[test]
#[should_panic(expected = "Equality type expected")]
fn test_reject_transport_non_eq() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("z", p("N"));
    ctx.add_uninterpreted("f", p("N -> N"));
    ctx.infer_type(&p("transport z f"));
}

#[test]
#[should_panic(expected = "Function expected for transport")]
fn test_reject_transport_non_function() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("x", p("N"));
    ctx.add_uninterpreted("eq", p("x == x"));
    // second arg must be a function
    ctx.infer_type(&p("transport eq x"));
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_reject_transport_domain_mismatch() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.add_uninterpreted("M", Type(0));
    ctx.add_uninterpreted("x", p("N"));
    ctx.add_uninterpreted("eq", p("x == x"));
    ctx.add_uninterpreted("f", p("M -> M"));
    // eq proves x == x where x: N, but f expects M
    ctx.infer_type(&p("transport eq f"));
}
