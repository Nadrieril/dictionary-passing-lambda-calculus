use dictionary_passing_lambda_calculus::*;

fn p(s: &str) -> Expr {
    parse(s).unwrap()
}

#[test]
fn test_mutual_rec_types() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", p("Type"));
    ctx.normalize(&p(r"
        let rec EvenList: Type = { val: N, next: OddList }
        and OddList: Type = { val: N, next: EvenList }
        in {=}
    "));
}

#[test]
fn test_mutual_rec_three_types() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", p("Type"));
    ctx.normalize(&p(r"
        let rec A: Type = { b: B, val: N }
        and B: Type = { c: C, val: N }
        and C: Type = { a: A, val: N }
        in {=}
    "));
}

#[test]
fn test_mutual_rec_function_sugar() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", p("Type"));
    ctx.normalize(&p(r"
        let rec Foo(n: N) -> Type = { val: N, link: Bar n }
        and Bar(n: N) -> Type = { val: N, link: Foo n }
        in {=}
    "));
}

#[test]
fn test_mutual_rec_self_type() {
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", p("Type"));
    ctx.add_uninterpreted("z", p("N"));
    let result = ctx.normalize(&p(r"
        let rec my_a: self.my_b = { val = z }
        and my_b: Type = { val: N }
        in my_a.val
    "));
    assert_eq!(result.to_string(), "z");
}
