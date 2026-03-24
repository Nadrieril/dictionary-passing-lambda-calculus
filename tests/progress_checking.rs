use dictionary_passing_lambda_calculus::*;

use Expr::*;

fn p(s: &str) -> Expr {
    parse(s).unwrap()
}

#[test]
fn magic_good() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let rec Copy(t: Type) -> Type = {} in

        let rec Magic(t: Type) -> Type = {
            supertrait1: Copy t,
            supertrait2: Copy t,
        } in

        // impl<T: Magic> Magic for T {}
        let rec MagicImpl(t: Type, t_copy: Copy t) -> Magic t = make (Magic t) {
            supertrait1 = t_copy,
            supertrait2 = (MagicImpl t t_copy).supertrait1, // that's productive!
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Copy {}
        let rec Copy(t: Type) -> Type = {} in

        // trait Magic: Copy {}
        let rec Magic(t: Type) -> Type = {
            supertrait: Copy t,
        } in

        // impl<T: Magic> Magic for T {}, kinda
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            supertrait = (MagicImpl t).supertrait,
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle_through_let() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Copy {}
        let rec Copy(t: Type) -> Type = {} in

        // trait Magic: Copy {}
        let rec Magic(t: Type) -> Type = {
            supertrait: Copy t,
        } in

        // impl<T: Magic> Magic for T {}, kinda
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            supertrait = let sup = (MagicImpl t).supertrait in sup,
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle_more_complicated() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Copy {}
        let rec Copy(t: Type) -> Type = {} in

        // trait Magic: Copy + Magic {}
        let rec Magic(t: Type) -> Type = {
            supertrait: Copy t,
            also_magic: Magic t,
        } in

        // impl<T: Magic> Magic for T {}
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            also_magic = (MagicImpl t),
            supertrait = (MagicImpl t).also_magic.supertrait,
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle_mutual_recursion() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let rec Copy(t: Type) -> Type = {} in

        // trait Super: Copy {}
        let rec Super(t: Type) -> Type = {
            supertrait: Copy t,
        } in

        // trait Trait: Super {}
        let rec Trait(t: Type) -> Type = {
            supertrait: Super t,
        } in

        // impl<T: Trait> Super for T {}
        let ImplSuper(t: Type, t_trait: Trait t) -> Super t = make (Super t) {
            supertrait = t_trait.supertrait.supertrait,
        } in

        // impl<T: Super> Trait for T {}
        let ImplTrait(t: Type, t_super: Super t) -> Trait t = make (Trait t) {
            supertrait = t_super,
        } in

        let rec BothImpls(t: Type) -> { trait: Trait t, super: Super t } = {
            trait = ImplTrait(t, BothImpls(t).super),
            super = ImplSuper(t, BothImpls(t).trait),
        } in

        {=}
    "));
}

#[test]
fn decreasing_chain() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Magic: Magic {}
        let rec Magic(t: Type) -> Type = {
            also_magic: Magic t,
        } in

        // impl<T> Magic for T {}
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            also_magic = (MagicImpl t),
        } in

        {=}
    "));
}

#[test]
fn decreasing_chain_external_knot() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Magic: Magic {}
        let rec Magic(t: Type) -> Type = {
            also_magic: Magic t,
        } in

        // impl<T: Magic> Magic for T {}
        let MagicImpl(t: Type, magic_t: Magic t) -> Magic t = make (Magic t) {
            also_magic = magic_t,
        } in

        let rec MagicImplRec(t: Type) -> Magic t =
            MagicImpl(t, MagicImplRec(t))
        in

        {=}
    "));
}

#[test]
fn decreasing_chain_through_function_call() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Magic: Magic {}
        let rec Magic(t: Type) -> Type = {
            also_magic: Magic t,
        } in

        // impl<T> Magic for T {}
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            also_magic =
                let f(x: Magic t) -> { x: Magic t } = { x = x } in
                f(MagicImpl t).x,
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn infinite_chain() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let rec Magic(t: Type) -> Type = {
            also_magic: Magic t,
        } in

        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            also_magic = (MagicImpl t).also_magic.also_magic,
        } in

        {=}
    "));
}

#[test]
fn finite_chain_reuses_edge() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let N = {} in
        let ty = {
            a: N,
            b: { x: N, y: N },
            c: { x: N, y: N },
        } in
        let rec val: ty = {
            a = val.b.x,
            b = val.c, // this edge gets used twice
            c = { x = val.b.y, y = {=} },
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle_alternate_suffixes() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let N = {} in
        let ty = {
            a: { x: N, y: N },
            b: { x: N, y: N },
        } in
        let rec val: ty = {
            a = val.b,
            b = {
                x = val.a.y,
                y = val.a.x,
            },
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn cycle_proves_cant_truncate() {
    // Proves we can't just truncate the graph to the size of the largest node.
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let N = {} in
        let ty = {
            a: N,
            b: { y: N },
            c: { x: { y: N } },
            d: { y: N },
        } in
        let rec val: ty = {
            a = val.b.y,
            b = val.c.x,
            c = { x = val.d },
            d = { y = val.a },
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn infinite_chain_alternate_suffixes() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let N = {} in
        let rec b_ty: Type(0) = { x: b_ty, y: b_ty, c: b_ty } in
        let ty = {
            a: b_ty,
            b: b_ty,
        } in
        let rec val: ty = {
            a = val.b,
            b = make (b_ty) {
                x = val.a.y,
                y = val.a.x.c,
                c = val.a.x,
            },
        } in

        {=}
    "));
}

#[test]
#[should_panic(expected = "recursive uses are not productive")]
fn infinite_chain_no_increasing_suffix() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let N = {} in
        let rec b_ty: Type(0) = { x: N, c: b_ty } in
        let ty = {
            a: N,
            b: b_ty,
        } in
        let rec val: ty = {
            a = val.b.x,
            b = val.b.c,
        } in

        {=}
    "));
}
