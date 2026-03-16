use crate::Expr::{self, *};
use crate::{__, Variable};
use nom::IResult;
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{char as nom_char, digit1};
use nom::character::complete::{multispace0, satisfy};
use nom::combinator::opt;
use nom::combinator::{map, recognize};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded};

fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

/// Skip leading whitespace before `inner`.
fn ws<'a, O>(
    inner: impl Parser<&'a str, Output = O, Error = nom::error::Error<&'a str>>,
) -> impl Parser<&'a str, Output = O, Error = nom::error::Error<&'a str>> {
    preceded(multispace0, inner)
}

const KEYWORDS: &[&str] = &["fn", "in", "let", "rec", "refl", "transport"];

/// Identifier: [a-zA-Z_][a-zA-Z0-9_]*, rejecting keywords.
fn ident<'a>(original: &'a str) -> IResult<&'a str, &'a str> {
    let (rest, id) = ws(recognize(pair(
        satisfy(|c: char| c.is_alphabetic() || c == '_'),
        take_while(|c: char| c.is_alphanumeric() || c == '_'),
    )))
    .parse(original)?;
    if KEYWORDS.contains(&id) {
        return Err(nom::Err::Error(nom::error::Error::new(
            original,
            nom::error::ErrorKind::Tag,
        )));
    }
    Ok((rest, id))
}

fn variable(input: &str) -> IResult<&str, Variable> {
    map(ident, |id| Variable::User(leak_str(id))).parse(input)
}

/// Match a keyword with word boundary check.
fn keyword<'a>(
    kw: &'static str,
) -> impl Parser<&'a str, Output = &'a str, Error = nom::error::Error<&'a str>> {
    move |input: &'a str| {
        let (rest, matched) = ws(tag(kw)).parse(input)?;
        if rest
            .chars()
            .next()
            .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            return Err(nom::Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::Tag,
            )));
        }
        Ok((rest, matched))
    }
}

/// `Type(n)`
fn parse_type(input: &str) -> IResult<&str, Expr> {
    map(
        (
            ws(tag("Type")),
            ws(nom_char('(')),
            ws(digit1),
            ws(nom_char(')')),
        ),
        |(_, _, digits, _): (_, _, &str, _)| Type(digits.parse::<usize>().unwrap()),
    )
    .parse(input)
}

/// `\(x: A) -> e`
fn parse_lambda(input: &str) -> IResult<&str, Expr> {
    map(
        (
            ws(nom_char('\\')),
            ws(nom_char('(')),
            variable,
            ws(nom_char(':')),
            parse_expr,
            ws(nom_char(')')),
            ws(tag("->")),
            parse_expr,
        ),
        |(_, _, x, _, t, _, _, e)| Lambda(__((x, t, e))),
    )
    .parse(input)
}

/// `fn(x: A) -> B` or `fn(A) -> B` (shorthand for `fn(_: A) -> B`)
fn parse_pi(input: &str) -> IResult<&str, Expr> {
    alt((
        map(
            (
                keyword("fn"),
                ws(nom_char('(')),
                variable,
                ws(nom_char(':')),
                parse_expr,
                ws(nom_char(')')),
                ws(tag("->")),
                parse_expr,
            ),
            |(_, _, x, _, t, _, _, e)| Pi(__((x, t, e))),
        ),
        map(
            (
                keyword("fn"),
                ws(nom_char('(')),
                parse_expr,
                ws(nom_char(')')),
                ws(tag("->")),
                parse_expr,
            ),
            |(_, _, t, _, _, e)| Pi(__((Variable::User("_"), t, e))),
        ),
    ))
    .parse(input)
}

/// `{ a = e, b = e }` or `{ a: T, b: T }` or `{}` or `{=}`
fn parse_struct(input: &str) -> IResult<&str, Expr> {
    let field_val = |input| {
        (ident, ws(nom_char('=')), parse_expr)
            .map(|(n, _, e)| (leak_str(n), e))
            .parse(input)
    };
    let field_ty = |input| {
        (ident, ws(nom_char(':')), parse_expr)
            .map(|(n, _, e)| (leak_str(n), e))
            .parse(input)
    };
    alt((
        // {=} — empty struct value
        map(
            (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}'))),
            |_| Struct(Box::leak(Vec::new().into_boxed_slice())),
        ),
        // { a = e, ... } — struct value
        map(
            delimited(
                ws(nom_char('{')),
                separated_list1(ws(nom_char(',')), field_val),
                (opt(ws(nom_char(','))), ws(nom_char('}'))),
            ),
            |fields| Struct(Box::leak(fields.into_boxed_slice())),
        ),
        // { a: T, ... } or {} — struct type
        map(
            delimited(
                ws(nom_char('{')),
                separated_list0(ws(nom_char(',')), field_ty),
                (opt(ws(nom_char(','))), ws(nom_char('}'))),
            ),
            |fields| StructTy(Variable::User("self"), Box::leak(fields.into_boxed_slice())),
        ),
    ))
    .parse(input)
}

/// Atom: variable, Type(n), struct, or parenthesized expression.
fn parse_atom(input: &str) -> IResult<&str, Expr> {
    alt((
        parse_type,
        parse_rec,
        parse_struct,
        map(variable, Var),
        delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
    ))
    .parse(input)
}

/// Postfix: atom followed by zero or more `.field` accesses.
fn parse_postfix(input: &str) -> IResult<&str, Expr> {
    let (mut input, mut expr) = parse_atom(input)?;
    while let Ok((rest, (_, name))) = (ws(nom_char('.')), ident).parse(input) {
        expr = Field(__(expr), leak_str(name));
        input = rest;
    }
    Ok((input, expr))
}

/// Application: left-associative sequence of postfix expressions,
/// or `refl`/`transport` keyword expressions.
fn parse_app(input: &str) -> IResult<&str, Expr> {
    alt((
        parse_refl,
        parse_transport,
        (parse_postfix, many0(parse_postfix)).map(|(first, rest)| {
            rest.into_iter()
                .fold(first, |acc, arg| App(__(acc), __(arg)))
        }),
    ))
    .parse(input)
}

/// `rec (ty) { a = e, ... }` or `rec (ty) {=}`
fn parse_rec(input: &str) -> IResult<&str, Expr> {
    let field_val = |input| {
        (ident, ws(nom_char('=')), parse_expr)
            .map(|(n, _, e)| (leak_str(n), e))
            .parse(input)
    };
    alt((
        map(
            (
                keyword("rec"),
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                ws(nom_char('{')),
                ws(nom_char('=')),
                ws(nom_char('}')),
            ),
            |(_, ty, _, _, _)| Rec(__(ty), Box::leak(Vec::new().into_boxed_slice())),
        ),
        map(
            (
                keyword("rec"),
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                delimited(
                    ws(nom_char('{')),
                    separated_list1(ws(nom_char(',')), field_val),
                    (opt(ws(nom_char(','))), ws(nom_char('}'))),
                ),
            ),
            |(_, ty, fields)| Rec(__(ty), Box::leak(fields.into_boxed_slice())),
        ),
    ))
    .parse(input)
}

/// `refl e`
fn parse_refl(input: &str) -> IResult<&str, Expr> {
    map((keyword("refl"), parse_postfix), |(_, e)| Refl(__(e))).parse(input)
}

/// `transport eq f`
fn parse_transport(input: &str) -> IResult<&str, Expr> {
    map(
        (keyword("transport"), parse_postfix, parse_postfix),
        |(_, eq, f)| Transport(__((eq, f))),
    )
    .parse(input)
}

/// Equality: `app == app` or just `app`.
fn parse_eq(input: &str) -> IResult<&str, Expr> {
    let (input, lhs) = parse_app(input)?;
    if let Ok((input, _)) = ws(tag("==")).parse(input) {
        let (input, rhs) = parse_app(input)?;
        Ok((input, Eq(__(lhs), __(rhs))))
    } else {
        Ok((input, lhs))
    }
}

/// `let x = e1 in e2`
fn parse_let(input: &str) -> IResult<&str, Expr> {
    map(
        (
            keyword("let"),
            variable,
            ws(nom_char('=')),
            parse_expr,
            keyword("in"),
            parse_expr,
        ),
        |(_, x, _, e1, _, e2)| Let(x, __(e1), __(e2)),
    )
    .parse(input)
}

/// `let rec x: T = e1 in e2`
fn parse_let_rec(input: &str) -> IResult<&str, Expr> {
    map(
        (
            keyword("let"),
            keyword("rec"),
            variable,
            ws(nom_char(':')),
            parse_expr,
            ws(nom_char('=')),
            parse_expr,
            keyword("in"),
            parse_expr,
        ),
        |(_, _, x, _, ty, _, e1, _, e2)| LetRec(x, __(ty), __(e1), __(e2)),
    )
    .parse(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    alt((parse_let_rec, parse_let, parse_lambda, parse_pi, parse_eq)).parse(input)
}

pub fn parse(input: &str) -> Result<Expr, String> {
    match parse_expr(input.trim()) {
        Ok((rest, expr)) => {
            if rest.trim().is_empty() {
                Ok(expr)
            } else {
                Err(format!("unexpected trailing input: {rest:?}"))
            }
        }
        Err(e) => Err(format!("parse error: {e}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip() {
        let cases = [
            "x",
            "Type(0)",
            "f x",
            "f x y",
            "f (g x)",
            r"\(x: Type(0)) -> x",
            "fn(x: Type(0)) -> x",
            r"\(f: fn(_: N) -> N) -> \(x: N) -> f (f (f x))",
            "fn(_: fn(_: N) -> N) -> fn(_: N) -> N",
            // Structs
            "{ a: Type(0), b: Type(0) }",
            "{ a = x, b = y }",
            "{ x = f y, y = z }",
            "{}",
            "{=}",
            // Field access
            "x.a",
            "x.a.b",
            "f x.a",
            "(f x).a",
            "{ a = x, b = y }.a",
            // Nested structs
            "{ a: { b: Type(0) } }",
            r"{ f = \(x: N) -> x }",
            // Equality
            "x == y",
            "f x == g y",
            "refl x",
            "transport eq f",
            "(x == y) == (y == x)",
            r"\(x: N) -> x == x",
            "refl (f x)",
            // Rec
            "rec ({ a: Type(0) }) {=}",
            "rec ({ a: Type(0) }) { a = x }",
            // Let
            "let x = y in x",
            "let rec x: Type(0) = N in x",
        ];
        for input in cases {
            let expr = parse(input).unwrap_or_else(|e| panic!("failed to parse {input:?}: {e}"));
            let output = expr.to_string();
            assert_eq!(output, input, "roundtrip failed for {input:?}");
        }
    }

    #[test]
    fn test_pi_shorthand() {
        // `fn(A) -> B` parses as `fn(_: A) -> B`
        assert_eq!(parse("fn(N) -> N").unwrap().to_string(), "fn(_: N) -> N");
        assert_eq!(
            parse("fn(fn(A) -> B) -> C").unwrap().to_string(),
            "fn(_: fn(_: A) -> B) -> C"
        );
    }
}
