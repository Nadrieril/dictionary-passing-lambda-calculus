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

/// Identifier: [a-zA-Z_][a-zA-Z0-9_]*, rejecting the keyword `fn`.
fn ident<'a>(original: &'a str) -> IResult<&'a str, &'a str> {
    let (rest, id) = ws(recognize(pair(
        satisfy(|c: char| c.is_alphabetic() || c == '_'),
        take_while(|c: char| c.is_alphanumeric() || c == '_'),
    )))
    .parse(original)?;
    if id == "fn" {
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

/// Match the keyword `fn` with word boundary check.
fn fn_keyword(input: &str) -> IResult<&str, &str> {
    let (rest, matched) = ws(tag("fn")).parse(input)?;
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

/// `fn(x: A) -> B`
fn parse_pi(input: &str) -> IResult<&str, Expr> {
    map(
        (
            fn_keyword,
            ws(nom_char('(')),
            variable,
            ws(nom_char(':')),
            parse_expr,
            ws(nom_char(')')),
            ws(tag("->")),
            parse_expr,
        ),
        |(_, _, x, _, t, _, _, e)| Pi(__((x, t, e))),
    )
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
            |fields| StructTy(Box::leak(fields.into_boxed_slice())),
        ),
    ))
    .parse(input)
}

/// Atom: variable, Type(n), struct, or parenthesized expression.
fn parse_atom(input: &str) -> IResult<&str, Expr> {
    alt((
        parse_type,
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

/// Application: left-associative sequence of postfix expressions.
fn parse_app(input: &str) -> IResult<&str, Expr> {
    (parse_postfix, many0(parse_postfix))
        .map(|(first, rest)| {
            rest.into_iter()
                .fold(first, |acc, arg| App(__(acc), __(arg)))
        })
        .parse(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    alt((parse_lambda, parse_pi, parse_app)).parse(input)
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
        ];
        for input in cases {
            let expr = parse(input).unwrap_or_else(|e| panic!("failed to parse {input:?}: {e}"));
            let output = expr.to_string();
            assert_eq!(output, input, "roundtrip failed for {input:?}");
        }
    }
}
