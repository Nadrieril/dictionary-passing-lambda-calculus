use crate::Expr::{self, *};
use crate::{__, Variable};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{char as nom_char, digit1};
use nom::character::complete::{multispace0, satisfy};
use nom::combinator::opt;
use nom::combinator::{map, recognize};
use nom::error::{ErrorKind, ParseError as _};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded};

/// Custom error that always keeps the error at the deepest (furthest) position.
#[derive(Debug)]
struct DeepError<'a> {
    input: &'a str,
}

impl<'a> nom::error::ParseError<&'a str> for DeepError<'a> {
    fn from_error_kind(input: &'a str, _kind: ErrorKind) -> Self {
        DeepError { input }
    }
    fn append(_input: &'a str, _kind: ErrorKind, other: Self) -> Self {
        other
    }
    fn from_char(input: &'a str, _: char) -> Self {
        DeepError { input }
    }
    fn or(self, other: Self) -> Self {
        // Keep whichever error is deeper (shorter remaining input = further into parse).
        if self.input.len() <= other.input.len() {
            self
        } else {
            other
        }
    }
}

impl<'a> nom::error::ContextError<&'a str> for DeepError<'a> {}

type IResult<'a, O> = nom::IResult<&'a str, O, DeepError<'a>>;

fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

/// Skip a single `// ...` line comment.
fn line_comment(input: &str) -> IResult<'_, &str> {
    recognize((tag("//"), take_while(|c| c != '\n'))).parse(input)
}

/// Skip whitespace and `//` comments.
fn skip_ws_and_comments(input: &str) -> IResult<'_, ()> {
    let mut input = input;
    loop {
        let (rest, _) = multispace0.parse(input)?;
        input = rest;
        if let Ok((rest, _)) = line_comment(input) {
            input = rest;
        } else {
            break;
        }
    }
    Ok((input, ()))
}

/// Skip leading whitespace and comments before `inner`.
fn ws<'a, O>(
    inner: impl Parser<&'a str, Output = O, Error = DeepError<'a>>,
) -> impl Parser<&'a str, Output = O, Error = DeepError<'a>> {
    preceded(skip_ws_and_comments, inner)
}

const KEYWORDS: &[&str] = &[
    "fn",
    "in",
    "let",
    "make",
    "rec",
    "refl",
    "todo",
    "transport",
];

/// Identifier: [a-zA-Z_][a-zA-Z0-9_]*, rejecting keywords.
fn ident<'a>(original: &'a str) -> IResult<'a, &'a str> {
    let (rest, id) = ws(recognize(pair(
        satisfy(|c: char| c.is_alphabetic() || c == '_'),
        take_while(|c: char| c.is_alphanumeric() || c == '_'),
    )))
    .parse(original)?;
    if KEYWORDS.contains(&id) {
        return Err(nom::Err::Error(DeepError::from_error_kind(
            original,
            ErrorKind::Tag,
        )));
    }
    Ok((rest, id))
}

fn variable(input: &str) -> IResult<'_, Variable> {
    map(ident, |id| Variable::User(leak_str(id))).parse(input)
}

/// Match a keyword with word boundary check.
fn keyword<'a>(kw: &'static str) -> impl Parser<&'a str, Output = &'a str, Error = DeepError<'a>> {
    move |input: &'a str| {
        let (rest, matched) = ws(tag(kw)).parse(input)?;
        if rest
            .chars()
            .next()
            .is_some_and(|c| c.is_alphanumeric() || c == '_')
        {
            return Err(nom::Err::Error(DeepError::from_error_kind(
                input,
                ErrorKind::Tag,
            )));
        }
        Ok((rest, matched))
    }
}

/// `Type(n)`
fn parse_type(input: &str) -> IResult<'_, Expr> {
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
fn parse_lambda(input: &str) -> IResult<'_, Expr> {
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
fn parse_pi(input: &str) -> IResult<'_, Expr> {
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
fn parse_struct(input: &str) -> IResult<'_, Expr> {
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
fn parse_atom(input: &str) -> IResult<'_, Expr> {
    alt((
        parse_type,
        parse_make,
        parse_struct,
        map(variable, Var),
        delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
    ))
    .parse(input)
}

/// Postfix: atom followed by zero or more `.field` accesses.
fn parse_postfix(input: &str) -> IResult<'_, Expr> {
    let (mut input, mut expr) = parse_atom(input)?;
    while let Ok((rest, (_, name))) = (ws(nom_char('.')), ident).parse(input) {
        expr = Field(__(expr), leak_str(name));
        input = rest;
    }
    Ok((input, expr))
}

/// Application: left-associative sequence of postfix expressions.
/// Keyword expressions (`refl`, `todo`, `transport`) can appear as the head
/// and are then followed by further arguments, e.g. `transport eq f x`.
fn parse_app(input: &str) -> IResult<'_, Expr> {
    let head = alt((parse_refl, parse_todo, parse_transport, parse_postfix));
    (head, many0(parse_postfix))
        .map(|(first, rest)| {
            rest.into_iter()
                .fold(first, |acc, arg| App(__(acc), __(arg)))
        })
        .parse(input)
}

/// `make (ty) { a = e, ... }` or `make (ty) {=}`
fn parse_make(input: &str) -> IResult<'_, Expr> {
    let field_val = |input| {
        (ident, ws(nom_char('=')), parse_expr)
            .map(|(n, _, e)| (leak_str(n), e))
            .parse(input)
    };
    alt((
        map(
            (
                keyword("make"),
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                ws(nom_char('{')),
                ws(nom_char('=')),
                ws(nom_char('}')),
            ),
            |(_, ty, _, _, _)| TypedStruct(__(ty), Box::leak(Vec::new().into_boxed_slice())),
        ),
        map(
            (
                keyword("make"),
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                delimited(
                    ws(nom_char('{')),
                    separated_list1(ws(nom_char(',')), field_val),
                    (opt(ws(nom_char(','))), ws(nom_char('}'))),
                ),
            ),
            |(_, ty, fields)| TypedStruct(__(ty), Box::leak(fields.into_boxed_slice())),
        ),
    ))
    .parse(input)
}

/// `refl e`
fn parse_refl(input: &str) -> IResult<'_, Expr> {
    map((keyword("refl"), parse_postfix), |(_, e)| Refl(__(e))).parse(input)
}

/// `todo ty`
fn parse_todo(input: &str) -> IResult<'_, Expr> {
    map((keyword("todo"), parse_postfix), |(_, t)| Todo(__(t))).parse(input)
}

/// `transport eq f`
fn parse_transport(input: &str) -> IResult<'_, Expr> {
    map(
        (keyword("transport"), parse_postfix, parse_postfix),
        |(_, eq, f)| Transport(__((eq, f))),
    )
    .parse(input)
}

/// Equality: `app == app` or just `app`.
fn parse_eq(input: &str) -> IResult<'_, Expr> {
    let (input, lhs) = parse_app(input)?;
    if let Ok((input, _)) = ws(tag("==")).parse(input) {
        let (input, rhs) = parse_app(input)?;
        Ok((input, Eq(__(lhs), __(rhs))))
    } else {
        Ok((input, lhs))
    }
}

/// `let x = e1 in e2` or `let x: T = e1 in e2`
fn parse_let(input: &str) -> IResult<'_, Expr> {
    alt((
        // let x: T = e1 in e2 — annotated let (desugars to LetRec)
        map(
            (
                keyword("let"),
                variable,
                ws(nom_char(':')),
                parse_expr,
                ws(nom_char('=')),
                parse_expr,
                keyword("in"),
                parse_expr,
            ),
            |(_, x, _, ty, _, e1, _, e2)| LetRec(x, __(ty), __(e1), __(e2)),
        ),
        // let x = e1 in e2
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
        ),
    ))
    .parse(input)
}

/// `let rec x: T = e1 in e2`
fn parse_let_rec(input: &str) -> IResult<'_, Expr> {
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

fn parse_expr(input: &str) -> IResult<'_, Expr> {
    alt((parse_let_rec, parse_let, parse_lambda, parse_pi, parse_eq)).parse(input)
}

/// Parse error with position information. Uses `Display` for pretty-printing,
/// so `unwrap()` shows the error nicely.
pub struct ParseError(String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::fmt::Debug for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\n")?;
        f.write_str(&self.0)
    }
}

/// Format a parse error showing position in context.
fn format_error(full_input: &str, err_input: &str) -> ParseError {
    let offset = full_input.len() - err_input.len();
    let before = &full_input[..offset];
    let line_num = before.chars().filter(|&c| c == '\n').count() + 1;
    let last_newline = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let col = full_input[last_newline..offset].chars().count() + 1;
    let line_end = full_input[offset..]
        .find('\n')
        .map(|i| offset + i)
        .unwrap_or(full_input.len());
    let line_text = &full_input[last_newline..line_end];
    ParseError(format!(
        "parse error at line {line_num}, column {col}:\n  {line_text}\n  {:>width$}",
        "^",
        width = col
    ))
}

pub fn parse(input: &str) -> Result<Expr, ParseError> {
    let input = input.trim();
    match parse_expr(input) {
        Ok((rest, expr)) => {
            let rest = skip_ws_and_comments(rest).map(|(r, _)| r).unwrap_or(rest);
            if rest.is_empty() {
                Ok(expr)
            } else {
                Err(format_error(input, rest.trim_start()))
            }
        }
        Err(nom::Err::Error(e) | nom::Err::Failure(e)) => Err(format_error(input, e.input)),
        Err(e) => Err(ParseError(format!("parse error: {e}"))),
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
            "transport eq f x",
            "(x == y) == (y == x)",
            r"\(x: N) -> x == x",
            "refl (f x)",
            // Todo
            "todo N",
            // Make
            "make ({ a: Type(0) }) {=}",
            "make ({ a: Type(0) }) { a = x }",
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

    #[test]
    fn test_annotated_let() {
        // `let x: T = e in body` desugars to `let rec x: T = e in body`
        assert_eq!(
            parse("let x: Type(0) = N in x").unwrap().to_string(),
            "let rec x: Type(0) = N in x"
        );
    }

    #[test]
    fn test_error_position() {
        // Trailing input: parser stops at the `(` it can't consume
        let err = parse("f (g +) x").unwrap_err().to_string();
        assert!(err.contains("line 1, column 3"), "got:\n{err}");

        // Points to `@` which is an invalid token
        let err = parse("@bad").unwrap_err().to_string();
        assert!(err.contains("line 1, column 1"), "got:\n{err}");

        // Multiline: deepest error is on line 2 at `@`
        let err = parse("let x =\n  @bad in x").unwrap_err().to_string();
        assert!(err.contains("line 2, column 3"), "got:\n{err}");
    }

    #[test]
    fn test_comments() {
        // Comment at end of line
        assert_eq!(parse("x // a variable").unwrap().to_string(), "x");
        // Comment between tokens
        assert_eq!(parse("f // apply\n  x").unwrap().to_string(), "f x");
        // Trailing comment
        assert_eq!(parse("x\n// done").unwrap().to_string(), "x");
    }
}
