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

fn leak_slice<T>(v: Vec<T>) -> &'static [T] {
    Box::leak(v.into_boxed_slice())
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

/// Parse a comma-separated list with optional trailing comma, wrapped in delimiters.
fn comma_list<'a, O>(
    open: char,
    close: char,
    item: impl Parser<&'a str, Output = O, Error = DeepError<'a>> + Copy,
) -> impl Parser<&'a str, Output = Vec<O>, Error = DeepError<'a>> {
    delimited(
        ws(nom_char(open)),
        separated_list1(ws(nom_char(',')), item),
        (opt(ws(nom_char(','))), ws(nom_char(close))),
    )
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

/// A single `name = expr` field.
fn field_val(input: &str) -> IResult<'_, (&'static str, Expr)> {
    (ident, ws(nom_char('=')), parse_expr)
        .map(|(n, _, e)| (leak_str(n), e))
        .parse(input)
}

/// A single `name: expr` field.
fn field_ty(input: &str) -> IResult<'_, (&'static str, Expr)> {
    (ident, ws(nom_char(':')), parse_expr)
        .map(|(n, _, e)| (leak_str(n), e))
        .parse(input)
}

/// A single `variable: expr` parameter.
fn param(input: &str) -> IResult<'_, (Variable, Expr)> {
    (variable, ws(nom_char(':')), parse_expr)
        .map(|(x, _, t)| (x, t))
        .parse(input)
}

/// Parse a parenthesized parameter list: `(x: A, y: B, ...)`
fn parse_params(input: &str) -> IResult<'_, Vec<(Variable, Expr)>> {
    comma_list('(', ')', param).parse(input)
}

/// Wrap a return type in nested Pi types for each parameter.
fn wrap_pi(params: &[(Variable, Expr)], ret: Expr) -> Expr {
    params
        .iter()
        .rev()
        .fold(ret, |acc, (x, t)| Pi(*x, __(*t), __(acc)))
}

/// Wrap a body in nested lambdas for each parameter.
fn wrap_lambda(params: &[(Variable, Expr)], body: Expr) -> Expr {
    params
        .iter()
        .rev()
        .fold(body, |acc, (x, t)| Lambda(*x, __(*t), __(acc)))
}

/// `Type(n)`
fn parse_type(input: &str) -> IResult<'_, Expr> {
    map(
        (ws(tag("Type")), ws(nom_char('(')), ws(digit1), ws(nom_char(')'))),
        |(_, _, digits, _): (_, _, &str, _)| Type(digits.parse::<usize>().unwrap()),
    )
    .parse(input)
}

/// `|x: A| body` or `|x: A, y: B| body` (multi-param sugar)
fn parse_lambda(input: &str) -> IResult<'_, Expr> {
    map(
        (
            ws(nom_char('|')),
            separated_list1(ws(nom_char(',')), param),
            opt(ws(nom_char(','))),
            ws(nom_char('|')),
            parse_expr,
        ),
        |(_, params, _, _, body)| wrap_lambda(&params, body),
    )
    .parse(input)
}

/// `fn(x: A) -> B`, `fn(x: A, y: B) -> C` (multi-param sugar), or `fn(A) -> B` (shorthand for `fn(_: A) -> B`)
fn parse_pi(input: &str) -> IResult<'_, Expr> {
    alt((
        // fn(x: A, ...) -> B — named params (possibly multiple)
        map(
            (keyword("fn"), parse_params, ws(tag("->")), parse_expr),
            |(_, params, _, ret)| wrap_pi(&params, ret),
        ),
        // fn(A) -> B — anonymous param
        map(
            (
                keyword("fn"),
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                ws(tag("->")),
                parse_expr,
            ),
            |(_, t, _, e)| Pi(Variable::User("_"), __(t), __(e)),
        ),
    ))
    .parse(input)
}

/// `{ a = e, b = e }` or `{ a: T, b: T }` or `{}` or `{=}`
fn parse_struct(input: &str) -> IResult<'_, Expr> {
    alt((
        // {=} — empty struct value
        map(
            (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}'))),
            |_| Struct(&[]),
        ),
        // { a = e, ... } — struct value
        map(comma_list('{', '}', field_val), |fields| {
            Struct(leak_slice(fields))
        }),
        // { a: T, ... } or {} — struct type
        map(
            delimited(
                ws(nom_char('{')),
                separated_list0(ws(nom_char(',')), field_ty),
                (opt(ws(nom_char(','))), ws(nom_char('}'))),
            ),
            |fields| StructTy(Variable::User("self"), leak_slice(fields)),
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

/// Postfix: atom followed by zero or more `.field` accesses or `(args)` calls.
/// Call syntax `f(a, b)` requires no whitespace before the `(` to distinguish
/// from juxtaposition application `f (a)`.
fn parse_postfix(input: &str) -> IResult<'_, Expr> {
    let (mut input, mut expr) = parse_atom(input)?;
    loop {
        if let Ok((rest, (_, name))) = (ws(nom_char('.')), ident).parse(input) {
            expr = Field(__(expr), leak_str(name));
            input = rest;
        } else if input.starts_with('(') {
            // No whitespace before '(' — parse as call syntax
            if let Ok((rest, args)) = comma_list('(', ')', parse_expr).parse(input) {
                for arg in args {
                    expr = App(__(expr), __(arg));
                }
                input = rest;
            } else {
                break;
            }
        } else {
            break;
        }
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
    let (input, _) = keyword("make").parse(input)?;
    let (input, ty) = delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))).parse(input)?;
    if let Ok((input, _)) =
        (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}'))).parse(input)
    {
        Ok((input, TypedStruct(__(ty), &[])))
    } else {
        let (input, fields) = comma_list('{', '}', field_val).parse(input)?;
        Ok((input, TypedStruct(__(ty), leak_slice(fields))))
    }
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

/// All `let` forms: plain, annotated, rec, and function sugar variants.
fn parse_let(input: &str) -> IResult<'_, Expr> {
    let (input, _) = keyword("let").parse(input)?;
    let (input, is_rec) = map(opt(keyword("rec")), |r| r.is_some()).parse(input)?;
    let (input, name) = variable(input)?;

    // Try to parse optional params, optional return type annotation
    let (input, params) = opt(parse_params).parse(input)?;

    if let Some(params) = params {
        // Function sugar: let [rec] f(params) [-> ret] = body in rest
        if let Ok((input, (_, ret, _, body, _, rest))) =
            (ws(tag("->")), parse_expr, ws(nom_char('=')), parse_expr, keyword("in"), parse_expr)
                .parse(input)
        {
            // With return type annotation — always LetRec
            return Ok((input, LetRec(
                name,
                __(wrap_pi(&params, ret)),
                __(wrap_lambda(&params, body)),
                __(rest),
            )));
        }
        // Without return type — plain Let with lambda body (only if not rec)
        let (input, (_, body, _, rest)) =
            (ws(nom_char('=')), parse_expr, keyword("in"), parse_expr).parse(input)?;
        if is_rec {
            // `let rec f(params) = body` doesn't make sense without a type
            return Err(nom::Err::Error(DeepError::from_error_kind(input, ErrorKind::Tag)));
        }
        return Ok((input, Let(name, __(wrap_lambda(&params, body)), __(rest))));
    }

    if is_rec {
        // let rec x: T = e1 in e2
        let (input, (_, ty, _, e1, _, e2)) =
            (ws(nom_char(':')), parse_expr, ws(nom_char('=')), parse_expr, keyword("in"), parse_expr)
                .parse(input)?;
        Ok((input, LetRec(name, __(ty), __(e1), __(e2))))
    } else if let Ok((input, (_, ty, _, e1, _, e2))) =
        (ws(nom_char(':')), parse_expr, ws(nom_char('=')), parse_expr, keyword("in"), parse_expr)
            .parse(input)
    {
        // let x: T = e1 in e2 — annotated let (desugars to LetRec)
        Ok((input, LetRec(name, __(ty), __(e1), __(e2))))
    } else {
        // let x = e1 in e2
        let (input, (_, e1, _, e2)) =
            (ws(nom_char('=')), parse_expr, keyword("in"), parse_expr).parse(input)?;
        Ok((input, Let(name, __(e1), __(e2))))
    }
}

fn parse_expr(input: &str) -> IResult<'_, Expr> {
    alt((parse_let, parse_lambda, parse_pi, parse_eq)).parse(input)
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
            "|x: Type(0)| x",
            "fn(x: Type(0)) -> x",
            "|f: fn(_: N) -> N, x: N| f (f (f x))",
            "fn(_: fn(_: N) -> N, _: N) -> N",
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
            "{ f = |x: N| x }",
            // Equality
            "x == y",
            "f x == g y",
            "refl x",
            "transport eq f",
            "transport eq f x",
            "(x == y) == (y == x)",
            "|x: N| x == x",
            "refl (f x)",
            // Todo
            "todo N",
            // Make
            "make ({ a: Type(0) }) {=}",
            "make ({ a: Type(0) }) { a = x }",
            // Let
            "let x = y in x",
            "let rec x: Type(0) = N in x",
            r"let rec f(x: Type(0), y: Type(0)) -> Type(0) = x in f",
            "let f(x: Type(0)) = x in f",
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
    fn test_desugaring() {
        let cases = [
            ("let x: Type(0) = N in x", "let rec x: Type(0) = N in x"),
            ("|x: A| |y: B| x", "|x: A, y: B| x"),
            ("fn(x: A) -> fn(y: B) -> C", "fn(x: A, y: B) -> C"),
            ("fn(A) -> fn(B) -> C", "fn(_: A, _: B) -> C"),
            (
                r"let f(x: A) -> B = x in f",
                r"let rec f(x: A) -> B = x in f",
            ),
            (
                r"let f(x: A, y: B) -> C = x in f",
                r"let rec f(x: A, y: B) -> C = x in f",
            ),
            ("fn(f: |x: A| x) -> B", "fn(f: |x: A| x) -> B"),
            // Unannotated function let
            ("let f(x: A) = x in f", "let f(x: A) = x in f"),
            (
                "let f(x: A, y: B) = x in f",
                "let f(x: A, y: B) = x in f",
            ),
            // Call syntax
            ("f(x)", "f x"),
            ("f(x, y)", "f x y"),
            ("f(x, y).a", "(f x y).a"),
            ("f(x)(y)", "f x y"),
        ];
        for (input, expected) in cases {
            let expr = parse(input).unwrap_or_else(|e| panic!("failed to parse {input:?}: {e}"));
            let output = expr.to_string();
            assert_eq!(output, expected, "desugaring failed for {input:?}");
        }
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
