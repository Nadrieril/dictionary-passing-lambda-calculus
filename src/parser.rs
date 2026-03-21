use crate::Expr::{self, *};
use crate::{__, Fields, Variable};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{char as nom_char, digit1};
use nom::character::complete::{multispace0, satisfy};
use nom::combinator::recognize;
use nom::combinator::{cut, opt};
use nom::error::{ErrorKind, ParseError as _};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded};
use ustr::Ustr;

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
    "Type",
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
    ident.map(|id| Variable::user(id)).parse(input)
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
fn field_val(input: &str) -> IResult<'_, (Ustr, Expr)> {
    (
        ident.map(|s| Ustr::from(s)),
        preceded(ws(nom_char('=')), parse_expr),
    )
        .parse(input)
}

/// A single `name: expr` field.
fn field_ty(input: &str) -> IResult<'_, (Ustr, Expr)> {
    (
        ident.map(|s| Ustr::from(s)),
        preceded(ws(nom_char(':')), parse_expr),
    )
        .parse(input)
}

/// A single `variable: expr` parameter.
fn param(input: &str) -> IResult<'_, (Variable, Expr)> {
    (variable, preceded(ws(nom_char(':')), parse_expr)).parse(input)
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
        .fold(ret, |acc, (x, t)| Pi(*x, __(t.clone()), __(acc), None))
}

/// Wrap a body in nested lambdas for each parameter.
fn wrap_lambda(params: &[(Variable, Expr)], body: Expr) -> Expr {
    params
        .iter()
        .rev()
        .fold(body, |acc, (x, t)| Lambda(*x, __(t.clone()), __(acc)))
}

/// `Type(n)` or `Type` (shorthand for `Type(0)`)
fn parse_type(input: &str) -> IResult<'_, Expr> {
    preceded(
        keyword("Type"),
        opt(delimited(ws(nom_char('(')), ws(digit1), ws(nom_char(')')))),
    )
    .map(|digits: Option<&str>| Type(digits.map_or(0, |d| d.parse::<usize>().unwrap())))
    .parse(input)
}

/// `|x: A| body` or `|x: A, y: B| body` (multi-param sugar)
fn parse_lambda(input: &str) -> IResult<'_, Expr> {
    (
        delimited(
            ws(nom_char('|')),
            separated_list1(ws(nom_char(',')), param),
            (opt(ws(nom_char(','))), ws(nom_char('|'))),
        ),
        // Committed: we've seen `|params|`, the body must parse.
        cut(parse_expr),
    )
        .map(|(params, body)| wrap_lambda(&params, body))
        .parse(input)
}

/// `fn(x: A) -> B`, `fn(x: A, y: B) -> C` (multi-param sugar), or `fn(A) -> B` (shorthand for `fn(_: A) -> B`)
fn parse_pi(input: &str) -> IResult<'_, Expr> {
    preceded(
        keyword("fn"),
        alt((
            // fn(x: A, ...) -> B — named params (possibly multiple)
            (parse_params, preceded(ws(tag("->")), parse_expr))
                .map(|(params, ret)| wrap_pi(&params, ret)),
            // fn(A) -> B — anonymous param
            (
                delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
                preceded(ws(tag("->")), parse_expr),
            )
                .map(|(t, e)| Pi(Variable::anon(), __(t), __(e), None)),
        )),
    )
    .parse(input)
}

fn fields_from_vec(v: Vec<(Ustr, Expr)>) -> crate::Fields {
    __(v.into_iter().collect())
}

/// `{ a = e, b = e }` or `{ a: T, b: T }` or `{}` or `{=}`
fn parse_struct(input: &str) -> IResult<'_, Expr> {
    alt((
        // {=} — empty struct value
        (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}')))
            .map(|_| Struct(None, Fields::default())),
        // { a = e, ... } — struct value
        comma_list('{', '}', field_val).map(|fields| Struct(None, fields_from_vec(fields))),
        // { a: T, ... } or {} — struct type
        delimited(
            ws(nom_char('{')),
            separated_list0(ws(nom_char(',')), field_ty),
            (opt(ws(nom_char(','))), ws(nom_char('}'))),
        )
        .map(|fields| StructTy(Variable::user("self"), fields_from_vec(fields))),
    ))
    .parse(input)
}

/// Atom: variable, Type(n), struct, or parenthesized expression.
fn parse_atom(input: &str) -> IResult<'_, Expr> {
    alt((
        parse_type,
        parse_make,
        parse_struct,
        variable.map(Var),
        delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
    ))
    .parse(input)
}

enum PostfixOp {
    Field(Ustr),
    Call(Vec<Expr>),
}

/// A single postfix operation: `.field` or `(args)` (no whitespace before `(`).
fn parse_postfix_op(input: &str) -> IResult<'_, PostfixOp> {
    if input.starts_with('(') {
        // No whitespace before '(' — parse as call syntax
        comma_list('(', ')', parse_expr)
            .map(PostfixOp::Call)
            .parse(input)
    } else {
        preceded(ws(nom_char('.')), ident)
            .map(|name| PostfixOp::Field(Ustr::from(name)))
            .parse(input)
    }
}

/// Postfix: atom followed by zero or more `.field` accesses or `(args)` calls.
/// Call syntax `f(a, b)` requires no whitespace before the `(` to distinguish
/// from juxtaposition application `f (a)`.
fn parse_postfix(input: &str) -> IResult<'_, Expr> {
    (parse_atom, many0(parse_postfix_op))
        .map(|(init, ops)| {
            ops.into_iter().fold(init, |acc, op| match op {
                PostfixOp::Field(name) => Field(__(acc), name),
                PostfixOp::Call(args) => {
                    args.into_iter().fold(acc, |acc, arg| App(__(acc), __(arg)))
                }
            })
        })
        .parse(input)
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
    (
        preceded(
            keyword("make"),
            delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
        ),
        alt((
            (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}')))
                .map(|_| __(Default::default())),
            comma_list('{', '}', field_val).map(fields_from_vec),
        )),
    )
        .map(|(ty, fields)| Struct(Some(__(ty)), fields))
        .parse(input)
}

/// `refl e`
fn parse_refl(input: &str) -> IResult<'_, Expr> {
    preceded(keyword("refl"), parse_postfix)
        .map(|e| Refl(__(e)))
        .parse(input)
}

/// `todo ty`
fn parse_todo(input: &str) -> IResult<'_, Expr> {
    preceded(keyword("todo"), parse_postfix)
        .map(|t| Todo(__(t)))
        .parse(input)
}

/// `transport eq f`
fn parse_transport(input: &str) -> IResult<'_, Expr> {
    preceded(keyword("transport"), (parse_postfix, parse_postfix))
        .map(|(eq, f)| Transport(__(eq), __(f)))
        .parse(input)
}

/// Arrow: `eq -> arrow` (right-associative) or just `eq`.
/// `A -> B` desugars to `fn(_: A) -> B`.
fn parse_arrow(input: &str) -> IResult<'_, Expr> {
    (parse_eq, opt(preceded(ws(tag("->")), cut(parse_arrow))))
        .map(|(lhs, rhs)| match rhs {
            Some(rhs) => Pi(Variable::anon(), __(lhs), __(rhs), None),
            None => lhs,
        })
        .parse(input)
}

/// Equality: `app == app` or just `app`.
fn parse_eq(input: &str) -> IResult<'_, Expr> {
    (parse_app, opt(preceded(ws(tag("==")), cut(parse_app))))
        .map(|(lhs, rhs)| match rhs {
            Some(rhs) => Eq(__(lhs), __(rhs)),
            None => lhs,
        })
        .parse(input)
}

/// Parse `= body in rest`, cutting after `=`.
fn parse_eq_body_in(input: &str) -> IResult<'_, (Expr, Expr)> {
    cut(preceded(
        ws(nom_char('=')),
        (parse_expr, preceded(keyword("in"), parse_expr)),
    ))
    .parse(input)
}

/// All `let` forms: plain, annotated, rec, and function sugar variants.
/// Uses `cut` after commitment points (`:`, `->`, `=`) so that deep errors
/// propagate instead of being swallowed by backtracking.
fn parse_let(input: &str) -> IResult<'_, Expr> {
    let (input, (_, is_rec, name, params)) = (
        keyword("let"),
        opt(keyword("rec")).map(|r| r.is_some()),
        variable,
        opt(parse_params),
    )
        .parse(input)?;
    if let Some(params) = params {
        // Function sugar: committed to function form.
        if let Ok((input, _)) = ws(tag("->")).parse(input) {
            // Committed to annotated function: let [rec] f(params) -> ret = body in rest
            cut((parse_expr, parse_eq_body_in))
                .map(|(ret, (body, rest))| {
                    let ty = __(wrap_pi(&params, ret));
                    let body = __(wrap_lambda(&params, body));
                    if is_rec {
                        LetRec(name, ty, body, __(rest))
                    } else {
                        Let(name, Some(ty), body, __(rest))
                    }
                })
                .parse(input)
        } else if !is_rec {
            parse_eq_body_in
                .map(|(body, rest)| Let(name, None, __(wrap_lambda(&params, body)), __(rest)))
                .parse(input)
        } else {
            // No return type: let f(params) = body in rest
            Err(nom::Err::Failure(DeepError::from_error_kind(
                input,
                ErrorKind::Tag,
            )))
        }
    } else if let Ok((input, _)) = ws(nom_char(':')).parse(input) {
        // Committed to annotated form: let [rec] x: T = e1 in e2
        cut((parse_expr, parse_eq_body_in))
            .map(|(ty, (e1, e2))| {
                if is_rec {
                    LetRec(name, __(ty), __(e1), __(e2))
                } else {
                    Let(name, Some(__(ty)), __(e1), __(e2))
                }
            })
            .parse(input)
    } else {
        // Plain form: let x = e1 in e2
        if is_rec {
            Err(nom::Err::Failure(DeepError::from_error_kind(
                input,
                ErrorKind::Tag,
            )))
        } else {
            parse_eq_body_in
                .map(|(e1, e2)| Let(name, None, __(e1), __(e2)))
                .parse(input)
        }
    }
}

fn parse_expr(input: &str) -> IResult<'_, Expr> {
    alt((parse_let, parse_lambda, parse_pi, parse_arrow)).parse(input)
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
            "Type",
            "Type(1)",
            "f x",
            "f x y",
            "f (g x)",
            "|x: Type| x",
            "fn(x: Type) -> x",
            "|f: N -> N, x: N| f (f (f x))",
            // Arrow syntax
            "N -> N",
            "A -> B -> C",
            "(A -> B) -> C",
            // Structs
            "{ a: Type, b: Type }",
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
            "{ a: { b: Type } }",
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
            "make ({ a: Type }) {=}",
            "make ({ a: Type }) { a = x }",
            // Let
            "let x = y in x",
            "let x: Type = N in x",
            "let rec x: Type = N in x",
            r"let f(x: Type, y: Type) -> Type = x in f",
            r"let rec f(x: Type, y: Type) -> Type = x in f",
            "let f(x: Type) = x in f",
        ];
        for input in cases {
            let expr = parse(input).unwrap_or_else(|e| panic!("failed to parse {input:?}: {e}"));
            let output = expr.to_string();
            assert_eq!(output, input, "roundtrip failed for {input:?}");
        }
    }

    #[test]
    fn test_pi_shorthand() {
        // `fn(A) -> B` parses as `fn(_: A) -> B`, prints as `A -> B`
        assert_eq!(parse("fn(N) -> N").unwrap().to_string(), "N -> N");
        assert_eq!(
            parse("fn(fn(A) -> B) -> C").unwrap().to_string(),
            "(A -> B) -> C"
        );
    }

    #[test]
    fn test_desugaring() {
        let cases = [
            // Type(0) prints as Type
            ("Type(0)", "Type"),
            ("|x: A| |y: B| x", "|x: A, y: B| x"),
            ("fn(x: A) -> fn(y: B) -> C", "fn(x: A, y: B) -> C"),
            ("fn(A) -> fn(B) -> C", "A -> B -> C"),
            // Function with return type (non-rec)
            (r"let f(x: A) -> B = x in f", r"let f(x: A) -> B = x in f"),
            (
                r"let f(x: A, y: B) -> C = x in f",
                r"let f(x: A, y: B) -> C = x in f",
            ),
            // Function with return type (rec)
            (
                r"let rec f(x: A) -> B = x in f",
                r"let rec f(x: A) -> B = x in f",
            ),
            ("fn(f: |x: A| x) -> B", "fn(f: |x: A| x) -> B"),
            // Arrow syntax desugaring
            ("A -> B", "A -> B"),
            ("A -> B -> C", "A -> B -> C"),
            // Unannotated function let
            ("let f(x: A) = x in f", "let f(x: A) = x in f"),
            ("let f(x: A, y: B) = x in f", "let f(x: A, y: B) = x in f"),
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
