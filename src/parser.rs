use std::sync::Arc;

use crate::ExprKind::{self, *};
use crate::syntax::Span;
use crate::{Expr, Fields, Variable};
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{char as nom_char, digit1};
use nom::character::complete::{multispace0, satisfy};
use nom::combinator::recognize;
use nom::combinator::{cut, opt};
use nom::error::{ErrorKind, ParseError as _};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded};
use nom::{Input as _, Offset, Parser};
use nom_locate::LocatedSpan;
use ustr::Ustr;

/// Parser input type: a located span carrying the original source as extra data.
type Input<'a> = LocatedSpan<&'a str, Arc<str>>;

/// Custom error that always keeps the error at the deepest (furthest) position.
#[derive(Debug)]
struct DeepError<'a> {
    input: Input<'a>,
}

impl<'a> nom::error::ParseError<Input<'a>> for DeepError<'a> {
    fn from_error_kind(input: Input<'a>, _kind: ErrorKind) -> Self {
        DeepError { input }
    }
    fn append(_input: Input<'a>, _kind: ErrorKind, other: Self) -> Self {
        other
    }
    fn from_char(input: Input<'a>, _: char) -> Self {
        DeepError { input }
    }
    fn or(self, other: Self) -> Self {
        // Keep whichever error is deeper (shorter remaining input = further into parse).
        if self.input.fragment().len() <= other.input.fragment().len() {
            self
        } else {
            other
        }
    }
}

impl<'a> nom::error::ContextError<Input<'a>> for DeepError<'a> {}

type IResult<'a, O> = nom::IResult<Input<'a>, O, DeepError<'a>>;

/// Convert a `LocatedSpan` fragment (as returned by `recognize` / `take`) into our `Span`.
fn to_span(input: &Input<'_>) -> Span {
    Span {
        start: input.location_offset(),
        end: input.location_offset() + input.fragment().len(),
        source: input.extra.clone(),
    }
}

/// Compute a span covering two sub-expressions.
fn span_of_union(a: &Expr, b: &Expr) -> Span {
    a.span().union(b.span())
}

/// Wrap a parser to attach a source span to the resulting `Expr`.
/// Uses nom-locate's `Offset` to compute the consumed input slice.
fn spanned<'a>(
    mut inner: impl Parser<Input<'a>, Output = ExprKind, Error = DeepError<'a>>,
) -> impl Parser<Input<'a>, Output = Expr, Error = DeepError<'a>> {
    move |input: Input<'a>| {
        // Skip leading whitespace so the span starts at the first real token.
        let (input, _) = skip_ws_and_comments(input)?;
        let start = input.clone();
        let (rest, expr) = inner.parse(input)?;
        let span = to_span(&start.take(start.offset(&rest)));
        Ok((rest, expr.into_expr(&span)))
    }
}

fn forget_span<'a>(
    inner: impl Parser<Input<'a>, Output = Expr, Error = DeepError<'a>>,
) -> impl Parser<Input<'a>, Output = ExprKind, Error = DeepError<'a>> {
    inner.map(|e| e.kind().clone())
}

/// Skip a single `// ...` line comment.
fn line_comment(input: Input<'_>) -> IResult<'_, Input<'_>> {
    recognize((tag("//"), take_while(|c| c != '\n'))).parse(input)
}

/// Skip whitespace and `//` comments.
fn skip_ws_and_comments(input: Input<'_>) -> IResult<'_, ()> {
    let mut input = input;
    loop {
        let (rest, _) = multispace0.parse(input)?;
        input = rest;
        if let Ok((rest, _)) = line_comment(input.clone()) {
            input = rest;
        } else {
            break;
        }
    }
    Ok((input, ()))
}

/// Skip leading whitespace and comments before `inner`.
fn ws<'a, O>(
    inner: impl Parser<Input<'a>, Output = O, Error = DeepError<'a>>,
) -> impl Parser<Input<'a>, Output = O, Error = DeepError<'a>> {
    preceded(skip_ws_and_comments, inner)
}

/// Parse a comma-separated list with optional trailing comma, wrapped in delimiters.
fn comma_list<'a, O>(
    open: char,
    close: char,
    item: impl Parser<Input<'a>, Output = O, Error = DeepError<'a>> + Copy,
) -> impl Parser<Input<'a>, Output = Vec<O>, Error = DeepError<'a>> {
    delimited(
        ws(nom_char(open)),
        separated_list1(ws(nom_char(',')), item),
        (opt(ws(nom_char(','))), ws(nom_char(close))),
    )
}

const KEYWORDS: &[&str] = &[
    "Type",
    "and",
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
fn ident<'a>(original: Input<'a>) -> IResult<'a, &'a str> {
    let (rest, id) = ws(recognize(pair(
        satisfy(|c: char| c.is_alphabetic() || c == '_'),
        take_while(|c: char| c.is_alphanumeric() || c == '_'),
    )))
    .parse(original.clone())?;
    let id = *id.fragment();
    if KEYWORDS.contains(&id) {
        return Err(nom::Err::Error(DeepError::from_error_kind(
            original,
            ErrorKind::Tag,
        )));
    }
    Ok((rest, id))
}

fn variable(input: Input<'_>) -> IResult<'_, Variable> {
    ident.map(|id| Variable::user(id)).parse(input)
}

/// Match a keyword with word boundary check.
fn keyword<'a>(
    kw: &'static str,
) -> impl Parser<Input<'a>, Output = Input<'a>, Error = DeepError<'a>> {
    move |input: Input<'a>| {
        let (rest, matched) = ws(tag(kw)).parse(input.clone())?;
        if rest
            .fragment()
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
fn field_val(input: Input<'_>) -> IResult<'_, (Ustr, Expr)> {
    (
        ident.map(|s| Ustr::from(s)),
        preceded(ws(nom_char('=')), parse_expr),
    )
        .parse(input)
}

/// A single `name: expr` field.
fn field_ty(input: Input<'_>) -> IResult<'_, (Ustr, Expr)> {
    (
        ident.map(|s| Ustr::from(s)),
        preceded(ws(nom_char(':')), parse_expr),
    )
        .parse(input)
}

/// A single `variable: expr` parameter.
fn param(input: Input<'_>) -> IResult<'_, (Variable, Expr)> {
    (variable, preceded(ws(nom_char(':')), parse_expr)).parse(input)
}

/// Parse a parenthesized parameter list: `(x: A, y: B, ...)`
fn parse_params(input: Input<'_>) -> IResult<'_, Vec<(Variable, Expr)>> {
    comma_list('(', ')', param).parse(input)
}

/// Wrap a return type in nested Pi types for each parameter.
fn wrap_pi(params: &[(Variable, Expr)], ret: Expr) -> Expr {
    params.iter().rev().fold(ret, |acc, (x, t)| {
        let span = t.span().union(acc.span());
        Pi(*x, t.clone(), acc, None).into_expr(&span)
    })
}

/// Wrap a body in nested lambdas for each parameter.
fn wrap_lambda(params: &[(Variable, Expr)], body: Expr) -> Expr {
    params.iter().rev().fold(body, |acc, (x, t)| {
        let span = t.span().union(acc.span());
        Lambda(*x, t.clone(), acc).into_expr(&span)
    })
}

/// `Type(n)` or `Type` (shorthand for `Type(0)`)
fn parse_type(input: Input<'_>) -> IResult<'_, ExprKind> {
    (preceded(
        keyword("Type"),
        opt(delimited(ws(nom_char('(')), ws(digit1), ws(nom_char(')')))),
    )
    .map(|digits: Option<Input>| {
        Type(digits.map_or(0, |d| d.fragment().parse::<usize>().unwrap()))
    }))
    .parse(input)
}

/// `|x: A| body` or `|x: A, y: B| body` (multi-param sugar)
fn parse_lambda(input: Input<'_>) -> IResult<'_, Expr> {
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
fn parse_pi(input: Input<'_>) -> IResult<'_, Expr> {
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
                .map(|(t, e)| {
                    let span = t.span().union(e.span());
                    Pi(Variable::anon(), t, e, None).into_expr(&span)
                }),
        )),
    )
    .parse(input)
}

fn fields_from_vec(v: Vec<(Ustr, Expr)>) -> crate::Fields {
    Arc::new(v.into_iter().collect())
}

/// `{ a = e, b = e }` or `{ a: T, b: T }` or `{}` or `{=}`
fn parse_struct(input: Input<'_>) -> IResult<'_, ExprKind> {
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
fn parse_atom(input: Input<'_>) -> IResult<'_, Expr> {
    spanned(alt((
        parse_type,
        parse_make,
        parse_struct,
        variable.map(|v| Var(v)),
        delimited(
            ws(nom_char('(')),
            forget_span(parse_expr),
            ws(nom_char(')')),
        ),
    )))
    .parse(input)
}

enum PostfixOp {
    Field(Ustr),
    Call(Vec<Expr>),
}

/// A single postfix operation: `.field` or `(args)` (no whitespace before `(`).
fn parse_postfix_op(input: Input<'_>) -> IResult<'_, PostfixOp> {
    if input.fragment().starts_with('(') {
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
fn parse_postfix(input: Input<'_>) -> IResult<'_, Expr> {
    let (mut rest, mut acc) = parse_atom(input)?;
    loop {
        match parse_postfix_op(rest.clone()) {
            Ok((new_rest, op)) => {
                acc = match op {
                    PostfixOp::Field(name) => {
                        // Extend span from acc's start to end of field name.
                        let span = Span {
                            start: acc.span().start,
                            end: new_rest.location_offset(),
                            source: acc.span().source.clone(),
                        };
                        Field(acc, name).into_expr(&span)
                    }
                    PostfixOp::Call(args) => args.into_iter().fold(acc, |acc, arg| {
                        let span = span_of_union(&acc, &arg);
                        App(acc, arg).into_expr(&span)
                    }),
                };
                rest = new_rest;
            }
            Err(_) => break,
        }
    }
    Ok((rest, acc))
}

/// Application: left-associative sequence of postfix expressions.
/// Keyword expressions (`refl`, `todo`, `transport`) can appear as the head
/// and are then followed by further arguments, e.g. `transport eq f x`.
fn parse_app(input: Input<'_>) -> IResult<'_, Expr> {
    (
        alt((
            spanned(parse_refl),
            spanned(parse_todo),
            spanned(parse_transport),
            parse_postfix,
        )),
        many0(parse_postfix),
    )
        .map(|(first, rest)| {
            rest.into_iter().fold(first, |acc, arg| {
                let span = span_of_union(&acc, &arg);
                App(acc, arg).into_expr(&span)
            })
        })
        .parse(input)
}

/// `make (ty) { a = e, ... }` or `make (ty) {=}`
fn parse_make(input: Input<'_>) -> IResult<'_, ExprKind> {
    (
        preceded(
            keyword("make"),
            delimited(ws(nom_char('(')), parse_expr, ws(nom_char(')'))),
        ),
        alt((
            (ws(nom_char('{')), ws(nom_char('=')), ws(nom_char('}'))).map(|_| Default::default()),
            comma_list('{', '}', field_val).map(fields_from_vec),
        )),
    )
        .map(|(ty, fields)| Struct(Some(ty), fields))
        .parse(input)
}

/// `refl e`
fn parse_refl(input: Input<'_>) -> IResult<'_, ExprKind> {
    preceded(keyword("refl"), parse_postfix)
        .map(|e| Refl(e))
        .parse(input)
}

/// `todo ty`
fn parse_todo(input: Input<'_>) -> IResult<'_, ExprKind> {
    preceded(keyword("todo"), parse_postfix)
        .map(|t| Todo(t))
        .parse(input)
}

/// `transport eq f`
fn parse_transport(input: Input<'_>) -> IResult<'_, ExprKind> {
    preceded(keyword("transport"), (parse_postfix, parse_postfix))
        .map(|(eq, f)| Transport(eq, f))
        .parse(input)
}

/// Arrow: `eq -> arrow` (right-associative) or just `eq`.
/// `A -> B` desugars to `fn(_: A) -> B`.
fn parse_arrow(input: Input<'_>) -> IResult<'_, Expr> {
    (parse_eq, opt(preceded(ws(tag("->")), cut(parse_arrow))))
        .map(|(lhs, rhs)| match rhs {
            Some(rhs) => {
                let span = span_of_union(&lhs, &rhs);
                Pi(Variable::anon(), lhs, rhs, None).into_expr(&span)
            }
            None => lhs,
        })
        .parse(input)
}

/// Equality: `app == app` or just `app`.
fn parse_eq(input: Input<'_>) -> IResult<'_, Expr> {
    (parse_app, opt(preceded(ws(tag("==")), cut(parse_app))))
        .map(|(lhs, rhs)| match rhs {
            Some(rhs) => {
                let span = span_of_union(&lhs, &rhs);
                Eq(lhs, rhs).into_expr(&span)
            }
            None => lhs,
        })
        .parse(input)
}

fn var_ustr(v: Variable) -> Ustr {
    match v {
        Variable::User(u) | Variable::SorryDeBruijn(u, _) => u,
    }
}

/// Desugar `let rec name1: T1 = e1 and name2: T2 = e2 and ... in rest` into a single
/// `let rec` over a combined record type, with field projections in the body and continuation.
fn desugar_mutual_rec(bindings: Vec<(Variable, Expr, Expr)>, rest: Expr) -> ExprKind {
    let mutual_rec = Variable::user("mutual_rec").refresh();

    // Compute the overall span covering all bindings.
    let full_span = bindings.iter().fold(Span::dummy(), |acc, (_, ty, body)| {
        acc.union(ty.span()).union(body.span())
    });

    // Build the combined struct type: { name1: T1, name2: T2, ... }
    let ty_fields: Vec<(Ustr, Expr)> = bindings
        .iter()
        .map(|(name, ty, _)| (var_ustr(*name), ty.clone()))
        .collect();
    let struct_ty =
        StructTy(Variable::user("self"), fields_from_vec(ty_fields)).into_expr(&full_span);

    // Build the body of `mutual_rec`:
    //   let name1 = mutual_rec.name1 in
    //   let name2 = mutual_rec.name2 in
    //   make (struct_ty) { name1 = body1, name2 = body2, ... }
    let val_fields: Vec<(Ustr, Expr)> = bindings
        .iter()
        .map(|(name, _, body)| (var_ustr(*name), body.clone()))
        .collect();
    let make_expr =
        Struct(Some(struct_ty.clone()), fields_from_vec(val_fields)).into_expr(&full_span);
    let struct_body = bindings.iter().rev().fold(make_expr, |acc, (name, ty, _)| {
        let span = acc.span().union(ty.span());
        let field_acc =
            Field(Var(mutual_rec).into_expr(ty.span()), var_ustr(*name)).into_expr(ty.span());
        Let(*name, None, field_acc, acc).into_expr(&span)
    });

    // Build the outer continuation:
    //   let name1 = mutual_rec.name1 in
    //   let name2 = mutual_rec.name2 in
    //   rest
    let outer_rest = bindings.iter().rev().fold(rest, |acc, (name, ty, _)| {
        let span = acc.span().union(ty.span());
        let field_acc =
            Field(Var(mutual_rec).into_expr(ty.span()), var_ustr(*name)).into_expr(ty.span());
        Let(*name, None, field_acc, acc).into_expr(&span)
    });

    LetRec(mutual_rec, struct_ty, struct_body, outer_rest)
}

/// Parse a single `name: type = body` or `name(params) -> ret = body` binding (used after `and`).
fn parse_rec_binding(input: Input<'_>) -> IResult<'_, (Variable, Expr, Expr)> {
    let (input, (name, params)) = (variable, opt(parse_params)).parse(input)?;
    if let Some(params) = params {
        // Function sugar: name(params) -> ret = body
        cut((
            preceded(ws(tag("->")), parse_expr),
            preceded(ws(nom_char('=')), parse_expr),
        ))
        .map(|(ret, body)| (name, wrap_pi(&params, ret), wrap_lambda(&params, body)))
        .parse(input)
    } else {
        // Plain annotated: name: type = body
        cut((
            preceded(ws(nom_char(':')), parse_expr),
            preceded(ws(nom_char('=')), parse_expr),
        ))
        .map(|(ty, body)| (name, ty, body))
        .parse(input)
    }
}

/// Parse `= body in rest`, cutting after `=`.
fn parse_eq_body_in(input: Input<'_>) -> IResult<'_, (Expr, Expr)> {
    cut(preceded(
        ws(nom_char('=')),
        (parse_expr, preceded(keyword("in"), parse_expr)),
    ))
    .parse(input)
}

/// All `let` forms: plain, annotated, rec, and function sugar variants.
/// Uses `cut` after commitment points (`:`, `->`, `=`) so that deep errors
/// propagate instead of being swallowed by backtracking.
fn parse_let(input: Input<'_>) -> IResult<'_, ExprKind> {
    let (input, (_, is_rec, name, params)) = (
        keyword("let"),
        opt(keyword("rec")).map(|r| r.is_some()),
        variable,
        opt(parse_params),
    )
        .parse(input)?;
    if let Some(params) = params {
        // Function sugar: committed to function form.
        if let Ok((input, _)) = ws(tag("->")).parse(input.clone()) {
            if is_rec {
                // let rec f(params) -> ret = body (and ...)* in rest
                cut((
                    parse_expr,
                    preceded(ws(nom_char('=')), parse_expr),
                    many0(preceded(keyword("and"), parse_rec_binding)),
                    preceded(keyword("in"), parse_expr),
                ))
                .map(|(ret, body, extra, rest)| {
                    let ty = wrap_pi(&params, ret);
                    let body = wrap_lambda(&params, body);
                    if extra.is_empty() {
                        LetRec(name, ty, body, rest)
                    } else {
                        let mut bindings = vec![(name, ty, body)];
                        bindings.extend(extra);
                        desugar_mutual_rec(bindings, rest)
                    }
                })
                .parse(input)
            } else {
                // let f(params) -> ret = body in rest
                cut((parse_expr, parse_eq_body_in))
                    .map(|(ret, (body, rest))| {
                        let ty = wrap_pi(&params, ret);
                        let body = wrap_lambda(&params, body);
                        Let(name, Some(ty), body, rest)
                    })
                    .parse(input)
            }
        } else if !is_rec {
            parse_eq_body_in
                .map(|(body, rest)| Let(name, None, wrap_lambda(&params, body), rest))
                .parse(input)
        } else {
            // No return type: let f(params) = body in rest
            Err(nom::Err::Failure(DeepError::from_error_kind(
                input,
                ErrorKind::Tag,
            )))
        }
    } else if let Ok((input, _)) = ws(nom_char(':')).parse(input.clone()) {
        if is_rec {
            // let rec x: T = e1 (and y: U = e2)* in rest
            cut((
                parse_expr,
                preceded(ws(nom_char('=')), parse_expr),
                many0(preceded(keyword("and"), parse_rec_binding)),
                preceded(keyword("in"), parse_expr),
            ))
            .map(|(ty, body, extra, rest)| {
                if extra.is_empty() {
                    LetRec(name, ty, body, rest)
                } else {
                    let mut bindings = vec![(name, ty, body)];
                    bindings.extend(extra);
                    desugar_mutual_rec(bindings, rest)
                }
            })
            .parse(input)
        } else {
            // Committed to annotated form: let x: T = e1 in e2
            cut((parse_expr, parse_eq_body_in))
                .map(|(ty, (e1, e2))| Let(name, Some(ty), e1, e2))
                .parse(input)
        }
    } else {
        // Plain form: let x = e1 in e2
        if is_rec {
            Err(nom::Err::Failure(DeepError::from_error_kind(
                input,
                ErrorKind::Tag,
            )))
        } else {
            parse_eq_body_in
                .map(|(e1, e2)| Let(name, None, e1, e2))
                .parse(input)
        }
    }
}

fn parse_expr(input: Input<'_>) -> IResult<'_, Expr> {
    alt((
        spanned(parse_let),
        spanned(forget_span(parse_lambda)),
        spanned(forget_span(parse_pi)),
        parse_arrow,
    ))
    .parse(input)
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
fn format_error(full_input: &str, offset: usize) -> ParseError {
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
    let source: Arc<str> = Arc::from(input);
    let span_input = LocatedSpan::new_extra(input, source);
    match parse_expr(span_input) {
        Ok((rest, expr)) => {
            let rest_after_ws = skip_ws_and_comments(rest.clone())
                .map(|(r, _)| r)
                .unwrap_or(rest);
            if rest_after_ws.fragment().is_empty() {
                Ok(expr)
            } else {
                let trimmed = rest_after_ws.fragment().trim_start();
                let trim_offset = rest_after_ws.location_offset()
                    + (rest_after_ws.fragment().len() - trimmed.len());
                Err(format_error(input, trim_offset))
            }
        }
        Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
            Err(format_error(input, e.input.location_offset()))
        }
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

    #[test]
    fn test_spans() {
        let expr = parse("f x").unwrap();
        let span = expr.span();
        assert!(!span.is_dummy());
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 3);
        assert_eq!(&*span.source, "f x");

        // Sub-expression spans
        if let App(f, x) = expr.kind() {
            let fs = f.span();
            assert_eq!(&span.source[fs.start..fs.end], "f");
            let xs = x.span();
            assert_eq!(&span.source[xs.start..xs.end], "x");
        } else {
            panic!("expected App");
        }

        // Let expression
        let expr = parse("let x = y in x").unwrap();
        let span = expr.span();
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 14);
    }
}
