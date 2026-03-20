use std::fmt;

use crate::Expr::{self, *};
use crate::Variable;

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Variable::User(name) => write!(f, "{name}"),
            Variable::SorryDeBruijn(name, id) => write!(f, "{name}#{id}"),
        }
    }
}

impl Expr {
    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: usize) -> fmt::Result {
        match self {
            Var(x) => write!(f, "{x}"),
            Type(k) => write!(f, "Type({k})"),
            Pi(x, t, e) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "fn({x}: ")?;
                t.fmt_prec(f, 0)?;
                let mut inner = &**e;
                while let Pi(x2, t2, e2) = inner {
                    write!(f, ", {x2}: ")?;
                    t2.fmt_prec(f, 0)?;
                    inner = e2;
                }
                write!(f, ") -> ")?;
                inner.fmt_prec(f, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Lambda(x, t, e) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "|{x}: ")?;
                t.fmt_prec(f, 0)?;
                let mut inner = &**e;
                while let Lambda(x2, t2, e2) = inner {
                    write!(f, ", {x2}: ")?;
                    t2.fmt_prec(f, 0)?;
                    inner = e2;
                }
                write!(f, "| ")?;
                inner.fmt_prec(f, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            App(e1, e2) => {
                if prec > 2 {
                    write!(f, "(")?;
                }
                e1.fmt_prec(f, 2)?;
                write!(f, " ")?;
                e2.fmt_prec(f, 3)?;
                if prec > 2 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Struct(fields) if fields.is_empty() => write!(f, "{{=}}"),
            Struct(fields) => fmt_fields(f, fields, " = "),
            StructTy(_, fields) => fmt_fields(f, fields, ": "),
            TypedStruct(ty, fields) if fields.is_empty() => {
                write!(f, "make (")?;
                ty.fmt_prec(f, 0)?;
                write!(f, ") {{=}}")
            }
            TypedStruct(ty, fields) => {
                write!(f, "make (")?;
                ty.fmt_prec(f, 0)?;
                write!(f, ") ")?;
                fmt_fields(f, fields, " = ")
            }
            Let(x, e1, e2) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "let {x} = ")?;
                e1.fmt_prec(f, 0)?;
                write!(f, " in ")?;
                e2.fmt_prec(f, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            LetRec(x, ty, e1, e2) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                // Detect function sugar: type is nested Pi, body is nested Lambda
                // with matching parameters.
                let (params, ret, body) = peel_fun_sugar(ty, e1);
                if params.is_empty() {
                    write!(f, "let rec {x}: ")?;
                    ret.fmt_prec(f, 0)?;
                } else {
                    write!(f, "let rec {x}(")?;
                    for (i, (px, pt)) in params.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{px}: ")?;
                        pt.fmt_prec(f, 0)?;
                    }
                    write!(f, ") -> ")?;
                    ret.fmt_prec(f, 0)?;
                }
                write!(f, " = ")?;
                body.fmt_prec(f, 0)?;
                write!(f, " in ")?;
                e2.fmt_prec(f, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Field(e, name) => {
                e.fmt_prec(f, 3)?;
                write!(f, ".{name}")
            }
            Eq(a, b) => {
                if prec > 1 {
                    write!(f, "(")?;
                }
                a.fmt_prec(f, 2)?;
                write!(f, " == ")?;
                b.fmt_prec(f, 2)?;
                if prec > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Refl(a) => {
                if prec > 2 {
                    write!(f, "(")?;
                }
                write!(f, "refl ")?;
                a.fmt_prec(f, 3)?;
                if prec > 2 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Transport((eq, ff)) => {
                if prec > 2 {
                    write!(f, "(")?;
                }
                write!(f, "transport ")?;
                eq.fmt_prec(f, 3)?;
                write!(f, " ")?;
                ff.fmt_prec(f, 3)?;
                if prec > 2 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Todo(t) => {
                if prec > 2 {
                    write!(f, "(")?;
                }
                write!(f, "todo ")?;
                t.fmt_prec(f, 3)?;
                if prec > 2 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

/// Peel matching Pi/Lambda layers for function sugar printing.
/// Returns (params, return_type, inner_body).
fn peel_fun_sugar<'a>(
    mut ty: &'a Expr,
    mut body: &'a Expr,
) -> (Vec<(Variable, &'a Expr)>, &'a Expr, &'a Expr) {
    let mut params = Vec::new();
    loop {
        match (ty, body) {
            (Pi(tx, tt, te), Lambda(bx, _bt, be)) if *tx == *bx => {
                params.push((*tx, &**tt));
                ty = te;
                body = be;
            }
            _ => break,
        }
    }
    (params, ty, body)
}

fn fmt_fields(f: &mut fmt::Formatter<'_>, fields: &[(&str, Expr)], sep: &str) -> fmt::Result {
    if fields.is_empty() {
        return write!(f, "{{}}");
    }
    write!(f, "{{ ")?;
    for (i, (name, expr)) in fields.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{name}{sep}")?;
        expr.fmt_prec(f, 0)?;
    }
    write!(f, " }}")
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}

#[test]
fn test_print() {
    use crate::*;
    let expr = Lambda(
        Variable::User("f"),
        __(Pi(
            Variable::User("_"),
            __(Var(Variable::User("N"))),
            __(Var(Variable::User("N"))),
        )),
        __(Lambda(
            Variable::User("x"),
            __(Var(Variable::User("N"))),
            __(App(
                __(Var(Variable::User("f"))),
                __(App(
                    __(Var(Variable::User("f"))),
                    __(App(
                        __(Var(Variable::User("f"))),
                        __(Var(Variable::User("x"))),
                    )),
                )),
            )),
        )),
    );
    assert_eq!(
        expr.to_string(),
        "|f: fn(_: N) -> N, x: N| f (f (f x))"
    );
}
