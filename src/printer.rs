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
            Pi((x, t, e)) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "fn({x}: ")?;
                t.fmt_prec(f, 0)?;
                write!(f, ") -> ")?;
                e.fmt_prec(f, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Lambda((x, t, e)) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "\\({x}: ")?;
                t.fmt_prec(f, 0)?;
                write!(f, ") -> ")?;
                e.fmt_prec(f, 0)?;
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
            StructTy(fields) => fmt_fields(f, fields, ": "),
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
        }
    }
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
    let expr = Lambda(__((
        Variable::User("f"),
        Pi(__((
            Variable::User("_"),
            Var(Variable::User("N")),
            Var(Variable::User("N")),
        ))),
        Lambda(__((
            Variable::User("x"),
            Var(Variable::User("N")),
            App(
                __(Var(Variable::User("f"))),
                __(App(
                    __(Var(Variable::User("f"))),
                    __(App(
                        __(Var(Variable::User("f"))),
                        __(Var(Variable::User("x"))),
                    )),
                )),
            ),
        ))),
    )));
    assert_eq!(
        expr.to_string(),
        r"\(f: fn(_: N) -> N) -> \(x: N) -> f (f (f x))"
    );
}
