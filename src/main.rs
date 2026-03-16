#![allow(dead_code)]
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use Expr::*;

mod parser;
mod printer;

// A but good
type __<A> = &'static A;
fn __<A>(a: A) -> &'static A {
    Box::leak(Box::new(a))
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
enum Variable {
    User(__<str>),
    SorryDeBruijn(__<str>, u128),
}

impl Variable {
    fn refresh(self) -> Variable {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        match self {
            Variable::User(x) | Variable::SorryDeBruijn(x, _) => {
                let k = COUNTER.fetch_add(1, Ordering::Relaxed);
                Variable::SorryDeBruijn(x, k as u128)
            }
        }
    }
}

type Abstraction = (Variable, Expr, Expr);

#[derive(Clone, Copy, Debug)]
enum Expr {
    Var(Variable),
    Type(usize),
    Pi(__<Abstraction>),
    Lambda(__<Abstraction>),
    App(__<Expr>, __<Expr>),
    Struct(&'static [(__<str>, Expr)]),
    StructTy(&'static [(__<str>, Expr)]),
    Field(__<Expr>, __<str>),
}

impl Expr {
    fn subst(self, s: HashMap<Variable, Expr>) -> Expr {
        match self {
            Var(x) => s.get(&x).copied().unwrap_or(self),
            Type(k) => Type(k),
            Pi(a) => Pi(subst_abstraction(s, a)),
            Lambda(a) => Lambda(subst_abstraction(s, a)),
            App(e1, e2) => App(__(e1.subst(s.clone())), __(e2.subst(s))),
            Struct(fields) => Struct(subst_fields(fields, s)),
            StructTy(fields) => StructTy(subst_fields(fields, s)),
            Field(e, name) => Field(__(e.subst(s)), name),
        }
    }
}

fn subst_abstraction(
    mut s: HashMap<Variable, Expr>,
    (x, t, e): __<Abstraction>,
) -> __<Abstraction> {
    let x_ = x.refresh();
    s.insert(*x, Var(x_));
    __((x_, t.subst(s.clone()), e.subst(s)))
}

fn subst_fields(
    fields: &'static [(__<str>, Expr)],
    s: HashMap<Variable, Expr>,
) -> &'static [(__<str>, Expr)] {
    let fields: Vec<_> = fields
        .iter()
        .map(|&(n, e)| (n, e.subst(s.clone())))
        .collect();
    Box::leak(fields.into_boxed_slice())
}

#[derive(Debug)]
struct Context(Vec<(Variable, (Expr, Option<Expr>))>);

impl Context {
    fn get(&self, x: Variable) -> (Expr, Option<Expr>) {
        self.0
            .iter()
            .rev()
            .find(|elem| x == elem.0)
            .expect("Failed to find variable!")
            .1
    }
    fn lookup_ty(&self, x: Variable) -> Expr {
        self.get(x).0
    }
    fn lookup_value(&self, x: Variable) -> Option<Expr> {
        self.get(x).1
    }
    fn extend(&mut self, x: Variable, t: Expr, value: Option<Expr>) {
        self.0.push((x, (t, value)));
    }
    fn infer_type(&mut self, e: Expr) -> Expr {
        match e {
            Var(x) => self.lookup_ty(x),
            Type(k) => Type(k + 1),
            Pi((x, t1, t2)) => {
                let k1 = self.infer_universe(*t1);
                self.extend(*x, *t1, None);
                let k2 = self.infer_universe(*t2);
                Type(k1.max(k2))
            }
            Lambda((x, t, e)) => {
                let _ = self.infer_universe(*t);
                let te = {
                    self.extend(*x, *t, None);
                    self.infer_type(*e)
                };
                Pi(__((*x, *t, te)))
            }
            App(e1, e2) => {
                let (x, s, t) = self.infer_pi(*e1);
                let te = self.infer_type(*e2);
                self.check_equal(*s, te);
                t.subst([(*x, *e2)].into_iter().collect())
            }
            StructTy(fields) => {
                let k = fields
                    .iter()
                    .map(|&(_, t)| self.infer_universe(t))
                    .max()
                    .unwrap_or(0);
                Type(k)
            }
            Struct(fields) => {
                let ty_fields: Vec<_> = fields
                    .iter()
                    .map(|&(n, e)| (n, self.infer_type(e)))
                    .collect();
                StructTy(Box::leak(ty_fields.into_boxed_slice()))
            }
            Field(e, name) => {
                let te = self.infer_type(*e);
                match self.normalize(te) {
                    StructTy(fields) => {
                        fields
                            .iter()
                            .find(|(n, _)| *n == name)
                            .unwrap_or_else(|| panic!("Field {name} not found"))
                            .1
                    }
                    _ => panic!("Struct type expected for field access"),
                }
            }
        }
    }
    fn infer_universe(&mut self, t: Expr) -> usize {
        match self.infer_type(t) {
            Type(k) => k,
            t => panic!("Type expected, got {t:?}."),
        }
    }
    fn normalize(&mut self, e: Expr) -> Expr {
        match e {
            Var(x) => match self.lookup_value(x) {
                None => Var(x),
                Some(e) => self.normalize(e),
            },
            App(e1, e2) => {
                let e2 = self.normalize(*e2);
                match self.normalize(*e1) {
                    Lambda((x, _, e1_)) => self.normalize(e1_.subst([(*x, e2)].into())),
                    e1 => App(__(e1), __(e2)),
                }
            }
            Type(k) => Type(k),
            Pi(a) => Pi(self.normalize_abstraction(a)),
            Lambda(a) => Lambda(self.normalize_abstraction(a)),
            Struct(fields) => Struct(self.normalize_fields(fields)),
            StructTy(fields) => StructTy(self.normalize_fields(fields)),
            Field(e, name) => match self.normalize(*e) {
                Struct(fields) => {
                    fields
                        .iter()
                        .find(|(n, _)| *n == name)
                        .unwrap_or_else(|| panic!("Field {name} not found"))
                        .1
                }
                e => Field(__(e), name),
            },
        }
    }
    fn normalize_abstraction(&mut self, (x, t, e): __<Abstraction>) -> __<Abstraction> {
        let t = self.normalize(*t);
        self.extend(*x, t, None);
        __((*x, t, self.normalize(*e)))
    }
    fn normalize_fields(
        &mut self,
        fields: &'static [(__<str>, Expr)],
    ) -> &'static [(__<str>, Expr)] {
        let fields: Vec<_> = fields
            .iter()
            .map(|&(n, e)| (n, self.normalize(e)))
            .collect();
        Box::leak(fields.into_boxed_slice())
    }
    fn infer_pi(&mut self, e: Expr) -> __<Abstraction> {
        let t = self.infer_type(e);
        match self.normalize(t) {
            Pi(a) => a,
            _ => panic!("Function expected."),
        }
    }
    fn check_equal(&mut self, e1: Expr, e2: Expr) {
        if !self.equal(e1, e2) {
            panic!("{e1:?} and {e2:?} are not equal.")
        }
    }
    fn equal(&mut self, e1: Expr, e2: Expr) -> bool {
        fn equal(e1: Expr, e2: Expr) -> bool {
            match (e1, e2) {
                (Var(x1), Var(x2)) => x1 == x2,
                (App(e11, e12), App(e21, e22)) => equal(*e11, *e21) && equal(*e12, *e22),
                (Type(k1), Type(k2)) => k1 == k2,
                (Pi(a1), Pi(a2)) => equal_abstraction(a1, a2),
                (Lambda(a1), Lambda(a2)) => equal_abstraction(a1, a2),
                (Struct(f1), Struct(f2)) | (StructTy(f1), StructTy(f2)) => equal_fields(f1, f2),
                (Field(e1, n1), Field(e2, n2)) => n1 == n2 && equal(*e1, *e2),
                _ => false,
            }
        }
        fn equal_abstraction((x, t1, e1): __<Abstraction>, (y, t2, e2): __<Abstraction>) -> bool {
            equal(*t1, *t2) && equal(*e1, e2.subst([(*y, Var(*x))].into()))
        }
        fn equal_fields(f1: &'static [(__<str>, Expr)], f2: &'static [(__<str>, Expr)]) -> bool {
            f1.len() == f2.len()
                && f1
                    .iter()
                    .all(|(n, e)| f2.iter().any(|(n2, e2)| n == n2 && equal(*e, *e2)))
        }

        let e1_ = self.normalize(e1);
        let e2_ = self.normalize(e2);
        equal(e1_, e2_)
    }
}

fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut ctx = Context(vec![
            (Variable::User("N"), (Type(0), None)),
            (Variable::User("z"), (Var(Variable::User("N")), None)),
            (
                Variable::User("s"),
                (
                    Pi(__((
                        Variable::User("_"),
                        Var(Variable::User("N")),
                        Var(Variable::User("N")),
                    ))),
                    None,
                ),
            ),
            (
                Variable::User("three"),
                (
                    parser::parse("fn(_: fn(_: N) -> N) -> fn(_: N) -> N").unwrap(),
                    Some(parser::parse(r"\(f: fn(_: N) -> N) -> \(x: N) -> f (f (f x))").unwrap()),
                ),
            ),
        ]);
        let expr = parser::parse("three (three s) z").unwrap();
        let normalized = ctx.normalize(expr);
        let ty = ctx.infer_type(expr);
        assert_eq!(
            normalized.to_string(),
            "s (s (s (s (s (s (s (s (s z))))))))"
        );
        assert_eq!(ty.to_string(), "N");
    }

    #[test]
    fn test_types() {
        let mut ctx = Context(vec![
            (Variable::User("N"), (Type(0), None)),
            (Variable::User("z"), (Var(Variable::User("N")), None)),
        ]);
        let sty = parser::parse("fn(_: fn(_: N) -> N) -> fn(_: N) -> N").unwrap();
        assert_eq!(ctx.infer_type(sty).to_string(), "Type(0)");
    }

    #[test]
    fn test_structs() {
        let mut ctx = Context(vec![
            (Variable::User("N"), (Type(0), None)),
            (Variable::User("z"), (Var(Variable::User("N")), None)),
        ]);
        // Struct type has a type
        let sty = parser::parse("{ a: N, b: N }").unwrap();
        assert_eq!(ctx.infer_type(sty).to_string(), "Type(0)");

        // Struct value has a struct type
        let sval = parser::parse("{ a = z, b = z }").unwrap();
        assert_eq!(ctx.infer_type(sval).to_string(), "{ a: N, b: N }");

        // Field access
        let fa = parser::parse("{ a = z, b = z }.a").unwrap();
        assert_eq!(ctx.infer_type(fa).to_string(), "N");
        assert_eq!(ctx.normalize(fa).to_string(), "z");

        // Field access via variable
        ctx.extend(
            Variable::User("p"),
            parser::parse("{ a: N, b: N }").unwrap(),
            Some(parser::parse("{ a = z, b = z }").unwrap()),
        );
        let fb = parser::parse("p.b").unwrap();
        assert_eq!(ctx.infer_type(fb).to_string(), "N");
        assert_eq!(ctx.normalize(fb).to_string(), "z");
    }
}
