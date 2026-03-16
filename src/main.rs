#![allow(dead_code)]

use std::collections::HashMap;

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
enum Variable {
    User(__<str>),
    SorryDeBruijn(__<str>, u128),
}

impl Variable {
    // Do NOT run more than 1 test.
    fn refresh(self) -> Variable {
        #[expect(non_upper_case_globals)]
        static mut k: u128 = 0;
        unsafe {
            match self {
                Variable::User(x) | Variable::SorryDeBruijn(x, _) => {
                    k += 1;
                    Variable::SorryDeBruijn(x, k)
                }
            }
        }
    }
}

type Abstraction = (Variable, Expr, Expr);

// A but good
type __<A> = &'static A;
fn __<A>(a: A) -> &'static A {
    Box::leak(Box::new(a))
}

#[derive(Clone, Copy, Debug)]
enum Expr {
    Var(Variable),
    Type(usize),
    Pi(__<Abstraction>),
    Lambda(__<Abstraction>),
    App(__<Expr>, __<Expr>),
}
use Expr::*;

impl Expr {
    fn subst(self, s: HashMap<Variable, Expr>) -> Expr {
        match self {
            Var(x) => s.get(&x).copied().unwrap_or(self),
            Type(k) => Type(k),
            Pi(a) => Pi(subst_abstraction(s, a)),
            Lambda(a) => Lambda(subst_abstraction(s, a)),
            App(e1, e2) => App(__(e1.subst(s.clone())), __(e2.subst(s))),
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
        }
    }
    fn infer_universe(&mut self, t: Expr) -> usize {
        match self.normalize(t) {
            Type(k) => k,
            _ => panic!("Type expected."),
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
        }
    }
    fn normalize_abstraction(&mut self, (x, t, e): __<Abstraction>) -> __<Abstraction> {
        let t = self.normalize(*t);
        self.extend(*x, t, None);
        __((*x, t, self.normalize(*e)))
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
                _ => false,
            }
        }
        fn equal_abstraction((x, t1, e1): __<Abstraction>, (y, t2, e2): __<Abstraction>) -> bool {
            equal(*t1, *t2) && equal(*e1, e2.subst([(*y, Var(*x))].into()))
        }

        let e1_ = self.normalize(e1);
        let e2_ = self.normalize(e2);
        equal(e1_, e2_)
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    // Do NOT run more than 1 test until refresh is fixed.
    use std::time::Duration;

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
                    Expr::Pi(__((
                        Variable::User("_"),
                        Expr::Pi(__((
                            Variable::User("_"),
                            Var(Variable::User("N")),
                            Var(Variable::User("N")),
                        ))),
                        Expr::Pi(__((
                            Variable::User("_"),
                            Var(Variable::User("N")),
                            Var(Variable::User("N")),
                        ))),
                    ))),
                    Some(Lambda(__((
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
                    )))),
                ),
            ),
        ]);
        let expr = App(
            __(App(
                __(Var(Variable::User("three"))),
                __(App(
                    __(Var(Variable::User("three"))),
                    __(Var(Variable::User("s"))),
                )),
            )),
            __(Var(Variable::User("z"))),
        );
        println!("{:?}", ctx.normalize(expr));
        println!("{:?}", ctx.infer_type(expr));
        panic!()
    }
}
