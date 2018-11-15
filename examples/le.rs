/*

In this example, we prove the following:

    X <= Y
    Y <= Z
    Z <= X
    ------
    Y = Z
    Y = X

*/

extern crate linear_solver;

use linear_solver::{solve_minimum, Inference};
use linear_solver::Inference::*;

use std::collections::HashSet;

use self::Expr::*;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Expr {
    Var(&'static str),
    Le(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
}

pub fn infer(cache: &HashSet<Expr>, facts: &[Expr]) -> Option<Inference<Expr>> {
    // Put simplification rules first to find simplest set of facts.
    for ea in facts {
        if let Le(ref a, ref b) = *ea {
            if a == b {
                // (X <= X) <=> true
                return Some(SimplifyTrue {from: vec![ea.clone()]});
            }

            for eb in facts {
                if let Le(ref c, ref d) = *eb {
                    if a == d && b == c {
                        // (X <= Y) ∧ (Y <= X) <=> (X = Y)
                        let new_expr = Eq(a.clone(), b.clone());
                        if !cache.contains(&new_expr) {return Some(Simplify {
                            from: vec![ea.clone(), eb.clone()],
                            to: new_expr
                        })}
                    }
                }
            }
        }

        if let Eq(ref a, ref b) = *ea {
            for eb in facts {
                if let Le(ref c, ref d) = *eb {
                    if c == b {
                        // (X = Y) ∧ (Y <= Z) <=> (X = Y) ∧ (X <= Z)
                        let new_expr = Le(a.clone(), d.clone());
                        if !cache.contains(&new_expr) {return Some(Simplify {
                            from: vec![eb.clone()],
                            to: new_expr
                        })}
                    } else if d == b {
                        // (X = Y) ∧ (Z <= Y) <=> (X = Y) ∧ (Z <= X)
                        let new_expr = Le(c.clone(), a.clone());
                        if !cache.contains(&new_expr) {return Some(Simplify {
                            from: vec![eb.clone()],
                            to: new_expr
                        })}
                    }
                }

                if let Eq(ref c, ref d) = *eb {
                    if b == c {
                        // (X = Y) ∧ (Y = Z) <=> (X = Y) ∧ (X = Z)
                        let new_expr = Eq(a.clone(), d.clone());
                        if !cache.contains(&new_expr) {return Some(Simplify {
                            from: vec![eb.clone()],
                            to: new_expr
                        })};
                    }
                }
            }
        }
    }

    // Put propagation rules last to find simplest set of facts.
    for ea in facts {
        if let Le(ref a, ref b) = *ea {
            for eb in facts {
                if let Le(ref c, ref d) = *eb {
                    if b == c {
                        // (X <= Y) ∧ (Y <= Z) => (X <= Z)
                        let new_expr = Le(a.clone(), d.clone());
                        if !cache.contains(&new_expr) {return Some(Propagate(new_expr))};
                    }
                }
            }
        }
    }
    None
}

pub fn var(name: &'static str) -> Box<Expr> {Box::new(Var(name))}

fn main() {
    let start = vec![
        Le(var("X"), var("Y")), // X <= Y
        Le(var("Y"), var("Z")), // Y <= Z
        Le(var("Z"), var("X")), // Z <= X
    ];

    let res = solve_minimum(start, infer);
    for i in 0..res.len() {
        println!("{:?}", res[i]);
    }
}
