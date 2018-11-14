/*

In this example, we reduce a walk (left, right, up, down):

    l, l, u, l, r, d, d, r
    ----------------------
    u, l

*/

extern crate linear_solver;

use linear_solver::{solve_minimum, Inference};
use linear_solver::Inference::*;

use std::collections::HashSet;

use self::Expr::*;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Expr {
    Left,
    Right,
    Up,
    Down,
}

pub fn infer(cache: &HashSet<Expr>, facts: &[Expr]) -> Option<Inference<Expr>> {
    // Put simplification rules first to find simplest set of facts.
    for ea in facts {
        if let Left = *ea {
            if cache.contains(&Right) {
                return Some(SimplifyTrue {from: vec![Left, Right]});
            }
        }
        if let Right = *ea {
            if cache.contains(&Left) {
                return Some(SimplifyTrue {from: vec![Left, Right]});
            }
        }
        if let Up = *ea {
            if cache.contains(&Down) {
                return Some(SimplifyTrue {from: vec![Up, Down]});
            }
        }
        if let Down = *ea {
            if cache.contains(&Up) {
                return Some(SimplifyTrue {from: vec![Up, Down]});
            }
        }
    }
    None
}

fn main() {
    let start = vec![
        Left,
        Left,
        Up,
        Left,
        Right,
        Down,
        Down,
        Right,
    ];

    let res = solve_minimum(start, infer);
    for i in 0..res.len() {
        println!("{:?}", res[i]);
    }
}
