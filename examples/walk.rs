/*

In this example, we reduce a walk (left, right, up, down):

    l, l, u, l, r, d, d, r
    ----------------------
    l, u

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

pub fn infer(cache: &HashSet<Expr>, _facts: &[Expr]) -> Option<Inference<Expr>> {
    // Put simplification rules first to find simplest set of facts.
    if cache.contains(&Left) && cache.contains(&Right) {
        return Some(ManyTrue {from: vec![Left, Right]});
    }
    if cache.contains(&Up) && cache.contains(&Down) {
        return Some(ManyTrue {from: vec![Up, Down]});
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
