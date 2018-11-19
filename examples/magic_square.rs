/*

In this example, we will prove the following solutions of the 3x3 magic square:

    |2|7|6|  |4|3|8|  |4|9|c|  |6|1|8|  |6|7|2|  |8|1|6|  |8|3|4|
    |9|5|1|  |9|5|1|  |3|5|7|  |7|5|3|  |1|5|9|  |3|5|7|  |1|5|9|
    |4|3|8|  |2|7|6|  |8|1|6|  |2|9|4|  |8|3|4|  |4|9|2|  |6|7|2|

*/

extern crate linear_solver;

use linear_solver::{solve_minimum, Inference};
use linear_solver::Inference::*;

use std::collections::HashSet;

use self::Expr::*;

/// Stores expression.
#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Expr {
    /// The proof is false.
    False,
    /// Constant.
    Const(u8),
    /// Variable.
    Var(&'static str),
    /// An equation of the form `a + b + ... = d + e + ...`.
    Sum(Vec<Expr>, Vec<Expr>),
    /// Sorts equations internally and on both sides.
    SortAll,
    // Expands equations by equality of each side.
    ExpandAll,
    /// Subtract constants on both sides of equation.
    SubtractConstants,
    /// Remove equations of the form `a = a`.
    RemoveRefl,
    /// Remove equal terms on both sides `(a + b = a + c) => (b = c)`.
    RemoveEqualTermsOnBothSides,
    /// Insert assignments e.g `a = 3` into `a + b = 5` = `3 + b = 5`.
    InsertAssignments,
    /// Check contradicting constants, e.g. `3 = 5`.
    CheckContradictingConstants,
    /// Require that there are no negative numbers.
    AbsoluteNumbers,
    /// Sum up constants, e.g. `3 + 5 + a` becomes `8 + a`.
    SumConstants,
    /// Specify a range for a variable.
    Range {var: &'static str, start: u8, end: u8},
    /// Check that an assignment is within a range.
    CheckRange,
    /// Check that all variables are assigned different values.
    UniqueAssignments,
    /// Remove range when variable is assigned.
    /// This is just to clean up result.
    /// Must be executed after the range has been checked.
    RemoveRangeWhenAssigned,
    /// Generate alternatives for a variable by
    /// recursive theorem proving by using the range.
    Narrow(&'static str),
    /// Stores alternatives for a variable.
    Alternatives(&'static str, Vec<u8>),
}

impl Expr {
    /// Returns assignment.
    pub fn assignment(&self) -> Option<(&'static str, u8)> {
        if let Sum(ref ls, ref rs) = *self {
            if ls.len() == 1 {
                if let Var(a) = ls[0] {
                    if rs.len() == 1 {
                        if let Const(x) = rs[0] {return Some((a, x))}
                    } else if rs.len() == 0 {return Some((a, 0))}
                }
            }
        }
        None
    }
}

pub fn infer(cache: &HashSet<Expr>, facts: &[Expr]) -> Option<Inference<Expr>> {
    if cache.contains(&False) {return None};

    // Put simplification rules first to find simplest set of facts.

    // Sorting makes it easier for rules to do their job,
    // and it makes the output easier to read.
    // Wait for `ExpandAll` to finish to avoid premature cycle detection.
    if cache.contains(&SortAll) && !cache.contains(&ExpandAll) {
        for ea in facts {
            if let Sum(ref ls, ref rs) = *ea {
                // Sort terms on left and right side.
                let mut sorted_ls = ls.clone();
                sorted_ls.sort();
                let mut sorted_rs = rs.clone();
                sorted_rs.sort();
                if &sorted_ls != ls || &sorted_rs != rs {
                    let new_expr = Sum(sorted_ls, sorted_rs);
                    return Some(SimplifyOne {from: ea.clone(), to: new_expr});
                }
            }

            if let Sum(ref ls, ref rs) = *ea {
                // Reorder left and right side.
                if ls < rs {
                    return Some(Inference::replace_one(
                        ea.clone(),
                        Sum(rs.clone(), ls.clone()),
                        cache
                    ));
                }
            }
        }
    }

    // Wait for `ExpandAll` to finish so a cycle detection is not triggered prematurely.
    if !cache.contains(&ExpandAll) {

        if cache.contains(&CheckRange) {
            for ea in facts {
                if let Range {var, start, end} = *ea {
                    for eb in facts {
                        if let Some((a, x)) = eb.assignment() {
                            if var == a && (x < start || x > end) {
                                return Some(Propagate(False));
                            }
                        }
                    }
                }
            }
        }

        if cache.contains(&UniqueAssignments) {
            let mut vars = vec![];
            let mut rss = vec![];
            // Find all isolated variables.
            for ea in facts {
                if let Sum(ref ls, ref rs) = *ea {
                    if ls.len() == 1 {
                        if let Var(a) = ls[0] {
                            vars.push(a);
                            rss.push(rs.clone());
                        }
                    }
                }
            }

            // Check for other variables
            for i in 0..vars.len() {
                let var = vars[i];
                for j in 0..vars.len() {
                    if vars[j] != var {
                        if rss[j] == rss[i] {
                            return Some(Propagate(False));
                        }
                    }
                }
            }
        }

        for ea in facts {

            if cache.contains(&RemoveRefl) {
                if let Sum(ref ls, ref rs) = *ea {
                    if ls == rs {
                        return Some(OneTrue {from: ea.clone()});
                    }
                }
            }

            if cache.contains(&RemoveRangeWhenAssigned) {
                if let Some((a, _)) = ea.assignment() {
                    for eb in facts {
                        if let Range {var, ..} = *eb {
                            if var == a {
                                return Some(OneTrue {from: eb.clone()});
                            }
                        }
                    }
                }
            }

            if cache.contains(&CheckContradictingConstants) {
                if let Sum(ref ls, ref rs) = *ea {
                    if rs.len() == 0 && ls.len() == 1 {
                        if let Const(x) = ls[0] {
                            if x != 0 {
                                return Some(Propagate(False));
                            }
                        }
                    }
                }
            }

            if cache.contains(&AbsoluteNumbers) {
                if let Sum(ref ls, ref rs) = *ea {
                    if rs.len() == 0 && ls.len() == 2 {
                        if let Const(x) = ls[0] {
                            if let Var(_) = ls[1] {
                                if x != 0 {
                                    return Some(Propagate(False));
                                }
                            }
                        }
                    }
                }
            }

            if cache.contains(&SumConstants) {
                if let Sum(ref ls, ref rs) = *ea {
                    let mut sum = 0;
                    let mut count = 0;
                    for i in 0..ls.len() {
                        if let Const(x) = ls[i] {
                            sum += x;
                            count += 1;
                        }
                    }
                    if count > 1 {
                        let mut new_ls = vec![];
                        for i in 0..ls.len() {
                            if let Const(_) = ls[i] {continue}
                            new_ls.push(ls[i].clone());
                        }
                        new_ls.push(Const(sum));
                        return Some(Inference::replace_one(
                            ea.clone(),
                            Sum(new_ls, rs.clone()),
                            cache
                        ));
                    }
                }
            }

            if cache.contains(&RemoveEqualTermsOnBothSides) {
                if let Sum(ref ls, ref rs) = *ea {
                    for i in 0..ls.len() {
                        for j in 0..rs.len() {
                            if ls[i] == rs[j] {
                                let mut new_ls = vec![];
                                for k in 0..ls.len() {
                                    if k == i {continue} else {new_ls.push(ls[k].clone())}
                                }
                                let mut new_rs = vec![];
                                for k in 0..rs.len() {
                                    if k == j {continue} else {new_rs.push(rs[k].clone())}
                                }
                                return Some(Inference::replace_one(
                                    ea.clone(),
                                    Sum(new_ls, new_rs),
                                    cache
                                ));
                            }
                        }
                    }
                }
            }

            // Insert assignment into other equations.
            if cache.contains(&InsertAssignments) {
                if let Sum(ref ls, ref rs) = *ea {
                    if ls.len() == 1 && rs.len() == 1 {
                        if let Const(_) = rs[0] {
                            for eb in facts {
                                if ea == eb {continue};
                                if let Sum(ref ls2, ref rs2) = *eb {
                                    for i in 0..ls2.len() {
                                        if ls2[i] == ls[0] {
                                            let new_ls: Vec<Expr> = ls2.clone().into_iter()
                                                .filter(|n| n != &ls[0])
                                                .chain(rs.clone().into_iter())
                                                .collect();
                                            return Some(Inference::replace_one(
                                                eb.clone(),
                                                Sum(new_ls, rs2.clone()),
                                                cache
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Subtract constants on both sides.
            if cache.contains(&SubtractConstants) {
                if let Sum(ref ls, ref rs) = *ea {
                    for i in 0..ls.len() {
                        for j in 0..rs.len() {
                            if let (&Const(x), &Const(y)) = (&ls[i], &rs[j]) {
                                let mut new_ls = vec![];
                                for k in 0..ls.len() {
                                    if k == i {
                                        if x == y {continue}
                                        else if x > y {new_ls.push(Const(x-y))}
                                    } else {
                                        new_ls.push(ls[k].clone())
                                    }
                                }
                                let mut new_rs = vec![];
                                for k in 0..rs.len() {
                                    if k == j {
                                        if x == y {continue}
                                        else if y > x {new_rs.push(Const(y-x))}
                                    } else {
                                        new_rs.push(rs[k].clone())
                                    }
                                }
                                return Some(Inference::replace_one(
                                    ea.clone(),
                                    Sum(new_ls, new_rs),
                                    cache
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    if cache.contains(&ExpandAll) {
        for ea in facts {
            if let Sum(ref ls, ref rs) = *ea {
                for eb in facts {
                    if ea == eb {continue};
                    if let Sum(ref ls2, ref rs2) = *eb {
                        if ls == ls2 {
                            // X = Y & X = Z => Y = Z
                            let new_expr = Sum(rs.clone(), rs2.clone());
                            if !cache.contains(&new_expr) {
                                return Some(Propagate(new_expr));
                            }
                        }
                        if rs == rs2 {
                            // X = Y & Z = Y => X = Z
                            let new_expr = Sum(ls.clone(), ls2.clone());
                            if !cache.contains(&new_expr) {
                                return Some(Propagate(new_expr));
                            }
                        }
                    }
                }
            }
        }

        // Consume `ExpandAll` to allow other simplifications to take place.
        return Some(OneTrue {from: ExpandAll});
    }

    // Narrow down alternatives with recursive theorem proving.
    for ea in facts {
        // A unique alternative means there is an assignment.
        if let Alternatives(a, ref alternatives) = *ea {
            if alternatives.len() == 1 {
                return Some(Inference::replace_one(
                    ea.clone(),
                    Sum(vec![Var(a)], vec![Const(alternatives[0])]),
                    cache
                ));
            }
            if alternatives.len() == 0 {
                return Some(Propagate(False));
            }
        }

        if let Narrow(a) = *ea {
            for eb in facts {
                if let Range {var, start, end} = *eb {
                    if var == a {
                        // Try the whole range.
                        // Call the solver recursively
                        let mut alternatives = vec![];
                        for k in start..end+1 {
                            let mut new_facts = vec![];
                            for i in 0..facts.len() {
                                // Ignore `Narrow` directive to avoid infinite recursion.
                                if &facts[i] == ea {continue};
                                new_facts.push(facts[i].clone());
                            }
                            new_facts.push(Sum(vec![Var(var)], vec![Const(k)]));
                            let res = solve_minimum(new_facts, infer);
                            if !res.iter().any(|n| n == &False) {
                                alternatives.push(k);
                            }
                        }
                        let new_expr = Alternatives(a, alternatives);
                        return Some(SimplifyOne {from: ea.clone(), to: new_expr});
                    }
                }
            }
        }
    }

    None
}

fn main() {
    let start = vec![
        // a + b + c = 15
        Sum(vec![Var("a"), Var("b"), Var("c")], vec![Const(15)]),
        // d + e + f = 15
        Sum(vec![Var("d"), Var("e"), Var("f")], vec![Const(15)]),
        // g + h + i = 15
        Sum(vec![Var("g"), Var("h"), Var("i")], vec![Const(15)]),

        // a + d + g = 15
        Sum(vec![Var("a"), Var("d"), Var("g")], vec![Const(15)]),
        // b + e + h = 15
        Sum(vec![Var("b"), Var("e"), Var("h")], vec![Const(15)]),
        // c + f + i = 15
        Sum(vec![Var("c"), Var("f"), Var("i")], vec![Const(15)]),

        // a + e + i = 15
        Sum(vec![Var("a"), Var("e"), Var("i")], vec![Const(15)]),
        // c + e + g = 15
        Sum(vec![Var("c"), Var("e"), Var("g")], vec![Const(15)]),

        Range {var: "a", start: 1, end: 9},
        Range {var: "b", start: 1, end: 9},
        Range {var: "c", start: 1, end: 9},
        Range {var: "d", start: 1, end: 9},
        Range {var: "e", start: 1, end: 9},
        Range {var: "f", start: 1, end: 9},
        Range {var: "g", start: 1, end: 9},
        Range {var: "h", start: 1, end: 9},
        Range {var: "i", start: 1, end: 9},

        // List of tactics.
        SortAll,
        ExpandAll,
        RemoveRefl,
        RemoveEqualTermsOnBothSides,
        SubtractConstants,
        InsertAssignments,
        CheckContradictingConstants,
        AbsoluteNumbers,
        SumConstants,
        CheckRange,
        UniqueAssignments,
        RemoveRangeWhenAssigned,

        // Uncomment/comment the following to investiage various solutions.

        /*
        // Get the alternative values that "a" can have.
        // Multiple `Narrow` means nested recursive theorem proving,
        // such that the top alternative is narrowed down.
        Narrow("a"),
        Narrow("b"),
        // Narrow("c"), // skip "c" because we don't need it.
        // Better to try "d", since it is better at narrowing down results.
        Narrow("d"),
        */

        Sum(vec![Var("a")], vec![Const(2)]),
        Sum(vec![Var("b")], vec![Const(7)]),
        Narrow("d"),

        /*
        Sum(vec![Var("a")], vec![Const(4)]),
        Sum(vec![Var("b")], vec![Const(3)]),
        Narrow("d"),
        */

        /*
        Sum(vec![Var("a")], vec![Const(4)]),
        Sum(vec![Var("b")], vec![Const(9)]),
        Narrow("d"),
        */

        /*
        Sum(vec![Var("a")], vec![Const(6)]),
        Sum(vec![Var("b")], vec![Const(1)]),
        Narrow("d"),
        */

        /*
        Sum(vec![Var("a")], vec![Const(6)]),
        Sum(vec![Var("b")], vec![Const(7)]),
        Narrow("d"),
        */

        /*
        Sum(vec![Var("a")], vec![Const(8)]),
        Sum(vec![Var("b")], vec![Const(1)]),
        Narrow("d"),
        */

        /*
        Sum(vec![Var("a")], vec![Const(8)]),
        Sum(vec![Var("b")], vec![Const(3)]),
        Narrow("d"),
        */
    ];

    let res = solve_minimum(start, infer);
    for i in 0..res.len() {
        println!("{:?}", res[i]);
    }
}
