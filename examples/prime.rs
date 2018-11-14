/*

In this example, we the algorithm Sieve of Eratosthenes to find prime numbers.
The input are numbers `2, 3, 4, ... 99`.
The output are prime numbers in that range.

One only has to check divisibility by prime numbers,
so all numbers that are not primes can be removed.

*/

extern crate linear_solver;

use linear_solver::{solve_minimum, Inference};
use linear_solver::Inference::*;

use std::collections::HashSet;

use self::Expr::*;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Expr {
    Prime(u32),
    Upto(u32),
}

pub fn infer(cache: &HashSet<Expr>, facts: &[Expr]) -> Option<Inference<Expr>> {
    // Put simplification rules first to find simplest set of facts.
    for (ind, ea) in facts.iter().enumerate() {
        match *ea {
            Prime(i) => {
                for (ind2, eb) in facts.iter().enumerate() {
                    if ind == ind2 {continue};
                    match *eb {
                        Prime(j) => {
                            if i % j == 0 {
                                // Remove the number.
                                return Some(SimplifyTrue {from: vec![ea.clone()]});
                            }
                        }
                        _ => {}
                    }
                }
            }
            Upto(n) => {
                if n > 1 {
                    let new_prime = Prime(n);
                    let new_upto = Upto(n-1);
                    if !cache.contains(&new_prime) && !cache.contains(&new_upto) {
                        return Some(SimplifyMany {
                            from: vec![ea.clone()],
                            to: vec![new_prime, new_upto]
                        })
                    }
                } else {
                    return Some(SimplifyTrue {from: vec![ea.clone()]});
                }
            }
        }
    }
    None
}

fn main() {
    let start = vec![Upto(100)];

    let res = solve_minimum(start, infer);
    for i in 0..res.len() {
        println!("{:?}", res[i]);
    }
}
