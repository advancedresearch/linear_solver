#![deny(missing_docs)]

//! A linear solver designed to be easy to use with Rust enums.
//!
//! This is a library for automated theorem proving.
//!
//! Linear solving means that some facts can be replaced with others.
//! This technique can also be used to make theorem proving more efficient.
//!
//! If you are looking for a solver that does not remove facts,
//! see see [monotonic_solver](https://github.com/advancedresearch/monotonic_solver)
//!
//! *Notice! This solver does not support multiple histories.  
//! It assumes that when facts are simplified,
//! they prove the same set of facts without the simplifaction.*
//!
//! A linear solver can be used to:
//!
//! - Prove some things in linear logic
//! - Prove some things about where resources are "consumed"
//! - Constraint solving
//! - Implement some constraint solving programming language
//!
//! ### Meaning of goals
//!
//! Since a linear solver can both introduce new facts
//! and remove them, it means that termination in the sense of proving a
//! goal does not make sense, since the goal can be removed later.
//!
//! Instead, a goal is considered proved when it belongs to the same "cycle".
//! This is the repeated list of sets of facts that follows from
//! using a deterministic solver with rules that stops expanding.
//!
//! The minimum set of facts in the cycle is considered the implicit goal,
//! because all the other facts in the cycle can be inferred from
//! this set of facts.
//!
//! Notice that this a minimum set of facts in a cycle is different
//! from a minimum set of axioms. A minimum set of axioms is a set of facts
//! that proves a minimum set of facts with even fewer facts.
//! With other words, the minimum set of axioms starts outside the cycle.
//! When it moves inside the cycle, it is identical to some minimum set of facts.
//!
//! Both the minimum set of facts and the minimum set of axioms can be used
//! to identify an equivalence between two sets of facts.
//!
//! ### Intuition of `false` and `true`
//!
//! The intuition of `false` can be thought of as:
//!
//! - Some fact which everything can be proven from
//! - Some fact which every contradiction can be simplified to
//! - A language that contains a contradiction for every truth value
//!
//! The minimum set of facts in a such language,
//! when a cycle contains `false`, is `false`.
//!
//! The intuition of `true` can be thought of as:
//!
//! - Some fact which every initial fact can be proven from.
//! - Some fact that contradicts `false`
//!
//! This means that the initial facts implies `true` and
//! since it contradicts `false`, if there exists a contradiction
//! in the initial facts, then they can prove `false`.
//!
//! Therefore a proof from initial facts is `true`
//! if it's minimum set of facts does not equals `false`.

extern crate bloom;

use std::collections::HashSet;
use std::hash::Hash;
use bloom::{ASMS, BloomFilter};

/// Tells the solver how to treat inference.
pub enum Inference<T> {
    /// Consumes `from` and replaces it with `to`.
    Simplify {
        /// Facts to remove from context.
        from: Vec<T>,
        /// Fact to replace removed facts.
        to: T
    },
    /// Consumes all `from` while producing nothing.
    SimplifyTrue {
        /// Facts to remove from context to be replaced by nothing.
        from: Vec<T>
    },
    /// Add new fact.
    Propagate(T),
}

enum State<T> {
    // Infer new facts.
    Solving,
    // Go to a state where the least amount of facts were present.
    SearchMinimum(Vec<T>),
}

/// Solves the starting condition using the `infer` function for inference.
///
/// Assumes that `infer` is deterministic and leading to a cycle for every input.
/// Finds the minimum set of facts in the cycle.
pub fn solve_minimum<T: Clone + PartialEq + Eq + Hash>(
    mut facts: Vec<T>,
    infer: fn(cache: &HashSet<T>, &[T]) -> Option<Inference<T>>
) -> Vec<T> {
    let mut cache = HashSet::new();
    for s in &facts {
        cache.insert(s.clone());
    }

    // Bloom filter of previous sets of facts.
    // Used to detect whether a given set of facts has already been inferred.
    // Set to a value such that a false positive never happens in practice.
    let false_positive_rate = 0.00000001;
    let expected_num_items = 1000000000;
    let mut filter = BloomFilter::with_rate(false_positive_rate,expected_num_items);

    let mut state = State::Solving;

    loop {
        match state {
            State::Solving => {
                if filter.contains(&facts) {
                    state = State::SearchMinimum(facts.clone());
                    filter = BloomFilter::with_rate(false_positive_rate,expected_num_items);
                }
            }
            State::SearchMinimum(ref fa) if filter.contains(&facts) => {
                // Completed cycle, minimum set of facts is found.
                if fa.len() < facts.len() {
                    facts = fa.clone();
                }
                break;
            }
            State::SearchMinimum(ref fa) if facts.len() < fa.len() => {
                // Found less amounts of facts in cycle.
                state = State::SearchMinimum(facts.clone());
            }
            _ => {}
        }
        filter.insert(&facts);
        if let Some(x) = infer(&cache, &facts) {
            match x {
                Inference::Simplify {from, to} => {
                    let mut new_facts = vec![];
                    for fact in facts.into_iter() {
                        if !from.iter().any(|fa| fa == &fact) {
                            new_facts.push(fact)
                        } else {
                            cache.remove(&fact);
                        }
                    }
                    new_facts.push(to.clone());
                    cache.insert(to);
                    facts = new_facts;
                }
                Inference::SimplifyTrue {from} => {
                    let mut new_facts = vec![];
                    for fact in facts.into_iter() {
                        if !from.iter().any(|fa| fa == &fact) {
                            new_facts.push(fact)
                        } else {
                            cache.remove(&fact);
                        }
                    }
                    facts = new_facts;
                }
                Inference::Propagate(x) => {
                    facts.push(x.clone());
                    cache.insert(x);
                }
            }
        } else {break}
    }
    facts
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
