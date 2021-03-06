# linear_solver
A linear solver designed to be easy to use with Rust enums.

This is a library for automated theorem proving.

Linear solving means that some facts can be replaced with others.
This technique can also be used to make theorem proving more efficient.

If you are looking for a solver that does not remove facts,  
see [monotonic_solver](https://github.com/advancedresearch/monotonic_solver)

*Notice! This solver does not support multiple histories.  
It assumes that when facts are simplified,
they prove the same set of facts without the simplifaction.*

A linear solver can be used to:

- Prove some things in linear logic
- Prove some things in classical logic more efficiently
- Prove some things about where resources are "consumed"
- Constraint solving
- Implement some constraint solving programming language

This project was heavily inspired by
[CHR (Constraint Handling Rules)](https://dtai.cs.kuleuven.be/CHR/)

### Example: Walk

```rust
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
```

### Example: Less or Equal

```rust
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
                return Some(OneTrue {from: ea.clone()});
            }

            for eb in facts {
                if let Le(ref c, ref d) = *eb {
                    if a == d && b == c {
                        // (X <= Y) ∧ (Y <= X) <=> (X = Y)
                        return Some(Inference::replace(
                            vec![ea.clone(), eb.clone()],
                            Eq(a.clone(), b.clone()),
                            cache
                        ))
                    }
                }
            }
        }

        if let Eq(ref a, ref b) = *ea {
            for eb in facts {
                if let Le(ref c, ref d) = *eb {
                    if c == b {
                        // (X = Y) ∧ (Y <= Z) <=> (X = Y) ∧ (X <= Z)
                        return Some(Inference::replace_one(
                            eb.clone(),
                            Le(a.clone(), d.clone()),
                            cache
                        ));
                    } else if d == b {
                        // (X = Y) ∧ (Z <= Y) <=> (X = Y) ∧ (Z <= X)
                        return Some(Inference::replace_one(
                            eb.clone(),
                            Le(c.clone(), a.clone()),
                            cache
                        ));
                    }
                }

                if let Eq(ref c, ref d) = *eb {
                    if b == c {
                        // (X = Y) ∧ (Y = Z) <=> (X = Y) ∧ (X = Z)
                        return Some(Inference::replace_one(
                            eb.clone(),
                            Eq(a.clone(), d.clone()),
                            cache
                        ));
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
```

### Linear logic

When some facts are simplified, e.g.:

```text
X, Y <=> Z
```

You need two new copies of `X` and `Y` to infer another `Z`.
This is because the solver does not remove all copies.

When doing classical theorem proving with a linear solver,
it is common to check that every fact is unique in the input,
and that the `cache` is checked before adding new facts.
This ensures that the solver does not add redundant facts.

However, when doing linear theorem proving,
one can generate redundant facts `Z` for every `X` and `Y`.

### Meaning of goals

Since a linear solver can both introduce new facts
and remove them, it means that termination in the sense of proving a
goal does not make sense, since the goal can be removed later.

Instead, a goal is considered proved when it belongs to the same "cycle".
This is the repeated list of sets of facts that follows from
using a deterministic solver with rules that stops expanding.

The minimum set of facts in the cycle is considered the implicit goal,
because all the other facts in the cycle can be inferred from
this set of facts.

Notice that this a minimum set of facts in a cycle is different
from a minimum set of axioms. A minimum set of axioms is a set of facts
that proves a minimum set of facts with even fewer facts.
With other words, the minimum set of axioms starts outside the cycle.
When it moves inside the cycle, it is identical to some minimum set of facts.

Both the minimum set of facts and the minimum set of axioms can be used
to identify an equivalence between two sets of facts.

### Intuition of `false` and `true`

The intuition of `false` can be thought of as:

- Some fact which everything can be proven from
- Some fact which every contradiction can be simplified to
- A language that contains a contradiction for every truth value

The minimum set of facts in a such language,
when a cycle contains `false`, is `false`.

The intuition of `true` can be thought of as:

- Some fact which every initial fact can be proven from.
- Some fact that contradicts `false`

This means that the initial facts implies `true` and
since it contradicts `false`, if there exists a contradiction
in the initial facts, then they can prove `false`.

Therefore a proof from initial facts is `true`
if it's minimum set of facts does not equals `false`.
