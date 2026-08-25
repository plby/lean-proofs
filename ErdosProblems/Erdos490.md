This is a formalized proof of [Erdős Problem 490](https://www.erdosproblems.com/forum/thread/490).

The latest version proves the original bound `|A| |B| < 60 n² / log n`
for all sufficiently large `n`, using only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. The older versions below
still assume four explicit estimates of Dusart.

The latest proof replaces those assumptions with:

* an elementary factorial argument giving `ψ(x) ≤ 1.11 x` eventually;
* the proved Mertens product theorem and a uniform upper sieve;
* weighted deletion and disjoint quotient rectangles in dyadic prime layers;
* a finite Euler-product certificate checked by Lean's kernel, followed by
  rational geometric-series estimates.

The resulting numerical bound is below `59.376`, so the constant `60` is unchanged.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos490.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos490.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos490.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos490.lean).
