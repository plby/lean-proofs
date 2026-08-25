This is a formalized proof of [Erdős Problem 258](https://www.erdosproblems.com/forum/thread/258).

The latest version is unconditional. It proves the formerly assumed
Tao–Teräväinen prime-multiplicity bound by extending the existing Problem 248
sieve. The first five copies of each prime are charged to the distinct-prime
count; Cauchy–Schwarz and single-prime-power counting estimates control the
remaining copies. The final theorem uses only `propext`, `Classical.choice`,
and `Quot.sound`. Older versioned files retain their original assumptions.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos258.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos258.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos258.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos258.lean).
