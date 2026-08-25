This is a formalized proof of [Erdős Problem 258](https://www.erdosproblems.com/forum/thread/258).

The latest version has two unconditional proofs:

* [Erdos258](../src/latest/ErdosProblems/Erdos258.lean) retains the original
  divisor-tail argument using Tao–Teräväinen. The formerly assumed theorem is
  now proved in [Util/TaoTeravainen](../src/latest/Util/TaoTeravainen/Final.lean),
  using truncated prime-power moments and the existing Problem 248 sieve.
* [Erdos258b](../src/latest/ErdosProblems/Erdos258b.lean) preserves the separate
  proof developed here. It charges the first five copies of each prime to the
  distinct-prime count; Cauchy–Schwarz and single-prime-power counting estimates
  control the remaining copies. It does not import `Util.TaoTeravainen`.

Both final theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
Older versioned files retain their original assumptions.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos258.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos258.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos258.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos258.lean).
