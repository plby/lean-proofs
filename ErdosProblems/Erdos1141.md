This is a formalized proof of [Erdős Problem 1141](https://www.erdosproblems.com/forum/thread/1141).

Two unconditional proofs are available for Lean/Mathlib 4.33.0:

* [Erdos1141](../src/latest/ErdosProblems/Erdos1141.lean) follows the original
  argument using Pollack's Theorem 1.3. The theorem now has a
  [complete proof](../src/latest/ErdosProblems/Erdos1141/PollackTheorem.lean);
  see the [supporting development](../src/latest/ErdosProblems/Erdos1141/README.md).
* [Erdos1141b](../src/latest/ErdosProblems/Erdos1141b.lean) avoids Pollack entirely.
  It uses a weaker small-prime existence theorem with exponent `31/64`, proved
  from a fourth-moment Burgess estimate and a Siegel lower bound, and treats
  the square case elementarily.

Both prove the same original statements, using only `propext`, `Classical.choice`,
and `Quot.sound`. The older version snapshots are unchanged.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos1141.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos1141.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos1141.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos1141.lean).
