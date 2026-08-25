This is a formalized proof of [Erdős Problem 659](https://www.erdosproblems.com/forum/thread/659).

The latest version has two unconditional proofs, both using default
computational limits:

* [Erdos659](../src/latest/ErdosProblems/Erdos659.lean) retains the original
  Bernays argument. The full [Bernays theorem](../src/latest/Util/Bernays/Theorem.lean)
  is now proved, with one positive asymptotic constant for every primitive
  positive-definite form of a given discriminant.
* [Erdos659b](../src/latest/ErdosProblems/Erdos659b.lean) avoids Bernays entirely.
  Its [counting proof](../src/latest/ErdosProblems/Erdos659b/Counting.lean)
  bounds values of `x² + 2y²` using Halberstam–Richert and the quadratic
  character modulo eight.

The proofs share only the [lattice geometry](../src/latest/ErdosProblems/Erdos659/Geometry.lean).
The Bernays development and its audit commands are described in its
[README](../src/latest/Util/Bernays/README.md). Earlier version snapshots
still assume Bernays.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos659.lean) (latest stable release).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos659.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos659.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos659.lean).
* [Mathlib/Lean v4.24.0](../src/v4.24.0/ErdosProblems/Erdos659.lean).
