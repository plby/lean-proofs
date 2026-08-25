This is a formalized proof of [Erdős Problem 237](https://www.erdosproblems.com/forum/thread/237).

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos237.lean) (latest stable release; original Maynard–Tao argument, unconditional).
* [Alternative dyadic sieve proof](../src/latest/ErdosProblems/Erdos237b.lean) (Mathlib/Lean v4.33.0; unconditional).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos237.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos237.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos237.lean).

The original proof uses the unconditional [Maynard–Tao development](../src/latest/Util/MaynardTao/README.md).
The alternative proof, `Erdos237b`, avoids that quantitative theorem; see its
[proof notes](../docs/erdos237b-unconditional.md).
