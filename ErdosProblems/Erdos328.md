# Erdős Problem 328

[EPC](https://www.erdosproblems.com/328) ·
[announcement](https://www.erdosproblems.com/forum/thread/328#post-7066) ·
[source](https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos328/solution.lean)

## Scope and authorship

The source gives a disproof for **C = 2**, counting ordered representations.
The powers of two form an infinite Sidon set with at most two representations
of each sum. Every finite partition has a part containing distinct `x` and `y`,
so that part has at least two ordered representations of `x + y`.

This refutes the universal partition assertion. It does **not** formalize the
stronger historical Nešetřil–Rödl theorem giving counterexamples for every C.
The source explicitly distinguishes its elementary argument from their proof.
Accordingly, the imported informal argument and formalization are attributed to
AxiomProver, as published by Axiom Math. No individual human proof author is
identified; the EPC poster and Git commit author are not assumed to be authors.

## Provenance and port

Snapshot: `3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab`.
Lean and Mathlib are both explicitly pinned to **4.27.0**. The Mathlib revision is
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.
MIT license, copyright 2026 Axiom Math.

The port preserves the powers-of-two construction, adds the `Erdos328` namespace,
and states the explicit negation as `Erdos328.not_erdos_328`. The Comparator
challenge retains only the representation function, the partition predicate,
and the final assertion.

## Verification

`lake build ErdosProblems.Erdos328 Erdos328` passes, with no solution warnings.
`#print axioms Erdos328.not_erdos_328` reports only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry` or `native_decide` occurs in the solution.

The independent exports pass `Comparator.compareAt`, `Comparator.checkAxioms`,
and Lean's `Environment.replay` kernel check. The full sandboxed Comparator runner
and Nanoda were **not** run: this macOS environment lacks the required Linux
`landrun` sandbox.
