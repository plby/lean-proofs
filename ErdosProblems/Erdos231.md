# Erdős Problem 231

[EPC](https://www.erdosproblems.com/231) ·
[finite-counterexample discussion](https://www.erdosproblems.com/forum/thread/231#post-4320) ·
[source](https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos231/solution.lean)

## Scope and source choice

This is the **finite disproof**: the word
`[0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]` over `Fin 4` has length
`2^4 - 1 = 15` and contains no abelian square. The final theorem refutes the
universal assertion for `k ≥ 2`, using the explicit witness with `k = 4`.
It does not formalize Keränen's stronger infinite-word theorem.

Lorenzo Luccioli's later EPC comments link a complete Aristotle formalization of
the infinite construction, but that source still uses `native_decide` and shares
the verification work with the skipped problem 192. Instead, this import uses
the separate finite proof published in the Axiom Math repository linked from
[EPC #209](https://www.erdosproblems.com/forum/thread/209#post-7065).
The finite counterexample is also discussed explicitly in #231's comments.

EPC credits Nicolaas Govert de Bruijn and Paul Erdős with the informal disproof.
The Axiom Math repository attributes its formalizations to AxiomProver; no
individual human formal author is identified. The source uses ordinary `decide`,
not `native_decide`, and proves the Boolean checker's equivalence to the
mathematical definition.

## Provenance and port

Snapshot: `3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab`.
Its toolchain and Mathlib dependency are both pinned to **4.27.0**; the Mathlib
revision is `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
MIT license, copyright 2026 Axiom Math.

The port adds the `Erdos231` namespace, preserves the explicit witness and checker
correctness proofs, and gives the final theorem the name
`Erdos231.not_erdos_231`. The Comparator challenge contains only the definition of
an abelian square and the explicit quantified conjecture.

## Verification

`lake build ErdosProblems.Erdos231 Erdos231` passes, with no solution warnings.
`#print axioms Erdos231.not_erdos_231` reports only `propext`, `Classical.choice`,
and `Quot.sound`.

The independently exported challenge and solution pass `Comparator.compareAt`,
`Comparator.checkAxioms`, and Lean's `Environment.replay` kernel check.
The full sandboxed Comparator runner and Nanoda were **not** run: this macOS
environment lacks the required Linux `landrun` sandbox.
