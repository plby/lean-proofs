# Erdős Problem 209

[EPC](https://www.erdosproblems.com/209) ·
[announcement](https://www.erdosproblems.com/forum/thread/209#post-7065) ·
[source](https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos209/solution.lean)

For every `d ≥ 4`, there is an arrangement of exactly `d` pairwise nonparallel
real affine lines, with at most three lines through each point and no Gallai
triangle. The source identifies the real plane with the complex numbers.

The informal construction is by Juan García Escudero (2016). The repository and
EPC announcement attribute the formalization to AxiomProver. No individual human
formal author is specified; the commit author (Evan Chen) and EPC poster (Ashvin)
are not taken as proof authors on that evidence alone.

The imported snapshot is `3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab`.
Its `lean-toolchain` and `lakefile.toml` pin Lean and Mathlib to **4.27.0**;
`lake-manifest.json` pins Mathlib to `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
The source is licensed under MIT, copyright 2026 Axiom Math.

## Port to Lean 4.33.0

The construction and final quantified result are preserved. The port adds the
`Erdos209` namespace, updates renamed set lemmas and `push Not`, and removes
unused proof arguments and tactics. The main theorem inlines the conclusion
wrapper while retaining the original geometric definitions.

## Repository layout

- `src/latest/ErdosProblems/Erdos209/Proof.lean`: imported construction and proof.
- `src/latest/ErdosProblems/Erdos209.lean`: final theorem `Erdos209.not_erdos_209`.
- `src/latest/ComparatorChallenges/ErdosProblems/Erdos209.lean`: independent statement.
- `src/latest/ComparatorChallenges/ErdosProblems/Erdos209.json`: Comparator setup.

## Verification

`lake build ErdosProblems.Erdos209 Erdos209` passes. The solution emits no
warnings, and `#print axioms Erdos209.not_erdos_209` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The independently exported challenge and solution pass `Comparator.compareAt`
(statement and definition comparison), `Comparator.checkAxioms`, and Lean's
`Environment.replay` kernel check. The solution contains no `sorry` or
`native_decide`.

The standard sandboxed Comparator runner and Nanoda have **not** been run:
this macOS environment lacks the runner's required Linux `landrun` sandbox.
The library checks above were run directly, without claiming sandbox or Nanoda
verification.
