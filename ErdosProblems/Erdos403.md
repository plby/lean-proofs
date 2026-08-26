# Erdős Problem 403

[EPC](https://www.erdosproblems.com/403) ·
[announcement](https://www.erdosproblems.com/forum/thread/403#post-7067) ·
[source](https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos403/solution.lean)

## Scope and authorship

The source classifies all solutions with **positive, distinct factorial indices**:

| Exponent | Indices |
| --- | --- |
| 0 | {1} |
| 1 | {2} |
| 3 | {2, 3} |
| 5 | {2, 3, 4} |
| 7 | {2, 3, 5} |

The complete classification is retained as `Erdos403.erdos403_complete`.
The final theorem `Erdos403.erdos_403` states finiteness of the set of pairs
`(m, s)` and follows from that classification. An empty index set cannot satisfy
the equation. This does not treat `0!` as a separate allowed summand, nor does it
formalize Lin's stronger 2-adic divisibility bound or the analogous base-three result.

EPC credits independent historical proofs to Frankl and Lin. The imported
artifacts are attributed to **AxiomProver**, as published by Axiom Math. The
repository's generated research notes explicitly state that Lin's original paper
was not accessed and that their argument is independent of it. The actual Lean
proof uses modular exclusions modulo 1008, 32, and 1024 and finite enumeration.
Those research notes are not themselves a verified mathematical proof.
Accordingly, metadata credits AxiomProver for the imported argument and formal
proof, rather than claiming to reproduce either historical argument.
No individual human formal author is identified. Ashvin posted the EPC comment;
Evan Chen committed the files, neither of which establishes proof authorship.

## Provenance and port

Pinned repository snapshot: `3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab`.
The solution was introduced in commit
`8c05a325f5b5cfa7a5eeb2de53337a51cf1a4067` and is unchanged in this snapshot.
The toolchain and Mathlib are explicitly pinned to **4.27.0**; the Mathlib
revision is `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
MIT license, copyright 2026 Axiom Math.

The port adds a namespace, updates Lean/Mathlib compatibility, removes unused helper hypotheses, and derives the
finiteness statement without the source's wrapper predicate. The independent
Comparator challenge imports Mathlib alone and states that finiteness assertion.

## Verification

- `lake build ErdosProblems.Erdos403 Erdos403` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the challenge's intentional `sorry` is expected.
- Both `erdos403_complete` and `erdos_403` depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent `lean4export` exports pass `Comparator.compareAt` and
  `Comparator.checkAxioms`; a fresh Lean environment accepts kernel replay of the
  exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS environment
  lacks `landrun`. Nanoda remains enabled in the Comparator configuration.
- Metadata, import registrations, challenge/configuration consistency, and the
  absence of proof placeholders, `native_decide`, custom axioms, and unsafe
  declarations were checked.
