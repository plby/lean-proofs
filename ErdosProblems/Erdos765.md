# Erdős Problem 765

[EPC](https://www.erdosproblems.com/765) ·
[formalization comment](https://www.erdosproblems.com/765#post-6480) ·
[pinned source](https://gist.githubusercontent.com/Parcly-Taxel/13d3bd0f1390b0832a42994a09cf91c5/raw/e267a3a494e64019a1a442b3b05438745923883b/Erdos765.lean)

## Statement and authorship

`Erdos765.erdos_765` proves `ex(n; C₄) ~ n^(3/2)/2`.
`C4` is the four-cycle on `Fin 4`, and the extremal number is Mathlib's
`SimpleGraph.extremalNumber`. Containment is ordinary subgraph containment,
not induced-subgraph containment.

The source formalizes Reiman's upper bound and the projective-plane lower
bound of Erdős–Rényi and independently Brown, following the exposition in
Martin Aigner and Günter M. Ziegler's *Proofs from THE BOOK*, sixth edition,
Chapter 28.5. The mathematical authors are recorded as **István Reiman,
Paul Erdős, Alfréd Rényi, and W. G. Brown**.

**Jeremy Tan Jie Rui** (`Parcly-Taxel`) posted the proof generated with
**Aristotle**. His public GitHub profile supplies the full human name.
This import proves the leading asymptotic, not the stronger conjectured
second-order error term, which EPC reports is false.

## Provenance and removal of the extra axiom

The gist has one revision, `e267a3a494e64019a1a442b3b05438745923883b`,
posted on 16 May 2026. The EPC editor link explicitly selects
`mathlib-v4.28.0`. No license or separate Mathlib revision was supplied.

The original source assumes `prime_between`: for each `ε > 0`, all sufficiently
large real `x` have a prime strictly between `x` and `(1 + ε)x`.
That assumption is removed here by importing the already tracked
`PrimeNumberTheoremAnd.Consequences` module. Its theorem `prime_between`
has the same statement, builds on 4.33.0, and its axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The later Jayyhk collection also vendors a proof of this input, but this port
uses the original gist and the repository's existing PNT+ library. No PNT+
code is copied or modified for this import.

## Port and Comparator

The port uses namespace `Erdos765`, separates `Definitions`, `Bounds`, and
`Asymptotics`, updates Mathlib interfaces, and renames the source's final
`erdos765` theorem to `erdos_765`.
The independent Comparator challenge imports only Mathlib and repeats the
four-cycle definition and final asymptotic assertion.

Compatibility changes include graph symmetry packaging, local finite
edge-set instances, renamed unordered-pair lemmas, namespaced containment
helpers, and explicit limit constants. A square-root limit conversion is
proved by eventual equality and field arithmetic rather than automated search.

## Verification

- `lake build ErdosProblems.Erdos765 Erdos765` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has its expected
  placeholder warning.
- `erdos_765` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Independent exports pass `Comparator.compareAt` and `Comparator.checkAxioms`;
  a fresh Lean environment accepts kernel replay of the exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS
  environment lacks `landrun`. Nanoda remains enabled in the configuration.
- Metadata, registrations, independent definitions, configuration consistency,
  and the absence of proof placeholders, `native_decide`, custom axioms, and
  unsafe declarations were checked.
