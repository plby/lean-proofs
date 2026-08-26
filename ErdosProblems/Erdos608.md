# Erdős Problem 608

[EPC](https://www.erdosproblems.com/608) ·
[formal-status submission](https://github.com/teorth/erdosproblems/pull/365) ·
[pinned source](https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908)

## Scope and authorship

The final theorem `Erdos608.not_erdos_608` refutes the asymptotic assertion that
all sufficiently large graphs with more than `n²/4` edges have at least `2n²/9`
edges lying on a five-cycle. The source's stronger `strong_disproof` is retained:
there is a fixed positive rational gap, witnessed by `47/7056`, at arbitrarily
large orders. The proof uses graphs on `28m` vertices with part sizes
`4m, 7m, 7m, 10m`; they have `197m² − 5m` edges and `169m² − 5m` pentagonal edges.

`OnC5` requires five pairwise distinct vertices in cyclic adjacency, with the
specified unordered edge among the cycle edges. The retained `onC5_iff_cycle`
proves equivalence with Mathlib's `Walk.IsCycle` of length five.
The source's separate `literal_form_false` for the complete graph on three
vertices is also retained, but is not the proof used for the final theorem.
This does not formalize the sharp asymptotic constant `(2 + √2)/16` or the
matching lower bound of Grzesik, Hu, and Volec.

The construction is due to **Zoltán Füredi and Zeinab Maleki**, as described by
Andrzej Grzesik, Ping Hu, and Jan Volec in
[*Minimum number of edges that occur in odd cycles*](https://arxiv.org/abs/1605.09055).
The source uses a rational specialization of their template, which suffices
for a disproof without reproducing the optimal irrational proportions.

Both source commits explicitly name **Emerson Hsieh and Claude Fable 5** as
coauthors. The README explains that Claude agents wrote the Lean proofs in
Claude Code, while the human role covered target selection, statement sign-off,
audits, and publication. These roles are recorded without attributing a new
mathematical disproof to the formal authors.

## Provenance and port

No formalization link appeared in the two EPC comments inspected. The EPC
community database instead links this repository in `formal_status`, dated
29 July 2026; pull request 365 records the submission and methodology.

Pinned source revision: `b50849234b8de6cb5c642b5cb0479cab2e9e9908`.
The proof was introduced by `09834c8a966657bc38b8a4a8e15ea164601d28fe`;
the subsequent pinned commit only changes presentation.
The explicit toolchain is `leanprover/lean4:v4.27.0`, and Mathlib is pinned to
`a3a10db0e9d66acbebf76c5e6a135066525ac900` (4.27.0).
The Apache-2.0 license is preserved in the supporting directory.

The port rewrites imports, updates graph symmetry/irreflexivity wrappers and
Mathlib lemma names, namespaces the literal
sanity theorem, and exposes `not_erdos_608` without the `Conjecture` wrapper.
The independent Comparator challenge repeats only `OnC5`, `pentEdges`, and the
explicit asymptotic assertion. It imports no solution modules.

## Verification

- `lake build ErdosProblems.Erdos608 Erdos608` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has the expected
  placeholder warning.
- `not_erdos_608`, `strong_disproof`, and `onC5_iff_cycle` depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Independent `lean4export` exports of the final asymptotic disproof pass
  `Comparator.compareAt` and `Comparator.checkAxioms`; a fresh Lean environment
  accepts kernel replay of the exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS environment
  lacks `landrun`. Nanoda remains enabled in the Comparator configuration.
- Metadata, registrations, independent definitions and theorem statements,
  configuration consistency, and the absence of proof placeholders,
  `native_decide`, custom axioms, and unsafe declarations were checked.
