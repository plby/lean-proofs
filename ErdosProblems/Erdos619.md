# Erdős Problem 619

[EPC](https://www.erdosproblems.com/619) ·
[formalization comment](https://www.erdosproblems.com/619#post-6986) ·
[pinned source](https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f)

## Statement and scope

`Erdos619.not_erdos_619` disproves the existence of a constant `c > 0` such that
every finite connected triangle-free graph on `n` vertices can be made to have
diameter at most four, while remaining triangle-free, by adding fewer than
`(1 - c)n` edges. The final statement quantifies over arbitrary finite vertex
types and uses the minimum added-edge count `minNewEdges`.

The source's stronger `counterexample_family` is retained: for every
`0 < η < 1`, all sufficiently large orders admit a connected triangle-free
graph with minimum added-edge count at least `(1 - η)n`. The proof constructs
sparse cores with small independence number by finite counting, connects them,
and attaches pendant vertices. It includes the graph-existence argument and
does not assume a probabilistic existence theorem as an extra axiom.

The definition uses extended diameter and **at most four**, as clarified in
[EPC comment 6052](https://www.erdosproblems.com/619#post-6052). Disconnected
supergraphs cannot qualify through the ordinary diameter's junk value.
Although `Nat.sInf` of the empty set is zero, each counterexample comes with
an attained minimum, through the source's `IsHR` predicate and an explicit
feasible supergraph. The proof therefore does not exploit an empty infimum.

This import does not claim Thomas Bloom's subsequent optimized error term
`O(n^(8/9)(log n)^(2/9))` from EPC comment 6995.

## Authorship and provenance

The EPC comment and source README credit **Claude Fable 5** with the informal
disproof and formalization guidance, and **GPT-5.5 with Codex** with implementing
the Lean proof. **Nick Kuhn**, named Nikolas Kuhn in the Git history, is recorded
as the human contributor and publisher. This does not attribute the AI-written
proof to him as its sole mathematical or Lean author.

The source revision is `7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f`.
Its toolchain is explicitly `leanprover/lean4:v4.28.0`; Mathlib is pinned to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`v4.28.0`).
No license was supplied for the standalone proof repository.

The `minNewEdges` definition comes from Formal Conjectures, revision
`1a9fbeebaa628fec9818216802298871c95b193c`, introduced through
[PR 4255](https://github.com/google-deepmind/formal-conjectures/pull/4255).
Its Apache-2.0 copyright and license notice are preserved in both copies.

## Port and Comparator

The proof is split into `Basic`, `Seed`, `Host`, and `Pendant`, with the
Formal Conjectures definition in `Statement`. The main file retains the bridge
between the source's attained-minimum predicate and `minNewEdges`, and states
the final negation explicitly without a conclusion wrapper.

The independent Comparator challenge imports only Mathlib and repeats only
`minNewEdges` and the final theorem. It imports no solution modules.

The 4.33 port updates unordered-pair constructors, graph symmetry structures,
and clique containment through graph copies. It makes required classical
instances local, marks individual finite-set constructions noncomputable,
removes an unused root parameter, updates deprecated extended-natural lemmas,
and makes several definition unfoldings explicit. Proof modules retain Lean's
compatibility options for backward elaboration; the challenge has no options.

## Verification

- `lake build ErdosProblems.Erdos619 Erdos619` passes on Lean/Mathlib 4.33.0.
  The solution modules emit no warnings; the independent challenge has its
  expected placeholder warning.
- Both `not_erdos_619` and `counterexample_family` depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Separate challenge and solution exports pass `Comparator.compareAt` and
  `Comparator.checkAxioms`; a fresh Lean environment accepts kernel replay of
  the exported solution. Comparator covers the final disproof; the stronger
  counterexample-family theorem is built and separately axiom-audited.
- The full Linux sandbox/Nanoda runner is unavailable in this macOS environment
  because `landrun` is missing. Nanoda remains enabled in the configuration.
- Metadata, registrations, independent definitions, configuration consistency,
  and the absence of proof placeholders, `native_decide`, custom axioms, and
  unsafe declarations were checked.
