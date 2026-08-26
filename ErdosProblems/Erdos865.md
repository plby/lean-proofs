# Erdős Problem 865

[EPC](https://www.erdosproblems.com/865) ·
[complete formalization comment](https://www.erdosproblems.com/865#post-7378) ·
[pinned source](https://github.com/mrricky22/erdos-865-lean/tree/54bfae36c1b0384737bc23b18180bdf001816c5d) ·
[paper](https://arxiv.org/abs/2606.29361)

## Statement and authorship

`Erdos865.erdos_865` proves that there is an absolute positive real constant
`C` such that every `A ⊆ {1, …, N}` with `|A| ≥ 5N/8 + C` contains three
distinct elements `a, b, c` whose three pairwise sums also belong to `A`.
It holds for every natural `N`, not just sufficiently large `N`.
The port chooses `C = 7` from the source's stronger explicit bound
`8|A| ≤ 5N + 53` for triple-free sets.

The imported `sharpness` theorem constructs triple-free sets of size
`5M + 2` inside `{1, …, 8M}` for every `M ≥ 1`, so the leading constant
`5/8` cannot be reduced. No optimal additive constant is claimed.

The paper attributes the mathematical findings and proof strategy to
**Ricky Cipollini** together with **GPT-5.5 Pro**. Its acknowledgements credit
**Stijn Cambie** for feedback and improvements, not for writing the Lean proof.
**Aristotle** generated the formalization, submitted and published by
**Ricky Cipollini** (`rickyc` on EPC, `mrricky22` on GitHub). The human formal
credit in the metadata records that role, rather than implying sole manual
authorship of the proof.

## Versions and source selection

The selected repository snapshot is
`54bfae36c1b0384737bc23b18180bdf001816c5d`. The complete proof was uploaded
on 6 July 2026; the snapshot adds the Apache 2.0 license on 25 July.
The upstream `lean-toolchain` explicitly specifies
`leanprover/lean4:v4.28.0`; `lakefile.toml` requests Mathlib `v4.28.0`, and
`lake-manifest.json` pins it to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

EPC's earlier June formalization assumed a coarse theorem. The 6 July
comment and the selected source replace that input with a strong induction
argument. This is the complete version. The arXiv v1 discussion of an
outdated conditional formalization predates this July update.

The original Apache 2.0 license is included in `Erdos865/LICENSE`.
The source supplies no named copyright notice; none has been invented.

## Port and Comparator

The original module structure is retained under `ErdosProblems.Erdos865`:
`Defs`, `FoldedAux`, `FoldedMain`, `Folding`, `UpperBound`, and `Sharpness`.
The root file assembles the proof and states the positive answer directly.
The independent Comparator challenge imports only Mathlib, repeats the
pairwise-sum-triple predicate, and states the same final theorem.

The port replaces ambiguous conversions with explicit finite-set cardinality
arguments over `ZMod`, and uses injectivity on the relevant interval to
transport intersections through reflection. Unused hypotheses and simp
arguments are removed without weakening the final result.

## Verification

- `lake build ErdosProblems.Erdos865 Erdos865` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has its expected
  placeholder warning.
- `erdos_865` and `sharpness` depend only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- Independent exports of `erdos_865` pass `Comparator.compareAt` and
  `Comparator.checkAxioms`; a fresh Lean environment accepts kernel replay
  of the exported solution.
- The full Linux sandbox/Nanoda runner is unavailable because this macOS
  environment lacks `landrun`. Nanoda remains enabled in the configuration.
- Metadata, unique registrations, configuration consistency, and the absence
  of solution placeholders, `native_decide`, custom axioms, unsafe declarations,
  `run_cmd`, and file/process IO have been checked.
