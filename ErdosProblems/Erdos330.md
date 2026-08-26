# Erdős Problem 330

[EPC](https://www.erdosproblems.com/330) ·
[formalization announcement](https://www.erdosproblems.com/forum/thread/330#post-6271) ·
[source](https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330)

## Statement and authors

This formalizes the **positive upper density** version: there is an exact
order-two asymptotic basis `A` with positive upper density such that, for each
`a ∈ A`, the sums that lose all representations after deleting `a` also have
positive upper density. The two summands may be equal. This is not a claim of
positive lower density or the existence of natural density.

The informal proof is by GPT-5.5 Pro, prompted by David Turturean
([announcement](https://www.erdosproblems.com/forum/thread/330#post-5756)).
Allen Graham Hart reports using GPT-5.5 Pro to prepare a formalization plan and
Codex to carry it out with him in the loop. His full name appears in the
repository's `erdosproblems-330-upper-density/task.toml` author field.
The underlying model used by Codex is not specified.

## Provenance

The complete-proof revision is `6160036caab0dcee80395ba3beb7b6ef2731604e` (5 May 2026).
The 21 Lean modules are unchanged in the repository snapshot inspected later;
only the README and formalization notes changed.
Both Lean and Mathlib are pinned to **4.27.0**, with Mathlib revision
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.
The task metadata additionally records Formal Conjectures revision
`233a10e857ef78e79fd9fe661d37db724089170a`.

No explicit license was found for the standalone construction. The reused
`Util.Density` definitions retain their existing Formal Conjectures author and
Apache 2.0 notices; their independent challenge copies preserve that notice.

## Port and verification

The construction is imported into `ErdosProblems/Erdos330/`, with the final
`Erdos330.erdos_330` in the main file. The redundant proposition wrappers are
inlined in the final statement. The blanket `noncomputable section` was removed.
The port uses the current interval-cardinality and set-membership lemmas,
makes a modular congruence conversion explicit, and updates proof-local instance
bindings and redundant tactics for the current linters. The density definitions in `Util.Density` are
byte-identical to those at the pinned Formal Conjectures revision.

`lake build ErdosProblems.Erdos330 Erdos330` passes with no solution warnings.
`#print axioms Erdos330.erdos_330` reports only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry` or `native_decide` occurs in the solution.

The independently exported challenge and solution pass `Comparator.compareAt`,
`Comparator.checkAxioms`, and Lean's `Environment.replay` kernel check.
The full sandboxed Comparator runner and Nanoda were **not** run because this
macOS environment lacks the required Linux `landrun` sandbox.
