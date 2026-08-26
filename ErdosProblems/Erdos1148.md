# Erdős Problem 1148

This repository contains an **unconditional** proof of
[Erdős Problem 1148](https://www.erdosproblems.com/1148): every sufficiently
large integer `n` is `x² + y² - z²` for integers `x, y, z` with all three
squares at most `n`.

The final theorem `Erdos1148.erdos_1148` has no Duke hypothesis. Its
independent Comparator challenge states exactly that conclusion, without
the auxiliary discriminant definitions or any solution imports.

## Original formalization and authors

[Przemek Chojecki's comment of 17 March 2026](https://www.erdosproblems.com/1148#post-4849)
links a Lean editor formalization and explicitly says it assumes Duke's
theorem. That original result is retained here as `erdos_1148_of_duke`.
The compressed editor link is preserved as `PrzemekChojecki_1148` in
`data/urls.yaml`; it still matches the link in the EPC comment.

The informal argument is credited to **Przemek Chojecki and GPT-5.4 Pro**
in [his preceding comment](https://www.erdosproblems.com/1148#post-4822).
His formalization comment names **Gemini 3.1, Claude Opus 4.6, GPT-5.4,
and UlamAI Prover**. The formalization comment does not specify the Pro
variant of GPT-5.4, so the formal AI field uses its stated model name;
the informal AI field retains GPT-5.4 Pro. The
[paper](https://www.ulam.ai/research/erdos1148-full.pdf) is titled *Bounded
Representations by x² + y² − z²* and gives his name as Przemyslaw Chojecki.
The shorter name used on EPC is retained consistently in the metadata.

The original editor snippet contains no explicit license or toolchain
version, and its URL does not select a versioned Lean project. The paper
does not supply a Lean version either. The previous `4.27.0` metadata
could not be confirmed from those sources. This repository's earliest
version header, added on 12 May 2026, records its then-current port as
Lean/Mathlib 4.29.1; that is not evidence of the original editor version.

## Unconditional repository completion

The later commit
[`a6e8981de30fd4bc839c1c58d6f687c2f78449ed`, “Make Erdos1148 unconditional.”](https://github.com/plby/lean-proofs/commit/a6e8981de30fd4bc839c1c58d6f687c2f78449ed)
adds the packet, entropy, and full-support development that supplies
`unconditional_fixed_ball_existence`. The root theorem applies the
existing parity correction and representation argument to that result.
The complete development was already present before this import review;
it has not been replaced by the older conditional proof.

The completion's Git author is **Boris Alexeev**. Its source and commit do
not separately identify proof-writing tools; we do not infer additional
tool credits or attribute this later completion to the original EPC
authors. The `author` fields in `sources.yaml` describe the original
formalization, with this distinction recorded beside them.

The selected complete version is pinned to that repository commit and
**Lean/Mathlib 4.33.0**, which its toolchain explicitly records. The source
entry therefore uses `version: "4.33.0"` and no longer has a `conditional`
field. This does not assert that the original editor formalization was
unconditional or used Lean 4.33.0.

## Verification

The existing source and challenge pass
`lake build ErdosProblems.Erdos1148 Erdos1148`. The final theorem prints
only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The existing
469 support modules contain no `sorry`, custom axiom declarations, or
`native_decide`; their pre-existing style and deprecation warnings are
not being refactored in this metadata/provenance reconciliation.

After export with `lean4export`, Comparator's `compareAt` accepted the
unconditional theorem statement, and `checkAxioms` accepted it with only
those three permitted axioms. Replaying the exported solution declarations
in a fresh Lean kernel environment also succeeded. This reconciliation
changes no proof code or theorem statements.

The full Linux sandbox/Nanoda runner is unavailable on this host. The
checks above use the local Comparator APIs and Lean kernel; Nanoda
remains enabled in the existing configuration.

## Available versions

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos1148.lean), unconditional.
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos1148.lean), historical conditional version.
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos1148.lean), historical conditional version.
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos1148.lean), historical conditional version.
