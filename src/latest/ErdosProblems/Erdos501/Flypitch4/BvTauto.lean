
set_option relaxedAutoImplicit true
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bv_tauto.lean (deferred) -/

/-! # Deferred: tactic-only file

The Lean 3 `src/bv_tauto.lean` (94 lines) consists of:

- One regular lemma `context_or_elim'` — used only by Lean 3
  `to_mathlib.lean`'s `tactic.interactive` block (itself deferred).
- Nine `meta def` tactics: `context_switch`, `bv_or_elim`, `auto_or_elim_aux`,
  `auto_or_elim_step`, `goal_is_bv_false`, `bv_tauto_step`, `bv_tauto`, plus
  internal helpers.

Cross-flypitch grep:
  - `bv_tauto` tactic — 10 call sites across `src/bvm.lean`, `src/bvm_extras.lean`.
  - `bv_or_elim` tactic — 73 call sites across `src/bvm.lean`, `src/bvm_extras.lean`.
  - `context_or_elim'` lemma — 0 call sites once `to_mathlib.lean`'s tactic
    block is also deferred.

Lean 4 has a different tactic framework (macros/elaborators rather than
`meta def`). Porting these tactics is non-trivial and high-risk for mechanical
translation. Strategy: **defer until porting `bvm.lean` / `bvm_extras.lean`,
then either port the tactics in `BvTauto.lean` at that time, or rewrite each
call site as an explicit `by …` block in the consuming file** — whichever is
cheaper given the patterns that show up.
-/
