/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sentence `Erdos501` translates to Flypitch's `Erdos501_f`

The Mathlib-side sentence `Erdos501.FOL.Erdos501` (Challenge / `Erdos501.FOL.Statement`) and the
Flypitch sentence `Flypitch.Erdos501.Erdos501_f` (`Flypitch4/Erdos501/Sentence.lean`) are built by
the same depth-polymorphic combinators; the translation `tr` maps one to the other *by
definitional unfolding* (`tr_Erdos501 : tr Erdos501 = Erdos501_f := rfl`).

The standard `L`-structure `zfsetStructure` on Mathlib's `ZFSet` is the translation of Flypitch's
`stdStructure`, so the faithfulness theorem `stdStructure_realize_Erdos501_f_iff` transfers.
-/
import ErdosProblems.Erdos501.FOL.Axioms
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Sentence
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Bridge

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol

namespace Erdos501.FOL

set_option maxRecDepth 100000 in
/-- The Mathlib-side sentence is the Flypitch sentence, symbol by symbol. -/
theorem tr_Erdos501 : tr Erdos501.FOL.Erdos501 = Flypitch.Erdos501.Erdos501_f := rfl

/-- The standard structure on `ZFSet` (Challenge) is the translation of Flypitch's standard
structure `stdStructure` (`Flypitch4/Erdos501/StdSemantics.lean`). -/
theorem zfsetStructure_eq_toM : zfsetStructure = toM Flypitch.Erdos501.stdStructure := by
  refine Structure.ext ?_ ?_
  · funext n f xs
    cases f <;> rfl
  · funext n r xs
    cases r
    rfl

/-- **Faithfulness**: `ZFSet.{0} ⊨ Erdos501` (with the standard interpretation) iff the
Mathlib-level statement of the first question of #501 (verbatim the proposition of
`formal-conjectures`' `erdos_501`, `Flypitch.Erdos501.erdos501_deepmind`) holds. -/
theorem realize_Erdos501_iff :
    (ZFSet.{0} ⊨ Erdos501.FOL.Erdos501) ↔ Flypitch.Erdos501.erdos501_deepmind := by
  rw [zfsetStructure_eq_toM]
  have h := realize_sentence_tr Flypitch.Erdos501.stdStructure Erdos501.FOL.Erdos501
  rw [tr_Erdos501] at h
  exact h.trans Flypitch.Erdos501.stdStructure_realize_Erdos501_f_iff

end Erdos501.FOL
