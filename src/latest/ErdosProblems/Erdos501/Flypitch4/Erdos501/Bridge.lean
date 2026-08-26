/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The bridge between `Erdos501_f` and DeepMind's `erdos_501`: the standard structure.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RealsInZFSet
import ErdosProblems.Erdos501.Flypitch4.Erdos501.ZFSetCOF

set_option relaxedAutoImplicit true

/-!
# The intended meaning of `Erdos501_f`

`Erdos501_f` (`Sentence.lean`) is meant to be the first-order rendering of the proposition
`erdos501_deepmind` (`StdSemantics.lean`), which is (verbatim) the right-hand side of the theorem
`erdos_501` in DeepMind's `formal-conjectures` (`FormalConjectures/ErdosProblems/501.lean`).

This file makes the intended meaning precise as a Lean theorem: Mathlib's `ZFSet` (the
Lean-internal model of `ZFC`) is an `L_ZFC`-structure `stdStructure` (`StdSemantics.lean`), and the
*specification* of the rendering,

    stdStructure ⊨ₘ Erdos501_f ↔ erdos501_deepmind        (`stdStructure_realize_Erdos501_f_iff`)

holds: in the standard model, the sentence is true iff the DeepMind proposition holds.  The proof
combines

* the two-valued unfolding `realize_Erdos501_f_std : (stdStructure ⊨ₘ Erdos501_f) ↔ StdSem.erdos501`
  (`StdSemantics.lean`);
* `RealsInZFSet.erdos501_deepmind_of_std`: `ℝ` is coded as a complete ordered field
  `(Rz, plusZ, timesZ, ltZ, zeroZ, oneZ)` inside `ZFSet`, and the Erdős property for it is DeepMind's
  proposition (with the covering lemma `exists_cover_of_volume_lt_one` for the outer-measure
  hypothesis);
* `ZFSetCOF.erdos501_std_of_deepmind`: every complete ordered field inside `ZFSet` is order-isomorphic
  to `ℝ` (Mathlib's uniqueness theorem for conditionally complete linear ordered fields, applied to
  the instances built on `ZFSetCOF.COF.Carrier`), and the Erdős property transports along the
  isomorphism.

It is *not* needed for the forcing results of `Main.lean`; it is the formal certificate of the
faithfulness of `Erdos501_f` (see also `validation/Erdos501Print.lean`).
-/

open Fol

namespace Flypitch.Erdos501

/-- **Specification of the rendering**: in the standard model `ZFSet`, the sentence `Erdos501_f`
holds if and only if the DeepMind proposition `erdos501_deepmind` holds. -/
theorem stdStructure_realize_Erdos501_f_iff :
    stdStructure ⊨ₘ Erdos501_f ↔ erdos501_deepmind := by
  rw [realize_Erdos501_f_std]
  exact ⟨RealsInZFSet.erdos501_deepmind_of_std, ZFSetCOF.erdos501_std_of_deepmind⟩

end Flypitch.Erdos501
