/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.Ladder

/-!
# The bounded cardinality of strict-prior ladder records

This unchanged cardinal argument is extracted from GroundingLemma727Inputs
so it is available independently of the historical obstruction-theorem
import branch. Its statement requires neither legality nor any marker rule.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Fewer than `kappa` paths have been recorded strictly before any one
stage. The recording stage is an injective rank into that bounded segment. -/
theorem mk_recordedBefore_lt (L : Gamma.KappaLadder kappa) (a : Stage kappa) :
    #(L.bookkeeping.recordedBefore a) < kappa := by
  classical
  let stageWitness : ∀ p : L.bookkeeping.recordedBefore a,
      ∃ b : Stage kappa, b < a ∧ L.chosen b = some p.1 := fun p ↦ p.2
  let recordStage : L.bookkeeping.recordedBefore a → Stage kappa :=
    fun p ↦ Classical.choose (stageWitness p)
  have hrecordStage : Function.Injective recordStage := by
    intro p q hpq
    apply Subtype.ext
    have hp := (Classical.choose_spec (stageWitness p)).2
    have hq := (Classical.choose_spec (stageWitness q)).2
    rw [show Classical.choose (stageWitness p) =
      Classical.choose (stageWitness q) by exact hpq] at hp
    exact Option.some.inj (hp.symm.trans hq)
  exact RegularCardinal.mk_lt_of_injective_bounded_stage
    a recordStage hrecordStage
      (fun p ↦ (Classical.choose_spec (stageWitness p)).1)

#print axioms mk_recordedBefore_lt

end Erdos599.DWeb.KappaLadder
