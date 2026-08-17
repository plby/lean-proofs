/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.BlockCRTBridge
import ErdosProblems.Erdos144.HarmonicSubtype
import ErdosProblems.Erdos144.PrimeTransfer

/-!
# Identifying the prime-transfer good mass with harmonic probability

This file joins the subtype-indexed CRT good event to the equal-subsum event
in the harmonic model.
-/

open scoped BigOperators

namespace Erdos144.TransferBridge

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The harmonic good-event mass used by the prime-block transfer is exactly
the harmonic probability of the bounded equal-subsum event. -/
theorem harmonicSubtypeGoodMass_eq_prob (I : Finset ℕ) (L : ℕ) :
    PrimeTransfer.harmonicSubtypeGoodMass I L =
      HarmonicProb.prob I
        (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ L) := by
  rw [HarmonicSubtype.boundedEqualSubsum_prob_eq_subtype_sum]
  unfold PrimeTransfer.harmonicSubtypeGoodMass
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    exact BlockCRTBridge.blockGood_subtype_iff T L
  · intro T _hT
    rfl

end

end Erdos144.TransferBridge
