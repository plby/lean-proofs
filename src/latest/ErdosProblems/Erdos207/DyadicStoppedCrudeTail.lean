/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicCrudeCutoffs
import ErdosProblems.Erdos207.DyadicMomentFloor

/-! # The actual stopped crude-state tail with explicit integer floor and cutoffs -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem timedStoppedAbsorber_dyadic_crude_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (steps : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (bank : TripleSystemOn V) (q t a floorPower : ℕ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hN : 1 ≤ Fintype.card V) (ht : 32 ≤ t) (hsteps : steps ≤ Fintype.card V ^ 2)
    (hsize : 8 * t ^ floorPower ≤ Fintype.card V ^ 3)
    (hfloor : ∀ i S, active i S → dyadicMomentFloor (Fintype.card V) t floorPower ≤ S.available.card)
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hroot : (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q bank ≤ (t : ℝ≥0) ^ a)
    (hpair : (pairTwoAwayThreatExtensionCoefficient q bank : ℝ≥0) ≤ (t : ℝ≥0) ^ a)
    (hcommon : absorberCommonThreatWeightBound q bank ≤ (t : ℝ≥0) ^ a)
    (hgain : absorberGainDefectWeightBound q bank ≤ (t : ℝ≥0) ^ a) :
    (FiniteLaw.timedStoppedProcessLaw steps (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ CrudeStateBounds F z.2 q
        (dyadicCrudeThresholds V t (dyadicCrudeExponent q a (floorPower + 1)))) ≤
      4 * (q + 1 : ℝ≥0) ^ 2 * (Fintype.card V + 1 : ℝ≥0) ^ 6 * (1 / 2 : ℝ≥0) ^ t := by
  have hw : (1 : ℝ≥0) ≤ (t : ℝ≥0) ^ (floorPower + 1) := by
    exact_mod_cast Nat.one_le_pow (floorPower + 1) t (show 1 ≤ t by omega)
  exact timedStoppedAbsorber_crudeState_polynomial_geometricTail steps F active
    (dyadicMomentFloor (Fintype.card V) t floorPower) S₀ bank q t ((t : ℝ≥0) ^ (floorPower + 1))
    (dyadicCrudeThresholds V t (dyadicCrudeExponent q a (floorPower + 1)))
    hF hInv₀ hchosen₀ (dyadicMomentFloor_pos _ _ _ (by omega) hsize) hw hfloor
    (dyadicMomentFloor_joint_ratio _ _ _ _ hN ht hsteps hsize)
    (dyadicCrudeThresholds_geometric q t a (floorPower + 1) bank (by omega)
      hconst hroot hpair hcommon hgain)

end

end Erdos207
