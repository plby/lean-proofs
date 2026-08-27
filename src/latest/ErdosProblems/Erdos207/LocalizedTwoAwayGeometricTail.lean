/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayAbsorberWeight
import ErdosProblems.Erdos207.TimedStoppedBoundedMomentTail

/-! # Growing-moment localized two-away tails for the actual stopped greedy law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedAbsorber_localizedTwoAway_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (q s : ℕ)
    (H : SimpleGraph V) (B : TripleSystemOn V) (X U : Finset V)
    (T : TripleOn V) {a b : V} (hab : a ≠ b) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ q * ((boundedIntersectionMomentCoefficient q s : ℝ≥0) *
      localizedTwoAwayWeightBound q B U)) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ selectedCount
        (fun v : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder v) z.2.chosen) ≤
      (1 / 2 : ℝ≥0) ^ s := by
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀
    (fun v : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder v)
    (fun S ↦ selectedCount
      (fun v : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder v) S.chosen)
    q s (Fintype.card V + 1 : ℝ≥0)⁻¹ w (localizedTwoAwayWeightBound q B U) K
    hInv₀ hchosen₀ hD hw hK hfloor hratio (fun _ _ ↦ le_rfl)
    (localizedTwoAway_absorber_remainder_card_le hF)
    (localizedTwoAway_absorber_hasExtensionBound F hF T hab hsep hrootLocal) hcut

end

end Erdos207
