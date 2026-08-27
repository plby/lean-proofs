/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedBoundedMomentTail
import ErdosProblems.Erdos207.AbsorberPairSelectedWeight
import ErdosProblems.Erdos207.AbsorberNontrivialFamily
import ErdosProblems.Erdos207.AbsorberGainDefectFamily
import ErdosProblems.Erdos207.GreedyGainDefectPairs

/-! # Source-strength geometric tails for the two-configuration crude statistics -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedAbsorber_pairSelected_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T : TripleOn V) (P : PairOn V) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ q * ((boundedIntersectionMomentCoefficient q s : ℝ≥0) *
      (pairTwoAwayThreatExtensionCoefficient q B : ℕ))) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦
        pairTwoAwayThreatRemainder u) z.2.chosen) ≤ (1 / 2 : ℝ≥0) ^ s := by
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀
    (fun u : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder u)
    (fun S ↦ selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦
      pairTwoAwayThreatRemainder u) S.chosen) q s (Fintype.card V + 1 : ℝ≥0)⁻¹ w
    (pairTwoAwayThreatExtensionCoefficient q B : ℕ) K hInv₀ hchosen₀ hD hw hK hfloor hratio
    (fun _ _ ↦ le_rfl) (absorberForbiddenPairThreat_remainder_card_le q B F T P hF)
    (absorberForbiddenPairThreat_hasExtensionBound q B F T P hF) hcut

theorem timedStoppedAbsorber_commonThreatSelected_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T T' : TripleOn V) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ (2 * q) * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) *
      absorberCommonThreatWeightBound q B)) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) z.2.chosen) ≤
      (1 / 2 : ℝ≥0) ^ s := by
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀
    (fun u : CommonThreatWitness F F T T' ↦ u.remainder)
    (fun S ↦ selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) S.chosen)
    (2 * q) s (Fintype.card V + 1 : ℝ≥0)⁻¹ w (absorberCommonThreatWeightBound q B) K
    hInv₀ hchosen₀ hD hw hK hfloor hratio (fun _ _ ↦ le_rfl)
    (absorberForbiddenCommonThreat_remainder_card_le q B F T T' hF)
    (absorberForbiddenCommonThreat_hasExtensionBound q B F T T' hF) hcut

theorem timedStoppedAbsorber_gainDefect_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q r c s : ℕ) (T : TripleOn V) (w K : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hc : c + 4 ≤ r) (hr : r ≤ q) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ (2 * q) * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) *
      (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4)))) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ (greedyActiveGainDefectCount
        (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B) z.2 T c : ℝ≥0)) ≤
      (1 / 2 : ℝ≥0) ^ s := by
  let J := absorberInducedConfigurationsOn q r B
  let G := absorberNontrivialInducedFamily q B
  let rem := fun u : GainDefectWitness J G T (r - 2 - c - 1) ↦ u.remainder
  have hk : HasExtensionBound rem (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
      (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4)) := by
    have he : r - 2 - c - 1 - 1 = r - c - 4 := by omega
    simpa only [he] using absorberGainDefect_hasExtensionBound q r (r - 2 - c - 1) B T
      (by omega) hr (by omega)
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀ rem
    (fun S ↦ (greedyActiveGainDefectCount J G S T c : ℝ≥0)) (2 * q) s
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w
    (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4)) K
    hInv₀ hchosen₀ hD hw hK hfloor hratio
    (fun S hS ↦ greedyActiveGainDefectCount_le_selectedCount J G S T c (r - 2) hS
      absorberInducedConfigurationsOn_fixed_card)
    (absorberGainDefect_remainder_card_le q r (r - 2 - c - 1) B T hr) hk hcut

end

end Erdos207
