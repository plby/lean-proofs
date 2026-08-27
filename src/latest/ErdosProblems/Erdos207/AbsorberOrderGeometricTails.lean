/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGeometricCrudeTails
import ErdosProblems.Erdos207.AbsorberRootedGeometricTail
import ErdosProblems.Erdos207.AbsorberOrderClass
import ErdosProblems.Erdos207.GreedyCrudeFamilyMono

/-! # Geometric tails for the actual forbidden order classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedAbsorber_orderRooted_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B R : TripleSystemOn V)
    (q j c s : ℕ) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hR : R.card = 2) (hc : c + 5 ≤ j) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ c * ((boundedIntersectionMomentCoefficient c s : ℝ≥0) *
      ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5)))) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ ((greedyRootedConfigurationClass
        (forbiddenFamilyOfOrder F j) z.2 R c).card : ℝ≥0)) ≤ (1 / 2 : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hmono : L.probability (fun z ↦ K ≤ ((greedyRootedConfigurationClass
        (forbiddenFamilyOfOrder F j) z.2 R c).card : ℝ≥0)) ≤
      L.probability (fun z ↦ K ≤ ((greedyRootedConfigurationClass
        (absorberInducedConfigurationsOn q j B) z.2 R c).card : ℝ≥0)) := by
    apply L.probability_mono
    intro z hz
    apply hz.trans
    exact_mod_cast card_le_card (greedyRootedConfigurationClass_mono
      (forbiddenFamilyOfOrder_subset_absorberInduced hF (by omega)) z.2 R c)
  exact hmono.trans (timedStoppedAbsorber_rooted_geometricTail n F active D S₀ B R q j c s w K
    hInv₀ hchosen₀ hR hc hD hw hK hfloor hratio hcut)

theorem timedStoppedAbsorber_orderGainDefect_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q r c s : ℕ) (T : TripleOn V) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hc : c + 4 ≤ r) (hr : r ≤ q) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ (2 * q) * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) *
      (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4)))) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ (greedyActiveGainDefectCount (forbiddenFamilyOfOrder F r) F z.2 T c : ℝ≥0)) ≤
      (1 / 2 : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hmono : L.probability (fun z ↦ K ≤
      (greedyActiveGainDefectCount (forbiddenFamilyOfOrder F r) F z.2 T c : ℝ≥0)) ≤
      L.probability (fun z ↦ K ≤ (greedyActiveGainDefectCount
        (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B) z.2 T c : ℝ≥0)) := by
    apply L.probability_mono
    intro z hz
    apply hz.trans
    exact_mod_cast greedyActiveGainDefectCount_mono
      (forbiddenFamilyOfOrder_subset_absorberInduced hF (by omega))
      (fun E hE hc ↦ mem_absorberNontrivialInducedFamily_of_card_ge_two (hF hE) hc) z.2 T c
  exact hmono.trans (timedStoppedAbsorber_gainDefect_geometricTail n F active D S₀ B q r c s T w K
    hInv₀ hchosen₀ hc hr hD hw hK hfloor hratio hcut)

end

end Erdos207
