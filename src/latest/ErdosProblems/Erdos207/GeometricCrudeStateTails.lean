/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStatisticIndex

/-! # A simultaneous geometric tail for all crude statistics at one stopped time -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure GeometricCrudeCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    (q s : ℕ) (B : TripleSystemOn V) (w : ℝ≥0) (K : CrudeThresholds) : Prop where
  rooted_pos : ∀ i : CrudeOrderIndex q 5, 0 < K.rooted i.order i.chosen
  pair_pos : 0 < K.pair
  common_pos : 0 < K.common
  gain_pos : ∀ i : CrudeOrderIndex q 4, 0 < K.gain i.order i.chosen
  rooted_cut : ∀ i : CrudeOrderIndex q 5,
    2 * (w ^ i.chosen * ((boundedIntersectionMomentCoefficient i.chosen s : ℝ≥0) *
      ((2 : ℝ≥0) ^ (i.order - 2) * pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1 : ℝ≥0) ^ (i.order - i.chosen - 5)))) ≤ K.rooted i.order i.chosen
  pair_cut : 2 * (w ^ q * ((boundedIntersectionMomentCoefficient q s : ℝ≥0) *
    (pairTwoAwayThreatExtensionCoefficient q B : ℕ))) ≤ K.pair
  common_cut : 2 * (w ^ (2 * q) * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) *
    absorberCommonThreatWeightBound q B)) ≤ K.common
  gain_cut : ∀ i : CrudeOrderIndex q 4,
    2 * (w ^ (2 * q) * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) *
      (absorberGainDefectWeightBound q B *
        (Fintype.card V + 1 : ℝ≥0) ^ (i.order - i.chosen - 4)))) ≤ K.gain i.order i.chosen

theorem timedStoppedAbsorber_crudeStatistic_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (w : ℝ≥0) (K : CrudeThresholds)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : GeometricCrudeCutoffs q s B w K) (i : CrudeStatisticIndex V q) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ crudeThreshold K i ≤ crudeStatistic F z.2 i) ≤ (1 / 2 : ℝ≥0) ^ s := by
  rcases i with ⟨j, roots⟩ | i
  · exact timedStoppedAbsorber_orderRooted_geometricTail n F active D S₀ B
      {roots.1.1, roots.1.2} q j.order j.chosen s w (K.rooted j.order j.chosen)
      hF hInv₀ hchosen₀ (card_pair roots.2) j.budget hD hw (hcut.rooted_pos j)
      hfloor hratio (hcut.rooted_cut j)
  rcases i with ⟨T, P⟩ | i
  · exact timedStoppedAbsorber_pairSelected_geometricTail n F active D S₀ B q s T P w K.pair
      hF hInv₀ hchosen₀ hD hw hcut.pair_pos hfloor hratio hcut.pair_cut
  rcases i with ⟨T, T'⟩ | ⟨j, T⟩
  · exact timedStoppedAbsorber_commonThreatSelected_geometricTail n F active D S₀ B q s T T' w K.common
      hF hInv₀ hchosen₀ hD hw hcut.common_pos hfloor hratio hcut.common_cut
  · exact timedStoppedAbsorber_orderGainDefect_geometricTail n F active D S₀ B q j.order j.chosen s T w
      (K.gain j.order j.chosen) hF hInv₀ hchosen₀ j.budget j.order_le hD hw (hcut.gain_pos j)
      hfloor hratio (hcut.gain_cut j)

theorem timedStoppedAbsorber_crudeState_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (w : ℝ≥0) (K : CrudeThresholds)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : GeometricCrudeCutoffs q s B w K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ CrudeStateBounds F z.2 q K) ≤
        (Fintype.card (CrudeStatisticIndex V q) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ s := by
  classical
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hsum : (∑ i : CrudeStatisticIndex V q,
      L.probability (fun z ↦ crudeThreshold K i ≤ crudeStatistic F z.2 i)) ≤
      (Fintype.card (CrudeStatisticIndex V q) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ s := by
    calc
      _ ≤ ∑ _i : CrudeStatisticIndex V q, (1 / 2 : ℝ≥0) ^ s := by
        apply sum_le_sum
        intro i _
        exact timedStoppedAbsorber_crudeStatistic_geometricTail n F active D S₀ B q s w K
          hF hInv₀ hchosen₀ hD hw hfloor hratio hcut i
      _ = _ := by simp
  have h := (L.probability_exists_le (univ : Finset (CrudeStatisticIndex V q))
    (fun i z ↦ crudeThreshold K i ≤ crudeStatistic F z.2 i)).trans hsum
  simpa only [CrudeStateBounds, not_forall, not_lt, mem_univ, true_and] using h

theorem timedStoppedAbsorber_crudeState_polynomial_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (w : ℝ≥0) (K : CrudeThresholds)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : GeometricCrudeCutoffs q s B w K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ CrudeStateBounds F z.2 q K) ≤
        4 * (q + 1 : ℝ≥0) ^ 2 * (Fintype.card V + 1 : ℝ≥0) ^ 6 * (1 / 2 : ℝ≥0) ^ s := by
  refine (timedStoppedAbsorber_crudeState_geometricTail n F active D S₀ B q s w K
    hF hInv₀ hchosen₀ hD hw hfloor hratio hcut).trans ?_
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast card_crudeStatisticIndex_le_polynomial V q

end

end Erdos207
