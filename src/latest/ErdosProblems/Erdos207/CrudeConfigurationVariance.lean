/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeConfigurationJumps
import ErdosProblems.Erdos207.GreedyConfigurationVariance
import ErdosProblems.Erdos207.PairStarJumpVariance

/-! # The full configuration variance bounds, including the zero-chosen class -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem restrictedGreedyKernel_configuration_zero_secondMoment_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (d : ℕ) (M H : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ C ∈ J, C.card = d + 1) (hM : 0 ≤ M)
    (hthreat : ∀ U ∈ S.available, ((greedyClosedThreats F S U).card : ℝ) ≤ H)
    (hloss : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      ((greedyConfigurationLosses F J S root 0 T).card : ℝ) ≤ M) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass J S' root 0).card : ℝ) -
        (greedyConfigurationClass J S root 0).card) ^ 2) ≤
      M * ((greedyConfigurationClass J S root 0).card * ((d : ℝ) * H)) /
        (S.available \ greedyClosedThreats F S root).card := by
  have hjump : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      -M ≤ ((greedyConfigurationClass J (greedyStep F S T) root 0).card : ℝ) -
        (greedyConfigurationClass J S root 0).card ∧
      ((greedyConfigurationClass J (greedyStep F S T) root 0).card : ℝ) -
        (greedyConfigurationClass J S root 0).card ≤ 0 := by
    intro T hT
    rw [greedyConfigurationClass_increment_zero hS (mem_sdiff.mp hT).1]
    exact ⟨neg_le_neg (hloss T hT), neg_nonpos.mpr (Nat.cast_nonneg _)⟩
  have hb := restrictedGreedyKernel_secondMoment_le_negative_mean F S _ hR
    (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
      (greedyConfigurationClass J S root 0).card) M hjump
  have hsum := sum_configurationLossSelectors_le (J := J) (c := 0) H hS hroot hcard hthreat
  simp only [Nat.sub_zero] at hsum
  calc
    _ ≤ M * (-(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
          (greedyConfigurationClass J S root 0).card)) := hb
    _ = M * (∑ C ∈ greedyConfigurationClass J S root 0,
        ((greedyConfigurationLossSelectors F S root C).card : ℝ)) /
        (S.available \ greedyClosedThreats F S root).card := by
      rw [restrictedGreedyKernel_configuration_drift_zero root hS hR]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hM) (Nat.cast_nonneg _)

namespace CrudeStateBounds

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}

theorem configuration_succ_variance
    (h : CrudeStateBounds F S q K) (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root : TripleOn V} (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hthreat : ∀ T ∈ S.available, ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    let M : ℝ := max (K.rooted j c : ℝ) (crudeConfigurationLossCutoff K H j (c + 1) : ℝ)
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S' root (c + 1)).card : ℝ) -
        (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card) ^ 2) ≤
      M * ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card * (j - 3 - c : ℕ) +
        (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card *
          ((j - 3 - (c + 1) : ℕ) * (H : ℝ))) / (S.available \ greedyClosedThreats F S root).card := by
  dsimp only
  apply restrictedGreedyKernel_configuration_secondMoment_le root c (j - 3) _ H hS hroot hR
  · intro E hE
    have hh := (mem_forbiddenFamilyOfOrder.mp hE).2
    omega
  · positivity
  · intro T hT
    exact_mod_cast hthreat T hT
  · intro T hT
    have hg : ((greedyConfigurationGains F (forbiddenFamilyOfOrder F j) S root c T).card : ℝ) ≤ K.rooted j c := by
      exact_mod_cast h.configuration_gain j c hj hc hroot hT
    exact hg.trans (le_max_left _ _)
  · intro T hT
    have hl : ((greedyConfigurationLosses F (forbiddenFamilyOfOrder F j) S root (c + 1) T).card : ℝ) ≤
        crudeConfigurationLossCutoff K H j (c + 1) := by
      exact_mod_cast h.configuration_loss j (c + 1) hj (by omega) H hS hpack hroot hT
        (hthreat T (mem_sdiff.mp hT).1)
    exact hl.trans (le_max_right _ _)

theorem configuration_zero_variance
    (h : CrudeStateBounds F S q K) (j : ℕ) (hj : j ≤ q) (hc : 4 ≤ j)
    (H : ℝ≥0) (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {root : TripleOn V} (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hthreat : ∀ T ∈ S.available, ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S' root 0).card : ℝ) -
        (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card) ^ 2) ≤
      (crudeConfigurationLossCutoff K H j 0 : ℝ) *
        ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card * ((j - 3 : ℕ) * (H : ℝ))) /
          (S.available \ greedyClosedThreats F S root).card := by
  apply restrictedGreedyKernel_configuration_zero_secondMoment_le root (j - 3) _ H hS hroot hR
  · intro E hE
    have hh := (mem_forbiddenFamilyOfOrder.mp hE).2
    omega
  · positivity
  · intro T hT
    exact_mod_cast hthreat T hT
  · intro T hT
    exact_mod_cast h.configuration_loss j 0 hj hc H hS hpack hroot hT (hthreat T (mem_sdiff.mp hT).1)

end CrudeStateBounds

end

end Erdos207
