/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationDrift
import ErdosProblems.Erdos207.GreedyConfigurationCardinality
import ErdosProblems.Erdos207.RestrictedThreatUnionBounds

/-! # Conditional configuration variance from the gain-plus-loss budget -/

namespace Erdos207

open Finset

noncomputable section

theorem sub_sq_le_bound_mul_add {g l M : ℝ}
    (hg0 : 0 ≤ g) (hl0 : 0 ≤ l) (hg : g ≤ M) (hl : l ≤ M) :
    (g - l) ^ 2 ≤ M * (g + l) := by
  have hgg := mul_le_mul_of_nonneg_right hg hg0
  have hll := mul_le_mul_of_nonneg_right hl hl0
  have hgl := mul_nonneg hg0 hl0
  nlinarith

theorem restrictedGreedyKernel_configuration_secondMoment_le_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c : ℕ) (M : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hgain : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      ((greedyConfigurationGains F J S root c T).card : ℝ) ≤ M)
    (hloss : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      ((greedyConfigurationLosses F J S root (c + 1) T).card : ℝ) ≤ M) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
        (greedyConfigurationClass J S root (c + 1)).card) ^ 2) ≤
      M * ((∑ C ∈ greedyConfigurationClass J S root c,
        ((greedyConfigurationGainSelectors F S root C).card : ℝ)) +
        ∑ C ∈ greedyConfigurationClass J S root (c + 1),
          ((greedyConfigurationLossSelectors F S root C).card : ℝ)) /
        (S.available \ greedyClosedThreats F S root).card := by
  let R := S.available \ greedyClosedThreats F S root
  have htransposeG : (∑ T ∈ R,
      ((greedyConfigurationGains F J S root c T).card : ℝ)) =
      ∑ C ∈ greedyConfigurationClass J S root c,
        ((greedyConfigurationGainSelectors F S root C).card : ℝ) := by
    exact_mod_cast sum_root_preserving_configuration_gains_eq (J := J) root c hS hroot
  have htransposeL : (∑ T ∈ R,
      ((greedyConfigurationLosses F J S root (c + 1) T).card : ℝ)) =
      ∑ C ∈ greedyConfigurationClass J S root (c + 1),
        ((greedyConfigurationLossSelectors F S root C).card : ℝ) := by
    exact_mod_cast sum_root_preserving_configuration_losses_eq (J := J) root (c + 1) hS
  rw [restrictedGreedyKernel_expectationReal]
  calc
    (R.card : ℝ)⁻¹ * (∑ T ∈ R,
        (((greedyConfigurationClass J (greedyStep F S T) root (c + 1)).card : ℝ) -
          (greedyConfigurationClass J S root (c + 1)).card) ^ 2) ≤
        (R.card : ℝ)⁻¹ * (∑ T ∈ R,
          M * ((greedyConfigurationGains F J S root c T).card +
            (greedyConfigurationLosses F J S root (c + 1) T).card)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply sum_le_sum
      intro T hT
      rw [greedyConfigurationClass_increment_succ c hS (mem_sdiff.mp hT).1]
      exact sub_sq_le_bound_mul_add (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (hgain T hT) (hloss T hT)
    _ = _ := by
      rw [← mul_sum, sum_add_distrib, htransposeG, htransposeL]
      ring

theorem sum_configurationGainSelectors_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hcard : ∀ C ∈ J, C.card = d + 1) :
    (∑ C ∈ greedyConfigurationClass J S root c,
      ((greedyConfigurationGainSelectors F S root C).card : ℝ)) ≤
      (greedyConfigurationClass J S root c).card * (d - c : ℕ) := by
  calc
    _ ≤ ∑ _C ∈ greedyConfigurationClass J S root c, ((d - c : ℕ) : ℝ) := by
      apply sum_le_sum
      intro C hC
      have hpart := greedyConfigurationGainSelectors_card_add_bad_eq hS hroot hC
        (hcard C (mem_greedyConfigurationClass.mp hC).1)
      exact_mod_cast (show (greedyConfigurationGainSelectors F S root C).card ≤ d - c by omega)
    _ = _ := by simp

theorem sum_configurationLossSelectors_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ} (H : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hcard : ∀ C ∈ J, C.card = d + 1)
    (hthreat : ∀ U ∈ S.available, ((greedyClosedThreats F S U).card : ℝ) ≤ H) :
    (∑ C ∈ greedyConfigurationClass J S root c,
      ((greedyConfigurationLossSelectors F S root C).card : ℝ)) ≤
      (greedyConfigurationClass J S root c).card * ((d - c : ℕ) * H) := by
  calc
    _ ≤ ∑ _C ∈ greedyConfigurationClass J S root c, ((d - c : ℕ) * H) := by
      apply sum_le_sum
      intro C hC
      have hccard := greedyConfigurationClass_available_nonroot_card hS hroot hC
        (hcard C (mem_greedyConfigurationClass.mp hC).1)
      calc
        ((greedyConfigurationLossSelectors F S root C).card : ℝ) ≤
            ∑ U ∈ (C ∩ S.available).erase root,
              ((greedyClosedThreats F S U).card : ℝ) := by
          exact_mod_cast card_restricted_biUnion_le_sum_card ((C ∩ S.available).erase root)
            (greedyClosedThreats F S) (greedyClosedThreats F S root)
        _ ≤ ∑ _U ∈ (C ∩ S.available).erase root, H := by
          apply sum_le_sum
          intro U hU
          exact hthreat U (mem_inter.mp (mem_erase.mp hU).2).2
        _ = _ := by simp [hccard]
    _ = _ := by simp

theorem restrictedGreedyKernel_configuration_secondMoment_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c d : ℕ) (M H : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ C ∈ J, C.card = d + 1) (hM : 0 ≤ M)
    (hthreat : ∀ U ∈ S.available, ((greedyClosedThreats F S U).card : ℝ) ≤ H)
    (hgain : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      ((greedyConfigurationGains F J S root c T).card : ℝ) ≤ M)
    (hloss : ∀ T ∈ S.available \ greedyClosedThreats F S root,
      ((greedyConfigurationLosses F J S root (c + 1) T).card : ℝ) ≤ M) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
        (greedyConfigurationClass J S root (c + 1)).card) ^ 2) ≤
      M * ((greedyConfigurationClass J S root c).card * (d - c : ℕ) +
        (greedyConfigurationClass J S root (c + 1)).card * ((d - (c + 1) : ℕ) * H)) /
        (S.available \ greedyClosedThreats F S root).card := by
  refine (restrictedGreedyKernel_configuration_secondMoment_le_budget root c M hS hroot hR
    hgain hloss).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hM
  exact add_le_add (sum_configurationGainSelectors_le hS hroot hcard)
    (sum_configurationLossSelectors_le H hS hroot hcard hthreat)

end

end Erdos207
