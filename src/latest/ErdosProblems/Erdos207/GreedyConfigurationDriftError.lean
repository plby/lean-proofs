/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationDrift
import ErdosProblems.Erdos207.GreedyConfigurationLossBound
import ErdosProblems.Erdos207.ConfigurationGainDefectWitness
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Quantitative configuration drift from threat and redundant-witness bounds -/

namespace Erdos207

open Finset

noncomputable section

theorem sum_configurationLossSelectors_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d K : ℕ} (H epsilon : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hcard : ∀ C ∈ J, C.card = d + 1)
    (hpack : ∀ C ∈ J, IsPackingOn C)
    (hinter : ∀ U ∈ S.available, ∀ W ∈ S.available, U ≠ W →
      (U.1 ∩ W.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (htrajectory : ∀ U ∈ S.available,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilon) :
    |(∑ C ∈ greedyConfigurationClass J S root c,
        ((greedyConfigurationLossSelectors F S root C).card : ℝ)) -
      (greedyConfigurationClass J S root c).card * ((d - c : ℕ) * H)| ≤
      (greedyConfigurationClass J S root c).card *
        ((d - c : ℕ) * epsilon + (((d - c) + (d - c).choose 2) * K : ℕ)) := by
  have hbound := abs_sum_sub_card_mul_le_sum_error
    (greedyConfigurationClass J S root c)
    (fun C ↦ ((greedyConfigurationLossSelectors F S root C).card : ℝ))
    (fun _ ↦ (d - c : ℕ) * epsilon + (((d - c) + (d - c).choose 2) * K : ℕ))
    ((d - c : ℕ) * H) (fun C hC ↦ ?_)
  · simpa only [sum_const, nsmul_eq_mul] using hbound
  · apply greedyConfigurationLossSelectors_trajectory_error H epsilon hS hroot hC
      (hcard C (mem_greedyConfigurationClass.mp hC).1)
    · intro U hU
      exact hinter U (mem_inter.mp (mem_erase.mp hU).2).2 root hroot
        (mem_erase.mp hU).1
        ((hpack C (mem_greedyConfigurationClass.mp hC).1).inter_card_le_one
          (mem_inter.mp (mem_erase.mp hU).2).1
          (mem_greedyConfigurationClass.mp hC).2.1 (mem_erase.mp hU).1)
    · intro U hU W hW hUW
      exact hinter U (mem_inter.mp (mem_erase.mp hU).2).2
        W (mem_inter.mp (mem_erase.mp hW).2).2 hUW
        ((hpack C (mem_greedyConfigurationClass.mp hC).1).inter_card_le_one
          (mem_inter.mp (mem_erase.mp hU).2).1
          (mem_inter.mp (mem_erase.mp hW).2).1 hUW)
    · intro U hU
      exact htrajectory U (mem_inter.mp (mem_erase.mp hU).2).2

theorem sum_configurationGainSelectors_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d : ℕ}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hcard : ∀ C ∈ J, C.card = d + 1)
    (hpack : ∀ C ∈ J, IsPackingOn C) (hcd : c + 2 ≤ d) :
    |(∑ C ∈ greedyConfigurationClass J S root c,
        ((greedyConfigurationGainSelectors F S root C).card : ℝ)) -
      (greedyConfigurationClass J S root c).card * (d - c : ℕ)| ≤
      2 * ∑ C ∈ greedyConfigurationClass J S root c,
        ((greedyConfigurationRedundantWitnesses F S C).card : ℝ) := by
  have hbound := abs_sum_sub_card_mul_le_sum_error
    (greedyConfigurationClass J S root c)
    (fun C ↦ ((greedyConfigurationGainSelectors F S root C).card : ℝ))
    (fun C ↦ 2 * (greedyConfigurationRedundantWitnesses F S C).card)
    (d - c : ℕ) (fun C hC ↦
      greedyConfigurationGainSelectors_trajectory_error hS hroot
        (hpack C (mem_greedyConfigurationClass.mp hC).1) hC
        (hcard C (mem_greedyConfigurationClass.mp hC).1) hcd)
  simpa only [mul_sum] using hbound

theorem restrictedGreedyKernel_configuration_drift_succ_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c d K : ℕ) (H epsilon : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ C ∈ J, C.card = d + 1)
    (hpack : ∀ C ∈ J, IsPackingOn C) (hcd : c + 2 ≤ d)
    (hinter : ∀ U ∈ S.available, ∀ W ∈ S.available, U ≠ W →
      (U.1 ∩ W.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (htrajectory : ∀ U ∈ S.available,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilon) :
    |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
          (greedyConfigurationClass J S root (c + 1)).card) -
      ((greedyConfigurationClass J S root c).card * (d - c : ℕ) -
        (greedyConfigurationClass J S root (c + 1)).card * ((d - (c + 1) : ℕ) * H)) /
          (S.available \ greedyClosedThreats F S root).card| ≤
      (2 * (∑ C ∈ greedyConfigurationClass J S root c,
          ((greedyConfigurationRedundantWitnesses F S C).card : ℝ)) +
        (greedyConfigurationClass J S root (c + 1)).card *
          ((d - (c + 1) : ℕ) * epsilon +
            (((d - (c + 1)) + (d - (c + 1)).choose 2) * K : ℕ))) /
        (S.available \ greedyClosedThreats F S root).card := by
  rw [restrictedGreedyKernel_configuration_drift_succ root c hS hroot hR,
    ← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (S.available \ greedyClosedThreats F S root).card :
      (0 : ℝ) ≤ (S.available \ greedyClosedThreats F S root).card)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact abs_difference_error_le
    (sum_configurationGainSelectors_trajectory_error hS hroot hcard hpack hcd)
    (sum_configurationLossSelectors_trajectory_error H epsilon hS hroot hcard hpack
      hinter htrajectory)

theorem restrictedGreedyKernel_configuration_drift_zero_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (d K : ℕ) (H epsilon : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ C ∈ J, C.card = d + 1)
    (hpack : ∀ C ∈ J, IsPackingOn C)
    (hinter : ∀ U ∈ S.available, ∀ W ∈ S.available, U ≠ W →
      (U.1 ∩ W.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (htrajectory : ∀ U ∈ S.available,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilon) :
    |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
          (greedyConfigurationClass J S root 0).card) +
      (greedyConfigurationClass J S root 0).card * (d * H) /
        (S.available \ greedyClosedThreats F S root).card| ≤
      ((greedyConfigurationClass J S root 0).card *
          (d * epsilon + ((d + d.choose 2) * K : ℕ))) /
        (S.available \ greedyClosedThreats F S root).card := by
  rw [restrictedGreedyKernel_configuration_drift_zero root hS hR,
    ← add_div, neg_add_eq_sub, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (S.available \ greedyClosedThreats F S root).card :
      (0 : ℝ) ≤ (S.available \ greedyClosedThreats F S root).card), abs_sub_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [Nat.sub_zero] using
    (sum_configurationLossSelectors_trajectory_error (c := 0) H epsilon hS hroot hcard hpack
      hinter htrajectory)

end

end Erdos207
