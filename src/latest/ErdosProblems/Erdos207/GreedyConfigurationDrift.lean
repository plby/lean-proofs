/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationGainSelectors
import ErdosProblems.Erdos207.GreedyConfigurationLossSelectors
import ErdosProblems.Erdos207.GreedyClosedThreatDrift

/-! # Exact root-preserving conditional configuration drift -/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

theorem filter_root_preserving_configuration_gain_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hC : C ∈ greedyConfigurationClass J S root c) :
    {T ∈ S.available \ greedyClosedThreats F S root |
      C ∈ greedyConfigurationGains F J S root c T} =
        greedyConfigurationGainSelectors F S root C := by
  classical
  ext T
  simpa only [mem_filter, hC, true_and] using
    (root_preserving_configuration_gain_iff (J := J) (root := root)
      (c := c) (C := C) (T := T) hS hroot)

theorem sum_root_preserving_configuration_gains_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c : ℕ) (hS : GreedyInvariant F S)
    (hroot : root ∈ S.available) :
    ∑ T ∈ S.available \ greedyClosedThreats F S root,
        (greedyConfigurationGains F J S root c T).card =
      ∑ C ∈ greedyConfigurationClass J S root c,
        (greedyConfigurationGainSelectors F S root C).card := by
  classical
  let R := S.available \ greedyClosedThreats F S root
  let X := greedyConfigurationClass J S root c
  calc
    (∑ T ∈ R, (greedyConfigurationGains F J S root c T).card) =
        ∑ T ∈ R, ∑ C ∈ X,
          if C ∈ greedyConfigurationGains F J S root c T then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro T _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have hset : {C ∈ X | C ∈ greedyConfigurationGains F J S root c T} =
          greedyConfigurationGains F J S root c T := by
        ext C
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h ↦ (mem_filter.mp h).1)
      rw [hset]
      rfl
    _ = ∑ C ∈ X, ∑ T ∈ R,
          if C ∈ greedyConfigurationGains F J S root c T then (1 : ℕ) else 0 := sum_comm
    _ = ∑ C ∈ X, (greedyConfigurationGainSelectors F S root C).card := by
      apply sum_congr rfl
      intro C hC
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [filter_root_preserving_configuration_gain_eq hS hroot hC]
      rfl

theorem restrictedGreedyKernel_configuration_drift_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c : ℕ) (hS : GreedyInvariant F S)
    (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ ((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
        (greedyConfigurationClass J S root (c + 1)).card) =
      ((∑ C ∈ greedyConfigurationClass J S root c,
          ((greedyConfigurationGainSelectors F S root C).card : ℝ)) -
        ∑ C ∈ greedyConfigurationClass J S root (c + 1),
          ((greedyConfigurationLossSelectors F S root C).card : ℝ)) /
            (S.available \ greedyClosedThreats F S root).card := by
  let R := S.available \ greedyClosedThreats F S root
  have hgain :
      (∑ T ∈ R, ((greedyConfigurationGains F J S root c T).card : ℝ)) =
        ∑ C ∈ greedyConfigurationClass J S root c,
          ((greedyConfigurationGainSelectors F S root C).card : ℝ) := by
    exact_mod_cast sum_root_preserving_configuration_gains_eq
      (J := J) root c hS hroot
  have hloss :
      (∑ T ∈ R, ((greedyConfigurationLosses F J S root (c + 1) T).card : ℝ)) =
        ∑ C ∈ greedyConfigurationClass J S root (c + 1),
          ((greedyConfigurationLossSelectors F S root C).card : ℝ) := by
    exact_mod_cast sum_root_preserving_configuration_losses_eq (J := J) root (c + 1) hS
  rw [restrictedGreedyKernel_expectationReal]
  have hinc :
      (∑ T ∈ R, (((greedyConfigurationClass J (greedyStep F S T) root (c + 1)).card : ℝ) -
        (greedyConfigurationClass J S root (c + 1)).card)) =
      ∑ T ∈ R, (((greedyConfigurationGains F J S root c T).card : ℝ) -
        (greedyConfigurationLosses F J S root (c + 1) T).card) := by
    apply sum_congr rfl
    intro T hT
    exact greedyConfigurationClass_increment_succ c hS (mem_sdiff.mp hT).1
  change (R.card : ℝ)⁻¹ * _ = _
  rw [hinc, sum_sub_distrib, hgain, hloss]
  ring

theorem restrictedGreedyKernel_configuration_drift_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (hS : GreedyInvariant F S)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
        (greedyConfigurationClass J S root 0).card) =
      -(∑ C ∈ greedyConfigurationClass J S root 0,
          ((greedyConfigurationLossSelectors F S root C).card : ℝ)) /
            (S.available \ greedyClosedThreats F S root).card := by
  let R := S.available \ greedyClosedThreats F S root
  have hloss :
      (∑ T ∈ R, ((greedyConfigurationLosses F J S root 0 T).card : ℝ)) =
        ∑ C ∈ greedyConfigurationClass J S root 0,
          ((greedyConfigurationLossSelectors F S root C).card : ℝ) := by
    exact_mod_cast sum_root_preserving_configuration_losses_eq (J := J) root 0 hS
  rw [restrictedGreedyKernel_expectationReal]
  have hinc :
      (∑ T ∈ R, (((greedyConfigurationClass J (greedyStep F S T) root 0).card : ℝ) -
        (greedyConfigurationClass J S root 0).card)) =
      ∑ T ∈ R, -((greedyConfigurationLosses F J S root 0 T).card : ℝ) := by
    apply sum_congr rfl
    intro T hT
    exact greedyConfigurationClass_increment_zero hS (mem_sdiff.mp hT).1
  change (R.card : ℝ)⁻¹ * _ = _
  rw [hinc, sum_neg_distrib, hloss]
  ring

end

end Erdos207
