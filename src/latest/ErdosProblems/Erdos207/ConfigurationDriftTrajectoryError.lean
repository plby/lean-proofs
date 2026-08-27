/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationDriftError
import ErdosProblems.Erdos207.ConfigurationDriftArithmetic

/-! # The actual configuration drift compared with the coupled target equation -/

namespace Erdos207

open Finset

noncomputable section

theorem restrictedGreedyKernel_configuration_drift_succ_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (c d K : ℕ) (H epsilonH Z y₀ y₁ e₀ e₁ A epsilonA : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ E ∈ J, E.card = d + 1) (hpack : ∀ E ∈ J, IsPackingOn E) (hcd : c + 2 ≤ d)
    (hinter : ∀ U ∈ S.available, ∀ W ∈ S.available, U ≠ W → (U.1 ∩ W.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilonH)
    (hgain : (∑ E ∈ greedyConfigurationClass J S root c,
      ((greedyConfigurationRedundantWitnesses F S E).card : ℝ)) ≤ Z)
    (hprev : |((greedyConfigurationClass J S root c).card : ℝ) - y₀| ≤ e₀)
    (hcurr : |((greedyConfigurationClass J S root (c + 1)).card : ℝ) - y₁| ≤ e₁)
    (hA : 0 < A)
    (hdenom : |((S.available \ greedyClosedThreats F S root).card : ℝ) - A| ≤ epsilonA) :
    let R := S.available \ greedyClosedThreats F S root
    let α : ℝ := (d - c : ℕ)
    let β : ℝ := (d - (c + 1) : ℕ)
    let v : ℝ := (greedyConfigurationClass J S root (c + 1)).card
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
          (greedyConfigurationClass J S root (c + 1)).card) - (α * y₀ - β * y₁ * H) / A| ≤
      (2 * Z + v * (β * epsilonH + (((d - (c + 1)) + (d - (c + 1)).choose 2) * K : ℕ))) / R.card +
        (α * e₀ + β * |H| * e₁) / R.card + |α * y₀ - β * y₁ * H| * epsilonA / (R.card * A) := by
  dsimp only
  let R := S.available \ greedyClosedThreats F S root
  let α : ℝ := (d - c : ℕ)
  let β : ℝ := (d - (c + 1) : ℕ)
  let u : ℝ := (greedyConfigurationClass J S root c).card
  let v : ℝ := (greedyConfigurationClass J S root (c + 1)).card
  let μ := (restrictedGreedyKernel F S R hR).expectationReal
    (fun S' ↦ ((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
      (greedyConfigurationClass J S root (c + 1)).card)
  let errorFactor : ℝ := β * epsilonH + (((d - (c + 1)) + (d - (c + 1)).choose 2) * K : ℕ)
  let rawGain : ℝ := ∑ E ∈ greedyConfigurationClass J S root c,
    ((greedyConfigurationRedundantWitnesses F S E).card : ℝ)
  have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hR
  have hraw := restrictedGreedyKernel_configuration_drift_succ_error root c d K H epsilonH
    hS hroot hR hcard hpack hcd hinter hthreat
  change |μ - (u * α - v * (β * H)) / R.card| ≤ (2 * rawGain + v * errorFactor) / R.card at hraw
  have he : u * α - v * (β * H) = α * u - β * v * H := by ring
  rw [he] at hraw
  have hraw' : |μ - (α * u - β * v * H) / R.card| ≤ (2 * Z + v * errorFactor) / R.card :=
    hraw.trans (div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hgain (by norm_num)) le_rfl) hRpos.le)
  exact configuration_drift_quotient_error_le μ u v y₀ y₁ α β H R.card A
    ((2 * Z + v * errorFactor) / R.card) e₀ e₁ epsilonA hRpos hA
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hraw' hprev hcurr hdenom

theorem restrictedGreedyKernel_configuration_drift_zero_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (d K : ℕ) (H epsilonH y e A epsilonA : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ E ∈ J, E.card = d + 1) (hpack : ∀ E ∈ J, IsPackingOn E)
    (hinter : ∀ U ∈ S.available, ∀ W ∈ S.available, U ≠ W → (U.1 ∩ W.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilonH)
    (hcurr : |((greedyConfigurationClass J S root 0).card : ℝ) - y| ≤ e)
    (hA : 0 < A)
    (hdenom : |((S.available \ greedyClosedThreats F S root).card : ℝ) - A| ≤ epsilonA) :
    let R := S.available \ greedyClosedThreats F S root
    let v : ℝ := (greedyConfigurationClass J S root 0).card
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
          (greedyConfigurationClass J S root 0).card) + (d : ℝ) * y * H / A| ≤
      (v * ((d : ℝ) * epsilonH + ((d + d.choose 2) * K : ℕ))) / R.card +
        ((d : ℝ) * |H| * e) / R.card + |(d : ℝ) * y * H| * epsilonA / (R.card * A) := by
  dsimp only
  let R := S.available \ greedyClosedThreats F S root
  let v : ℝ := (greedyConfigurationClass J S root 0).card
  let μ := (restrictedGreedyKernel F S R hR).expectationReal
    (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
      (greedyConfigurationClass J S root 0).card)
  let eta := (v * ((d : ℝ) * epsilonH + ((d + d.choose 2) * K : ℕ))) / (R.card : ℝ)
  have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hR
  have hraw := restrictedGreedyKernel_configuration_drift_zero_error root d K H epsilonH
    hS hroot hR hcard hpack hinter hthreat
  have hraw' : |μ - (0 * 0 - (d : ℝ) * v * H) / R.card| ≤ eta := by
    have he : μ - (0 * 0 - (d : ℝ) * v * H) / R.card = μ + v * ((d : ℝ) * H) / R.card := by ring
    rw [he]
    exact hraw
  have h := configuration_drift_quotient_error_le μ 0 v 0 y 0 d H R.card A eta 0 e epsilonA
    hRpos hA le_rfl (Nat.cast_nonneg _) hraw' (by simp) hcurr hdenom
  simpa only [zero_mul, zero_add, zero_sub, neg_div, sub_neg_eq_add, abs_neg] using h

end

end Erdos207
