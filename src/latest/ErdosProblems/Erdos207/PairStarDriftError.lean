/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClosedThreatDrift
import ErdosProblems.Erdos207.ConfigurationDriftArithmetic

/-! # Quantitative pair-star drift with exact closed threats -/

namespace Erdos207

open Finset

noncomputable section

theorem restrictedGreedyKernel_pairStar_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {P : Finset V}
    (hS : GreedyInvariant F S) (hP : P.card = 2)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty)
    (H epsilon : ℝ)
    (hthreat : ∀ U ∈ availableTrianglesContainingPair S P,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilon) :
    let Q := availableTrianglesContainingPair S P
    let R := S.available \ Q
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S) +
      (Q.card : ℝ) * (H - Q.card) / R.card| ≤ Q.card * epsilon / R.card := by
  dsimp only
  let Q := availableTrianglesContainingPair S P
  let R := S.available \ Q
  have hsub : Q ⊆ S.available := fun U hU ↦ (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hdenom : (S.available.card : ℝ) - Q.card = (R.card : ℝ) := by
    dsimp only [R]
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hR
  have hs := abs_sum_sub_card_mul_le_sum_error Q
    (fun U ↦ ((greedyClosedThreats F S U).card : ℝ) - Q.card)
    (fun _ ↦ epsilon) (H - Q.card) (by
      intro U hU
      have he : (((greedyClosedThreats F S U).card : ℝ) - Q.card) - (H - Q.card) =
          ((greedyClosedThreats F S U).card : ℝ) - H := by ring
      rw [he]
      exact hthreat U hU)
  rw [sum_const, nsmul_eq_mul] at hs
  rw [restrictedGreedyKernel_pairStar_drift hS hP hR]
  change |(-(∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card))) /
    ((S.available.card : ℝ) - Q.card) + (Q.card : ℝ) * (H - Q.card) / R.card| ≤ _
  rw [hdenom]
  have he : (-(∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card))) / R.card +
      (Q.card : ℝ) * (H - Q.card) / R.card =
      -((∑ U ∈ Q, (((greedyClosedThreats F S U).card : ℝ) - Q.card)) -
        (Q.card : ℝ) * (H - Q.card)) / R.card := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hRpos]
  exact div_le_div_of_nonneg_right hs hRpos.le

theorem restrictedGreedyKernel_pairStar_drift_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {P : Finset V}
    (hS : GreedyInvariant F S) (hP : P.card = 2)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty)
    (H epsilonH x epsilonX A epsilonA : ℝ) (hA : 0 < A)
    (hthreat : ∀ U ∈ availableTrianglesContainingPair S P,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilonH)
    (hpair : |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ epsilonX)
    (hdenom : |((S.available \ availableTrianglesContainingPair S P).card : ℝ) - A| ≤ epsilonA) :
    let Q := availableTrianglesContainingPair S P
    let R := S.available \ Q
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S) +
      x * (H - x) / A| ≤
        Q.card * epsilonH / R.card +
          epsilonX * (|H| + |(Q.card : ℝ)| + |x|) / R.card +
            |x * (H - x)| * epsilonA / (R.card * A) := by
  dsimp only
  let Q := availableTrianglesContainingPair S P
  let R := S.available \ Q
  let μ := (restrictedGreedyKernel F S R hR).expectationReal
    (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S)
  have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hR
  have hraw : |μ - (-((Q.card : ℝ) * (H - Q.card))) / R.card| ≤ Q.card * epsilonH / R.card := by
    simpa only [neg_div, sub_neg_eq_add] using restrictedGreedyKernel_pairStar_drift_error hS hP hR H epsilonH hthreat
  have hn : |(-((Q.card : ℝ) * (H - Q.card))) - (-(x * (H - x)))| ≤
      epsilonX * (|H| + |(Q.card : ℝ)| + |x|) := by
    rw [neg_sub_neg, abs_sub_comm]
    exact pair_quadratic_numerator_error_le Q.card x H epsilonX hpair
  have hquot := abs_div_sub_div_le_of_errors hRpos hA hn hdenom
  change |μ + x * (H - x) / A| ≤ _
  have he : μ + x * (H - x) / A = μ - (-(x * (H - x))) / A := by ring
  rw [he]
  have htri := (abs_sub_le μ (-((Q.card : ℝ) * (H - Q.card)) / R.card)
    (-(x * (H - x)) / A)).trans (add_le_add hraw hquot)
  simpa only [abs_neg, add_assoc] using htri

end

end Erdos207
