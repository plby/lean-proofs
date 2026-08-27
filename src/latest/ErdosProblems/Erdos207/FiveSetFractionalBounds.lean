/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiveSetFractionalBalance

/-! # The five-set correction stays inside the probability interval -/

namespace Erdos207

open Finset

noncomputable section

theorem fiveSet_contained_edge_card_le
    {V : Type*} [DecidableEq V] (E : Finset (Finset V)) (J : Finset V)
    (hE : ∀ P ∈ E, P.card = 2) (hJ : J.card = 5) :
    (E.filter (· ⊆ J)).card ≤ 10 := by
  calc
    _ ≤ (J.powersetCard 2).card := card_le_card (fun P hP ↦
      mem_powersetCard.mpr ⟨(mem_filter.mp hP).2, hE P (mem_filter.mp hP).1⟩)
    _ = 10 := by rw [card_powersetCard, hJ]; decide

theorem fiveSet_local_correction_abs_le
    {V : Type*} [DecidableEq V] (E : Finset (Finset V)) (J T : Finset V)
    (c : Finset V → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ P ∈ E, P.card = 2) (hJ : J.card = 5)
    (hc : ∀ P ∈ E, |c P| ≤ B) :
    |∑ P ∈ E.filter (· ⊆ J), c P * fiveSetEdgeCorrection P J T| ≤
      if T ⊆ J then 10 * B / 3 else 0 := by
  by_cases hTJ : T ⊆ J
  · rw [if_pos hTJ]
    have hcard : ((E.filter (· ⊆ J)).card : ℝ) ≤ 10 := by
      exact_mod_cast fiveSet_contained_edge_card_le E J hE hJ
    calc
      _ ≤ ∑ P ∈ E.filter (· ⊆ J), |c P * fiveSetEdgeCorrection P J T| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _P ∈ E.filter (· ⊆ J), B * (1 / 3 : ℝ) := by
        apply sum_le_sum
        intro P hP
        rw [abs_mul]
        exact mul_le_mul (hc P (mem_filter.mp hP).1)
          (by simpa only [if_pos hTJ] using fiveSetEdgeCorrection_abs_le P J T)
          (abs_nonneg _) hB
      _ = ((E.filter (· ⊆ J)).card : ℝ) * (B / 3) := by
        simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ 10 * B / 3 := by nlinarith
  · simp [fiveSetEdgeCorrection, hTJ]

theorem fiveSet_fractional_weight_deviation
    {V : Type*} [DecidableEq V] (E Js : Finset (Finset V)) (T : Finset V)
    (c : Finset V → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ P ∈ E, P.card = 2) (hJ : ∀ J ∈ Js, J.card = 5)
    (hc : ∀ P ∈ E, |c P| ≤ B) :
    |fiveSetFractionalWeight E Js c T - 1 / 4| ≤
      (Js.filter (T ⊆ ·)).card * B * (5 / 6 : ℝ) := by
  unfold fiveSetFractionalWeight
  rw [add_sub_cancel_left, abs_mul, fiveSet_correction_sum_comm]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ J ∈ Js,
        |∑ P ∈ E.filter (· ⊆ J), c P * fiveSetEdgeCorrection P J T| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 4 : ℝ) * ∑ J ∈ Js, if T ⊆ J then 10 * B / 3 else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum (fun J hJs ↦ fiveSet_local_correction_abs_le E J T c B
        hB hE (hJ J hJs) hc)
    _ = _ := by rw [← sum_filter]; simp only [sum_const, nsmul_eq_mul]; ring

theorem fiveSet_fractional_weight_mem_unitInterval
    {V : Type*} [DecidableEq V] (E Js : Finset (Finset V)) (T : Finset V)
    (c : Finset V → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ P ∈ E, P.card = 2) (hJ : ∀ J ∈ Js, J.card = 5)
    (hc : ∀ P ∈ E, |c P| ≤ B)
    (hbudget : ((Js.filter (T ⊆ ·)).card : ℝ) * B ≤ 3 / 10) :
    0 ≤ fiveSetFractionalWeight E Js c T ∧ fiveSetFractionalWeight E Js c T ≤ 1 := by
  have hdev := fiveSet_fractional_weight_deviation E Js T c B hB hE hJ hc
  have habs : |fiveSetFractionalWeight E Js c T - 1 / 4| ≤ (1 / 4 : ℝ) := by
    nlinarith
  have hh := abs_le.mp habs
  constructor <;> linarith

end

end Erdos207
