/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationJointInclusion
import Mathlib.Data.Nat.Choose.Bounds

/-! # Binomial normalization and exact cancellation of graph density -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem regularization_choose_lower
    (m r : ℕ) (hm : 2 * r ≤ m) (x : ℝ≥0) (hx : x ≤ m) :
    (x / 2) ^ r / (r.factorial : ℝ≥0) ≤ Nat.choose m r := by
  have hhalf : (m : ℝ≥0) / 2 ≤ ((m + 1 - r : ℕ) : ℝ≥0) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).mpr
    have hnat : m ≤ (m + 1 - r) * 2 := by omega
    exact_mod_cast hnat
  have hxhalf : x / 2 ≤ ((m + 1 - r : ℕ) : ℝ≥0) :=
    (div_le_div_of_nonneg_right hx zero_le).trans hhalf
  exact (div_le_div_of_nonneg_right (pow_le_pow_left' hxhalf r) zero_le).trans
    (Nat.pow_le_choose (α := ℝ≥0) r m)

theorem regularization_ratio_scale_le
    (m r : ℕ) (hm : 2 * r ≤ m) (n sigma C B D A : ℝ≥0)
    (hn : 0 < n) (hsigma : 0 < sigma) (hC : 0 < C)
    (hmass : sigma * n ^ 3 / C ≤ m) (hdegree : D ≤ B * sigma ^ r * n ^ r) :
    A * D / (Nat.choose m r : ℝ≥0) ≤
      A * (2 * C) ^ r * r.factorial * B / n ^ (2 * r) := by
  have hlow := regularization_choose_lower m r hm (sigma * n ^ 3 / C) hmass
  have hden : 0 < ((sigma * n ^ 3 / C / 2) ^ r / (r.factorial : ℝ≥0)) := by positivity
  have hfirst : A * D / (Nat.choose m r : ℝ≥0) ≤
      (A * (B * sigma ^ r * n ^ r)) / ((sigma * n ^ 3 / C / 2) ^ r / (r.factorial : ℝ≥0)) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdegree zero_le) zero_le).trans
    exact div_le_div_of_nonneg_left zero_le hden hlow
  apply hfirst.trans_eq
  have hn0 := ne_of_gt hn
  have hs0 := ne_of_gt hsigma
  have hC0 := ne_of_gt hC
  have hf0 : (r.factorial : ℝ≥0) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  simp only [div_pow, mul_pow, pow_mul]
  field_simp
  ring

theorem regularizationBaseHazard_le_source_scale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (G0 : Finset (Finset I)) (k : ℕ)
    (hm : 2 * (k - 1) ≤ Fintype.card I) (n sigma C B : ℝ≥0)
    (hn : 0 < n) (hsigma : 0 < sigma) (hC : 0 < C)
    (hmass : sigma * n ^ 3 / C ≤ Fintype.card I)
    (hdegree : (finiteHypergraphMaxDegree G0 : ℝ≥0) ≤ B * sigma ^ (k - 1) * n ^ (k - 1)) :
    2 * regularizationBaseHazard G0 k ≤
      (2 : ℝ≥0) ^ (k + 1) * (2 * C) ^ (k - 1) * (k - 1).factorial * B / n ^ (2 * (k - 1)) := by
  have hgap : (finiteHypergraphDegreeGap G0 : ℝ≥0) ≤ B * sigma ^ (k - 1) * n ^ (k - 1) := by
    apply le_trans _ hdegree
    exact_mod_cast (Nat.sub_le (finiteHypergraphMaxDegree G0) (finiteHypergraphMinDegree G0))
  have h := regularization_ratio_scale_le (Fintype.card I) (k - 1) hm n sigma C B
    (finiteHypergraphDegreeGap G0) ((2 : ℝ≥0) ^ (k + 1)) hn hsigma hC hmass hgap
  simpa only [regularizationBaseHazard, pow_succ, mul_div_assoc, mul_assoc, mul_comm, mul_left_comm] using h

end

end Erdos207
