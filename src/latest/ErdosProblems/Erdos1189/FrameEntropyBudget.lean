/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A common cutoff for the frame and the remaining moduli.
Informal source: BBMST Section 7.2. Using one external budget avoids separate
small-large-prime cases in the analytic estimate.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.RootLogCutoff

namespace Erdos1189

open Finset

lemma sum_rootLog_prefix_le_cutoff {β : Type*} (S : Finset β) (rank w : β → ℕ)
    (hinj : Set.InjOn rank S) {a n : ℝ} (ha : 0 < a) (hn : 1 < n) :
    (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) ≤
      ((2 / 3 : ℝ) * (∑ i ∈ S, w i) * Real.sqrt ((∑ i ∈ S, w i : ℕ) : ℝ)) /
        (Real.sqrt a * Real.sqrt (Real.log n)) +
          (∑ i ∈ S, w i) * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) := by
  have hsum : (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) ≤
      (∑ i ∈ S, (w i : ℝ) * Real.sqrt (prefixWeight S rank w i)) /
        (Real.sqrt a * Real.sqrt (Real.log n)) +
          (∑ i ∈ S, w i) * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) := by
    have h := sum_le_sum (s := S) (fun i _ => mul_le_mul_of_nonneg_left
      (rootLog_cutoff ha hn (prefixWeight S rank w i)) (Nat.cast_nonneg (w i)))
    simpa only [mul_add, ← mul_div_assoc, sum_add_distrib, ← sum_div, ← sum_mul,
      ← Nat.cast_sum] using h
  exact hsum.trans (add_le_add
    (div_le_div_of_nonneg_right (sum_sqrt_prefixWeight_le S rank w hinj) (by positivity)) le_rfl)

lemma frame_and_remainder_entropy_budget {β : Type*} (S : Finset β) (rank w : β → ℕ)
    (hinj : Set.InjOn rank S) {a n x : ℝ} (ha : 0 < a) (hn : 1 < n) (hx : 0 ≤ x) :
    (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) +
      x * rootLog (∑ i ∈ S, w i) ≤
        (2 / (3 * Real.sqrt a)) * (((∑ i ∈ S, w i : ℕ) : ℝ) + x) *
          Real.sqrt (((∑ i ∈ S, w i : ℕ) : ℝ) + x) / Real.sqrt (Real.log n) +
            (((∑ i ∈ S, w i : ℕ) : ℝ) + x) * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) := by
  let m : ℝ := ((∑ i ∈ S, w i : ℕ) : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hframe := sum_rootLog_prefix_le_cutoff S rank w hinj ha hn
  have hextra := mul_le_mul_of_nonneg_left (rootLog_cutoff ha hn (∑ i ∈ S, w i)) hx
  have hden : 0 < Real.sqrt a * Real.sqrt (Real.log n) :=
    mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr (Real.log_pos hn))
  have hconvex := sqrt_power_increment hm (le_add_of_nonneg_right hx)
  have hnum : (2 / 3 : ℝ) * m * Real.sqrt m + x * Real.sqrt m ≤
      (2 / 3 : ℝ) * (m + x) * Real.sqrt (m + x) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  have hsum := add_le_add hframe hextra
  have heq : (2 / 3 : ℝ) * (m + x) * Real.sqrt (m + x) /
      (Real.sqrt a * Real.sqrt (Real.log n)) =
        (2 / (3 * Real.sqrt a)) * (m + x) * Real.sqrt (m + x) /
          Real.sqrt (Real.log n) := by ring
  rw [heq] at hdiv
  change _ ≤ (2 / (3 * Real.sqrt a)) * (m + x) * Real.sqrt (m + x) /
    Real.sqrt (Real.log n) + (m + x) * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2)
  change _ ≤ (2 / 3 : ℝ) * m * Real.sqrt m / (Real.sqrt a * Real.sqrt (Real.log n)) +
    m * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) +
      x * (Real.sqrt m / (Real.sqrt a * Real.sqrt (Real.log n)) +
        Real.sqrt (n ^ a) / Real.sqrt (Real.log 2)) at hsum
  apply hsum.trans
  calc
    _ = ((2 / 3 : ℝ) * m * Real.sqrt m + x * Real.sqrt m) /
        (Real.sqrt a * Real.sqrt (Real.log n)) +
          (m + x) * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2) := by ring
    _ ≤ _ := add_le_add hdiv le_rfl

end Erdos1189
