import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit first-order bounds for finite differences of natural powers -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem real_pow_difference_bounds {s p : ℝ} (hs : 0 ≤ s) (hsp : s ≤ p) (k : ℕ) :
    k * s ^ (k - 1) * (p - s) ≤ p ^ k - s ^ k ∧
      p ^ k - s ^ k ≤ k * p ^ (k - 1) * (p - s) := by
  have hp : 0 ≤ p := hs.trans hsp
  have hdiff : 0 ≤ p - s := sub_nonneg.mpr hsp
  constructor
  · have hsum : (k : ℝ) * s ^ (k - 1) ≤
        ∑ i ∈ range k, p ^ i * s ^ (k - 1 - i) := by
      calc
        _ = ∑ _i ∈ range k, s ^ (k - 1) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro i hi
          have hexp : i + (k - 1 - i) = k - 1 := by have h := mem_range.mp hi; omega
          calc
            _ = s ^ i * s ^ (k - 1 - i) := by rw [← pow_add, hexp]
            _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hsp i) (pow_nonneg hs _)
    have h := mul_le_mul_of_nonneg_right hsum hdiff
    rw [geom_sum₂_mul] at h
    exact h
  · have h := abs_pow_sub_pow_le p s k
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hs hsp k)),
      abs_of_nonneg hdiff, abs_of_nonneg hp, abs_of_nonneg hs, max_eq_left hsp] at h
    nlinarith only [h]

theorem real_pow_difference_error {s p : ℝ} (hs : 0 ≤ s) (hsp : s ≤ p) (k : ℕ) :
    0 ≤ k * p ^ (k - 1) * (p - s) - (p ^ k - s ^ k) ∧
      k * p ^ (k - 1) * (p - s) - (p ^ k - s ^ k) ≤
        k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := real_pow_difference_bounds hs hsp k
  have hprev := (real_pow_difference_bounds hs hsp (k - 1)).2
  have hexp : k - 1 - 1 = k - 2 := by omega
  rw [hexp] at hprev
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hprev (sub_nonneg.mpr hsp)) (Nat.cast_nonneg k)
  exact ⟨sub_nonneg.mpr hhi, by nlinarith only [hlo, hmul]⟩

end Arxiv2411_18291
