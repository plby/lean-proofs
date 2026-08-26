/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Geometric sums in the characteristic-function estimate for Erdős 521.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open scoped BigOperators

/-- Variance of the sum with `N` fair-sign coefficients at the real point `x`. -/
def geometricVariance (x : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, x ^ (2 * k)

theorem geometricVariance_nonneg (x : ℝ) (N : ℕ) : 0 ≤ geometricVariance x N := by
  apply Finset.sum_nonneg
  intro k _
  rw [pow_mul]
  positivity

theorem geometricVariance_mono (x : ℝ) : Monotone (geometricVariance x) := by
  intro n m hnm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
  intro k _ _
  rw [pow_mul]
  positivity

theorem geometricVariance_add (x : ℝ) (N M : ℕ) :
    geometricVariance x (N + M) =
      geometricVariance x N + x ^ (2 * N) * geometricVariance x M := by
  rw [geometricVariance, Finset.sum_range_add]
  simp only [geometricVariance, Nat.mul_add, pow_add, Finset.mul_sum]

theorem geometricVariance_add_le {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (N M : ℕ) :
    geometricVariance x (N + M) ≤ geometricVariance x N + geometricVariance x M := by
  rw [geometricVariance_add]
  exact add_le_add le_rfl (mul_le_of_le_one_left (geometricVariance_nonneg x M)
    (pow_le_one₀ hx₀ hx₁))

theorem geometricVariance_le_double {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    {N L : ℕ} (hNL : N ≤ 2 * L) : geometricVariance x N ≤ 2 * geometricVariance x L := by
  exact (geometricVariance_mono x hNL).trans
    (by simpa only [two_mul] using geometricVariance_add_le hx₀ hx₁ L L)

theorem sum_tail_square (x t : ℝ) (m N : ℕ) :
    (∑ k ∈ Finset.Ico m N, (t * x ^ k) ^ 2) =
      (t * x ^ m) ^ 2 * geometricVariance x (N - m) := by
  rw [Finset.sum_Ico_eq_sum_range, geometricVariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  ring

/-- A terminal half contains at least half the variance after rescaling its
first coefficient to one. -/
theorem sum_tail_square_lower {x t : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    {m N : ℕ} (hmN : 2 * m ≤ N) :
    (t * x ^ m) ^ 2 * geometricVariance x N / 2 ≤
      ∑ k ∈ Finset.Ico m N, (t * x ^ k) ^ 2 := by
  rw [sum_tail_square]
  have h := geometricVariance_le_double hx₀ hx₁ (show N ≤ 2 * (N - m) by omega)
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (t * x ^ m))
  linarith

end Erdos521
