import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite discrete Abel summation

This module isolates the exact finite summation-by-parts identity used in
the manuscript.  Keeping the endpoint terms explicit is important: the
later two-sided bounded-variation estimate is obtained only after these
finite identities have been proved and the tails have been controlled.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The partial sum of `a` on the integer interval from `u` through `v`. -/
def intervalPartialSum (a : ℕ → ℂ) (u v : ℕ) : ℂ :=
  ∑ n ∈ Icc u v, a n

/-- Exact finite Abel summation, including the right endpoint term. -/
theorem discreteAbel_identity (a w : ℕ → ℂ) {u v : ℕ} (huv : u ≤ v) :
    ∑ n ∈ Icc u v, a n * w n =
      intervalPartialSum a u v * w v +
        ∑ n ∈ Ico u v, intervalPartialSum a u n * (w n - w (n + 1)) := by
  induction v, huv using Nat.le_induction with
  | base => simp [intervalPartialSum]
  | succ v huv ih =>
      rw [sum_Icc_succ_top (huv.trans (Nat.le_succ v)),
        sum_Ico_succ_top huv, ih]
      simp only [intervalPartialSum, sum_Icc_succ_top (huv.trans (Nat.le_succ v))]
      ring

/-- A finite bounded-variation consequence of `discreteAbel_identity`.
Every boundary contribution is displayed on the right-hand side. -/
theorem norm_sum_mul_le_partialSum_mul_variation
    (a w : ℕ → ℂ) {u v : ℕ} (huv : u ≤ v) (M : ℝ)
    (hM : ∀ n ∈ Icc u v, ‖intervalPartialSum a u n‖ ≤ M) :
    ‖∑ n ∈ Icc u v, a n * w n‖ ≤
      M * (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
  rw [discreteAbel_identity a w huv]
  calc
    ‖intervalPartialSum a u v * w v +
          ∑ n ∈ Ico u v, intervalPartialSum a u n * (w n - w (n + 1))‖
        ≤ ‖intervalPartialSum a u v * w v‖ +
          ‖∑ n ∈ Ico u v, intervalPartialSum a u n * (w n - w (n + 1))‖ :=
      norm_add_le _ _
    _ ≤ ‖intervalPartialSum a u v‖ * ‖w v‖ +
          ∑ n ∈ Ico u v, ‖intervalPartialSum a u n * (w n - w (n + 1))‖ := by
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _
    _ ≤ M * ‖w v‖ +
          ∑ n ∈ Ico u v, M * ‖w n - w (n + 1)‖ := by
      gcongr with n hn
      · exact hM v (mem_Icc.mpr ⟨huv, le_rfl⟩)
      · rw [norm_mul]
        gcongr
        exact hM n (mem_Icc.mpr ⟨(mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩)
    _ = M * (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
      rw [mul_add, mul_sum]

/-- Version whose hypothesis uniformly controls every nonempty finite
integer interval.  This is the finite statement applied to products of
Ramanujan sums later in the proof. -/
theorem norm_sum_mul_le_intervalBound
    (a w : ℕ → ℂ) {u v : ℕ} (huv : u ≤ v) (M : ℝ)
    (hM : ∀ i j : ℕ, i ≤ j → ‖∑ n ∈ Icc i j, a n‖ ≤ M) :
    ‖∑ n ∈ Icc u v, a n * w n‖ ≤
      M * (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
  apply norm_sum_mul_le_partialSum_mul_variation a w huv M
  intro n hn
  exact hM u n (Finset.mem_Icc.mp hn).1

end

end Erdos1002
