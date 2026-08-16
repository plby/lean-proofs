import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic

/-!
# Finite second-moment support bounds for Erdős problem 851

This file isolates the elementary Cauchy--Schwarz step in the second-moment
method.  If `R a` counts representations of `a`, its positive support is the
set of integers having at least one representation.  The lemmas below turn a
lower bound for the first moment and an upper bound for the second moment into
a lower bound for that support.
-/

open scoped BigOperators

namespace Erdos851

/-- Cauchy--Schwarz applied only to the nonzero support of a function. -/
theorem sq_sum_le_card_ne_zero_mul_sum_sq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ S, f i) ^ 2 ≤
      ((S.filter fun i => f i ≠ 0).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  let T := S.filter fun i => f i ≠ 0
  have hsum : (∑ i ∈ T, f i) = ∑ i ∈ S, f i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_not] at hiT
    exact hiT
  have hsumSq : (∑ i ∈ T, f i ^ 2) = ∑ i ∈ S, f i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_not] at hiT
    simp [hiT]
  calc
    (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ T, f i) ^ 2 := by rw [hsum]
    _ ≤ (T.card : ℝ) * ∑ i ∈ T, f i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = ((S.filter fun i => f i ≠ 0).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
      rw [hsumSq]

/-- The support form of Cauchy--Schwarz for a natural-valued counting
function. -/
theorem sq_sum_natCast_le_card_pos_mul_sum_sq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ) :
    (∑ i ∈ S, (R i : ℝ)) ^ 2 ≤
      ((S.filter fun i => 0 < R i).card : ℝ) *
        ∑ i ∈ S, (R i : ℝ) ^ 2 := by
  have hfilter :
      S.filter (fun i => (R i : ℝ) ≠ 0) = S.filter fun i => 0 < R i := by
    ext i
    simp [Nat.pos_iff_ne_zero]
  have h := sq_sum_le_card_ne_zero_mul_sum_sq S fun i => (R i : ℝ)
  rw [hfilter] at h
  exact h

/-- Finite second-moment method.  A first moment at least `L` and a second
moment at most `U` force `L² ≤ U` times the size of the positive support. -/
theorem lower_sq_le_card_pos_mul_upper
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ) {L U : ℝ}
    (hL : 0 ≤ L)
    (hfirst : L ≤ ∑ i ∈ S, (R i : ℝ))
    (hsecond : (∑ i ∈ S, (R i : ℝ) ^ 2) ≤ U) :
    L ^ 2 ≤ ((S.filter fun i => 0 < R i).card : ℝ) * U := by
  calc
    L ^ 2 ≤ (∑ i ∈ S, (R i : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hL hfirst 2
    _ ≤ ((S.filter fun i => 0 < R i).card : ℝ) *
        ∑ i ∈ S, (R i : ℝ) ^ 2 :=
      sq_sum_natCast_le_card_pos_mul_sum_sq S R
    _ ≤ ((S.filter fun i => 0 < R i).card : ℝ) * U := by
      exact mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg _)

/-- Division form of the finite second-moment method, also known as the
support case of the Paley--Zygmund inequality. -/
theorem lower_sq_div_upper_le_card_pos
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ) {L U : ℝ}
    (hL : 0 ≤ L) (hU : 0 < U)
    (hfirst : L ≤ ∑ i ∈ S, (R i : ℝ))
    (hsecond : (∑ i ∈ S, (R i : ℝ) ^ 2) ≤ U) :
    L ^ 2 / U ≤ ((S.filter fun i => 0 < R i).card : ℝ) := by
  rw [div_le_iff₀ hU]
  simpa [mul_comm] using
    lower_sq_le_card_pos_mul_upper S R hL hfirst hsecond

end Erdos851
