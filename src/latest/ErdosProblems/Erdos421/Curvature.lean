import Mathlib

/-!
# Curvature estimates for positive interval products

These estimates investigate an elementary replacement for the general
affine-curve point-count input. No lattice-point bound is asserted here yet.
-/

namespace Erdos421

noncomputable def reciprocalSum (r : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range r, (1 / (x - i))

noncomputable def reciprocalSquareSum (r : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range r, (1 / (x - i)) ^ 2

theorem curvature_polynomial_bound {r s : ℕ} (hs : 0 < s) (hrs : s < r)
    {x : ℝ} (hx : 2 * (r : ℝ) ^ 2 ≤ x) :
    (s : ℝ) * x ^ 2 < (r : ℝ) * (x - r + 1) ^ 2 := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  have hsr : (s : ℝ) + 1 ≤ r := by exact_mod_cast hrs
  have hxpos : 0 < x := by nlinarith
  have hsmall : 2 * (r : ℝ) * (r - 1) < x := by nlinarith
  have hprod := mul_lt_mul_of_pos_right hsmall hxpos
  have hsq := mul_nonneg (show (0 : ℝ) ≤ r - s - 1 by linarith) (sq_nonneg x)
  have hlast := mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sq_nonneg ((r : ℝ) - 1))
  nlinarith

theorem reciprocalSum_lower {r : ℕ} {x : ℝ} (hx : (r : ℝ) < x) :
    (r : ℝ) / x ≤ reciprocalSum r x := by
  have hxpos : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg r) hx
  calc
    (r : ℝ) / x = ∑ _i ∈ Finset.range r, (1 / x) := by simp [div_eq_mul_inv]
    _ ≤ reciprocalSum r x := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : (i : ℝ) < r := by exact_mod_cast Finset.mem_range.mp hi
      have hpos : 0 < x - i := by linarith
      apply one_div_le_one_div_of_le hpos
      have := Nat.cast_nonneg (α := ℝ) i
      linarith

theorem reciprocalSquareSum_upper {r : ℕ} {x : ℝ} (hx : (r : ℝ) < x) :
    reciprocalSquareSum r x ≤ (r : ℝ) * (1 / (x - r + 1)) ^ 2 := by
  have hdpos : 0 < x - r + 1 := by linarith
  calc
    reciprocalSquareSum r x ≤ ∑ _i ∈ Finset.range r, (1 / (x - r + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : (i : ℝ) + 1 ≤ r := by exact_mod_cast Finset.mem_range.mp hi
      have hden : x - r + 1 ≤ x - i := by linarith
      have hle := one_div_le_one_div_of_le hdpos hden
      have hpos : 0 ≤ 1 / (x - i) := le_of_lt (one_div_pos.mpr (hdpos.trans_le hden))
      nlinarith [sq_nonneg (1 / (x - r + 1) - 1 / (x - i))]
    _ = (r : ℝ) * (1 / (x - r + 1)) ^ 2 := by simp

/-- This is the positive second-derivative numerator for the `s`th root of
the falling product of length `r`, beyond the cutoff `2r²`. -/
theorem falling_root_curvature_pos {r s : ℕ} (hs : 0 < s) (hrs : s < r)
    {x : ℝ} (hx : 2 * (r : ℝ) ^ 2 ≤ x) :
    0 < (reciprocalSum r x) ^ 2 - (s : ℝ) * reciprocalSquareSum r x := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  have hrpos : (0 : ℝ) < r := by positivity
  have hsnonneg : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hrx : (r : ℝ) < x := by nlinarith
  have hxpos : 0 < x := hrpos.trans hrx
  have hdpos : 0 < x - r + 1 := by linarith
  have hpoly := curvature_polynomial_bound hs hrs hx
  have hfrac : (s : ℝ) * ((r : ℝ) * (1 / (x - r + 1)) ^ 2) < ((r : ℝ) / x) ^ 2 := by
    rw [one_div_pow, mul_one_div, ← mul_div_assoc, div_pow]
    apply (div_lt_div_iff₀ (sq_pos_of_pos hdpos) (sq_pos_of_pos hxpos)).mpr
    nlinarith [mul_lt_mul_of_pos_left hpoly hrpos]
  have hlo := reciprocalSum_lower hrx
  have hhi := reciprocalSquareSum_upper hrx
  have hnonneg : 0 ≤ (r : ℝ) / x := div_nonneg hrpos.le hxpos.le
  have hsq : ((r : ℝ) / x) ^ 2 ≤ (reciprocalSum r x) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhi hsnonneg
  linarith

end Erdos421
