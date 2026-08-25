import Mathlib

/-!
# The small-angle cubic in the glide-crossing argument

These lemmas prove the cubic comparison by factorization, without calculus.
-/

noncomputable section

namespace Puzzling139335.GlideCrossing

/-- The polynomial obtained after the tangent-half-angle substitution. -/
def smallCubic (C S t : ℝ) : ℝ :=
  2 * (1 + 2 * C) * t ^ 3 - (2 + C) * t ^ 2 +
    2 * (1 - S - 2 * C) * t + C

/-- The difference factorization used for an algebraic monotonicity proof. -/
theorem smallCubic_sub_factor (C S x y : ℝ) :
    smallCubic C S x - smallCubic C S y =
      (y - x) * ((2 + C) * (x + y) -
        2 * (1 + 2 * C) * (x ^ 2 + x * y + y ^ 2) -
        2 * (1 - S - 2 * C)) := by
  unfold smallCubic
  ring

/-- A slightly larger interval than the geometric application requires. -/
theorem smallCubic_antitone {C S x y : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1 / 2)
    (hlinear : 1 - S - 2 * C < 0)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 4) :
    smallCubic C S y ≤ smallCubic C S x := by
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hx1 : x ≤ 1 / 4 := le_trans hxy hy
  have hsum0 : 0 ≤ x + y := add_nonneg hx hy0
  have hsum1 : x + y ≤ 1 / 2 := by linarith
  have hxy0 : 0 ≤ x * y := mul_nonneg hx hy0
  have hquad0 : 0 ≤ x ^ 2 + x * y + y ^ 2 := by positivity
  have hsumprod : 0 ≤ (x + y) * (1 / 2 - (x + y)) :=
    mul_nonneg hsum0 (sub_nonneg.mpr hsum1)
  have hquad : x ^ 2 + x * y + y ^ 2 ≤ (x + y) / 2 := by
    nlinarith
  have hcoef : 2 * (1 + 2 * C) ≤ 4 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hquad0
  have hCsum : 0 ≤ C * (x + y) := mul_nonneg hC0 hsum0
  have hfactor : 0 < (2 + C) * (x + y) -
      2 * (1 + 2 * C) * (x ^ 2 + x * y + y ^ 2) -
      2 * (1 - S - 2 * C) := by
    nlinarith
  have hdiff : 0 ≤ smallCubic C S x - smallCubic C S y := by
    rw [smallCubic_sub_factor]
    exact mul_nonneg (sub_nonneg.mpr hxy) hfactor.le
  exact sub_nonneg.mp hdiff

/-- The endpoint expression is positive with generous rational bounds. -/
theorem smallCubic_endpoint_lower_pos {C S : ℝ}
    (hC0 : 0 < C) (hC1 : C < 3 / 10)
    (hS0 : 9 / 10 < S) (hS1 : S < 1) :
    0 < C * (1 - C * (1 / 2 + 2 * S)) / (1 + S) := by
  have hden : 0 < 1 + S := by linarith
  have hmul : C * (1 / 2 + 2 * S) < C * (5 / 2) :=
    mul_lt_mul_of_pos_left (by linarith) hC0
  have hbracket : 0 < 1 - C * (1 / 2 + 2 * S) := by
    nlinarith
  exact div_pos (mul_pos hC0 hbracket) hden

private theorem smallCubic_endpoint_expansion {C S : ℝ} (hden : 1 + S ≠ 0) :
    smallCubic C S (C / (1 + S)) =
      2 * (1 + (C / (1 + S)) ^ 2) *
        (C * (1 - C * (1 / 2 + 2 * S)) / (1 + S)) +
      C * (C ^ 2 + S ^ 2 - 1) * (4 * C * S + 5 * C - S - 1) /
        (1 + S) ^ 3 := by
  unfold smallCubic
  field_simp
  ring

/-- The exact endpoint identity, using only the unit-circle equation. -/
theorem smallCubic_endpoint_identity {C S : ℝ}
    (hcircle : C ^ 2 + S ^ 2 = 1) (hden : 1 + S ≠ 0) :
    smallCubic C S (C / (1 + S)) =
      2 * (1 + (C / (1 + S)) ^ 2) *
        (C * (1 - C * (1 / 2 + 2 * S)) / (1 + S)) := by
  rw [smallCubic_endpoint_expansion hden, hcircle]
  ring

/-- Endpoint positivity is proved here, rather than assumed. -/
theorem smallCubic_endpoint_pos {C S : ℝ}
    (hC0 : 0 < C) (hC1 : C < 3 / 10)
    (hS0 : 9 / 10 < S) (hS1 : S < 1)
    (hcircle : C ^ 2 + S ^ 2 = 1) :
    0 < smallCubic C S (C / (1 + S)) := by
  have hden : 0 < 1 + S := by linarith
  rw [smallCubic_endpoint_identity hcircle hden.ne']
  exact mul_pos (by positivity) (smallCubic_endpoint_lower_pos hC0 hC1 hS0 hS1)

private theorem smallCubic_linear_neg {C S : ℝ}
    (hC : 0 < C) (hS : 0 < S) (hcircle : C ^ 2 + S ^ 2 = 1) :
    1 - S - 2 * C < 0 := by
  have hCS : 0 < C * S := mul_pos hC hS
  have hsum : 1 < C + S := by
    by_contra h
    have hprod : 0 ≤ (1 - (C + S)) * (1 + (C + S)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  linarith

/-- Positivity throughout the required half-angle interval. -/
theorem smallCubic_pos {C S t : ℝ}
    (hC0 : 0 < C) (hC1 : C < 3 / 10)
    (hS0 : 9 / 10 < S) (hS1 : S < 1)
    (hcircle : C ^ 2 + S ^ 2 = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ C / (1 + S)) :
    0 < smallCubic C S t := by
  have hden : 0 < 1 + S := by linarith
  have hend : C / (1 + S) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hlinear : 1 - S - 2 * C < 0 :=
    smallCubic_linear_neg hC0 (by linarith) hcircle
  have hmono := smallCubic_antitone hC0.le (by linarith) hlinear ht0 ht1 hend
  exact lt_of_lt_of_le (smallCubic_endpoint_pos hC0 hC1 hS0 hS1 hcircle) hmono

/-- Exact rational tangent-half-angle substitution in the lower bound. -/
theorem smallCubic_halfAngle_identity (C S t : ℝ) :
    2 * (1 + t ^ 2) *
      (2 * t / (1 + t ^ 2) -
        (1 + (C * (1 - t ^ 2) + 2 * S * t) / (1 + t ^ 2)) / 2 +
        (1 - t ^ 2) / (1 + t ^ 2) *
          (1 / 2 + C - (1 + 2 * C) * t)) =
      smallCubic C S t := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  unfold smallCubic
  field_simp
  ring

end Puzzling139335.GlideCrossing
