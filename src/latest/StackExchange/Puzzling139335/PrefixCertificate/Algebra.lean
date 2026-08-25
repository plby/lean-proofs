import StackExchange.Puzzling139335.PrefixCertificate.PolynomialBounds

/-!
# Exact half-angle identities for the prefix certificate

The rational expressions in this file are the usual tangent-half-angle
parametrization of sine and cosine.  Both possible orders of the two
half-angle parameters are covered by explicit polynomial identities.
-/

noncomputable section

namespace Puzzling139335.PrefixCertificate

def rationalSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

def rationalCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

def rationalGap (t r m : ℝ) : ℝ :=
  rationalSin t * rationalCos r + rationalCos t * rationalSin r +
    2 * (rationalCos t * rationalCos r - rationalSin t * rationalSin r) - 2 -
    m * (1 - rationalSin t +
      2 * (rationalCos t * rationalCos r - rationalSin t * rationalSin r) -
      2 * rationalSin r)

def trigN (a b : ℝ) : ℝ := Real.sin (a + b) + 2 * Real.cos (a + b) - 2

def trigD (a b : ℝ) : ℝ :=
  1 - Real.sin a + 2 * Real.cos (a + b) - 2 * Real.sin b

theorem half_angle_denominator_pos (x y : ℝ) :
    0 < (1 + x ^ 2) * (1 + y ^ 2) := by positivity

theorem rational_gap_identity_one (x y : ℝ) :
    rationalGap x y x * ((1 + x ^ 2) * (1 + y ^ 2)) =
      F0 x + (y - x) * (B1 x - A1 x * (x + y)) := by
  have hx : 1 + x ^ 2 ≠ 0 := by positivity
  have hy : 1 + y ^ 2 ≠ 0 := by positivity
  unfold rationalGap rationalSin rationalCos F0 A1 B1
  field_simp
  ring

theorem rational_gap_identity_two (x y : ℝ) :
    rationalGap y x x * ((1 + x ^ 2) * (1 + y ^ 2)) =
      F0 x + (y - x) * (B2 x - A2 x * (x + y)) := by
  have hx : 1 + x ^ 2 ≠ 0 := by positivity
  have hy : 1 + y ^ 2 ≠ 0 := by positivity
  unfold rationalGap rationalSin rationalCos F0 A2 B2
  field_simp
  ring

theorem rational_gap_pos_one {x y : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28)
    (hxy : x ≤ y) (hsum : x + y < 2 / 7) : 0 < rationalGap x y x := by
  have h := numerator_one_pos hx0 hx hxy hsum
  rw [← rational_gap_identity_one] at h
  exact (mul_pos_iff_of_pos_right (half_angle_denominator_pos x y)).mp h

theorem rational_gap_pos_two {x y : ℝ} (hx0 : 0 < x) (hx : x < 3 / 28)
    (hxy : x ≤ y) (hsum : x + y < 2 / 7) : 0 < rationalGap y x x := by
  have h := numerator_two_pos hx0 hx hxy hsum
  rw [← rational_gap_identity_two] at h
  exact (mul_pos_iff_of_pos_right (half_angle_denominator_pos x y)).mp h

theorem rational_gap_min_pos {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hmin : min t r < 3 / 28) (hsum : t + r < 2 / 7) :
    0 < rationalGap t r (min t r) := by
  rcases le_total t r with htr | hrt
  · rw [min_eq_left htr] at hmin ⊢
    exact rational_gap_pos_one ht hmin htr hsum
  · rw [min_eq_right hrt] at hmin ⊢
    exact rational_gap_pos_two hr hmin hrt (by linarith)

theorem trig_gap_eq_rational (a b m : ℝ)
    (hca : Real.cos a ≠ -1) (hcb : Real.cos b ≠ -1) :
    trigN a b - m * trigD a b =
      rationalGap (Real.tan (a / 2)) (Real.tan (b / 2)) m := by
  unfold trigN trigD rationalGap rationalSin rationalCos
  rw [Real.sin_add, Real.cos_add]
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq a,
    Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq b,
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq a hca,
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq b hcb]

theorem tan_half_eq_sin_div_one_add_cos (a : ℝ) (hca : Real.cos a ≠ -1) :
    Real.tan (a / 2) = Real.sin a / (1 + Real.cos a) := by
  have hd : 1 + Real.cos a ≠ 0 := by
    intro h
    apply hca
    linarith
  apply (eq_div_iff hd).mpr
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq a,
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq a hca]
  have ht : 1 + Real.tan (a / 2) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem tan_half_complement {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Real.tan ((Real.pi / 2 - θ) / 2) = Real.cos θ / (1 + Real.sin θ) := by
  have hc : Real.cos (Real.pi / 2 - θ) ≠ -1 := by
    rw [Real.cos_pi_div_two_sub]
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
    linarith
  rw [tan_half_eq_sin_div_one_add_cos _ hc,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem side_fit_le_tan_half {φ l : ℝ} (hφ : 0 < φ) (hφπ : φ < Real.pi / 2)
    (hfit : Real.cos φ + l * Real.sin φ ≤ 1) : l ≤ Real.tan (φ / 2) := by
  have hs : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφπ⟩
  have htan : Real.tan (φ / 2) * Real.sin φ = 1 - Real.cos φ := by
    rw [tan_half_eq_sin_div_one_add_cos φ (by linarith), div_mul_eq_mul_div]
    apply (div_eq_iff (by positivity : (1 : ℝ) + Real.cos φ ≠ 0)).mpr
    nlinarith [Real.sin_sq_add_cos_sq φ]
  by_contra h
  have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge h) hs
  linarith

/-- A division-free version of the extra rectangle-support inequality.
It isolates the algebra used to obtain the fifth prefix hypothesis. -/
theorem support_fit_lower_bound {A B c s p u v l T : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hrel : A * s - B * c = p)
    (hu : T * c + s * v ≤ c * u) (hv : c * l ≤ v) :
    A * T + B * (1 - l) + l * p ≤ A * u + B * (1 - l - v) := by
  have h₁ := mul_le_mul_of_nonneg_left hu hA
  have h₂ := mul_le_mul_of_nonneg_left hv hp
  have h₃ := congrArg (fun z : ℝ => z * v) hrel
  have hscaled : c * (A * T + B * (1 - l) + l * p) ≤
      c * (A * u + B * (1 - l - v)) := by
    nlinarith only [h₁, h₂, h₃]
  by_contra h
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) hc
  linarith

theorem support_projection_relation (θ φ : ℝ) :
    Real.cos (θ - φ) * Real.sin θ - Real.sin (θ - φ) * Real.cos θ = Real.sin φ := by
  have h := Real.sin_sub θ (θ - φ)
  have heq : θ - (θ - φ) = φ := by ring
  rw [heq] at h
  nlinarith only [h]

end Puzzling139335.PrefixCertificate
