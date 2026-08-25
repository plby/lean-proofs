import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Explicit elementary estimates for Erdős problem 157

The real-part bound below is the elementary disk estimate used in the
zero-free-region argument. It does not invoke a Riemann hypothesis or a
finite-field point-count theorem.
-/

namespace Erdos157.Elementary

/-- The two possible polynomial coincidences cannot both fail at large levels. -/
theorem scale_contradiction (a b : ℝ) (ha : 400 ≤ a) (hb : b ≤ a)
    (hprod : (b - 4) ^ 2 ≤ (7 / 20 : ℝ) * ((a + 2) ^ 2 + (b + 5) ^ 2))
    (hsingle : (a - 1) ^ 2 - (b + 7) ^ 2 ≤ (7 / 20 : ℝ) * (a + 2) ^ 2) :
    False := by
  have hupper : b ^ 2 ≤ (7 / 13 : ℝ) * a ^ 2 + 20 * a := by nlinarith
  have hlower : (13 / 20 : ℝ) * a ^ 2 - 18 * a ≤ b ^ 2 := by nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hquad : 400 * a ≤ a ^ 2 := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)]
  nlinarith

namespace ElementaryCharacterBound

/-- The positivity identity underlying the elementary Euler-product argument. -/
theorem character_positivity {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ 3 + 4 * w.re + (w ^ 2).re := by
  have hs : w.re * w.re + w.im * w.im ≤ 1 := by
    have hnorm : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    simpa only [Complex.sq_norm, Complex.normSq_apply] using hnorm
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (w.re + 1)]

/-- One inverse root's contribution to `z L'(z) / L(z)`. -/
noncomputable def contribution (w : ℂ) : ℂ := -w / (1 - w)

/-- Every nonsingular point in the closed unit disk contributes at most one half. -/
theorem contribution_re_le_half {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) :
    (contribution w).re ≤ 1 / 2 := by
  have hden : 0 < Complex.normSq (1 - w) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hs : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  simp only [contribution, Complex.div_re, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  rw [← add_div, div_le_iff₀ hden]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, zero_sub] at hs ⊢
  nlinarith

/-- The numerical contradiction giving an explicit elementary zero-free radius. -/
theorem inverse_root_numeric_contradiction (H u v : ℝ) (hH : 0 < H)
    (hu : u = 10 * H - 1) (hv : 100 * H / 11 - 1 ≤ v)
    (hpositive : 0 ≤ 3 * u - 4 * v + (5 * H - 9) / 2) : False := by
  nlinarith

/-- The test radius is inside the unit disk and bounded away from zero. -/
theorem test_radius_bounds {H : ℝ} (hH : 1 ≤ H) :
    0 < 1 - 1 / (10 * H) ∧ 1 - 1 / (10 * H) < 1 := by
  have hden : 0 < 10 * H := by positivity
  have hfrac : 0 < 1 / (10 * H) := one_div_pos.mpr hden
  have hsmall : 1 / (10 * H) < 1 := (div_lt_one hden).mpr (by linarith)
  constructor <;> linarith

/-- An inverse root too close to the boundary contradicts Euler-product positivity. -/
theorem normalized_root_numeric_contradiction (H y : ℝ) (hH : 1 ≤ H)
    (hylo : (1 - 1 / (100 * H)) * (1 - 1 / (10 * H)) ≤ y)
    (hyhi : y < 1)
    (hpositive : 0 ≤ 3 * ((1 - 1 / (10 * H)) / (1 - (1 - 1 / (10 * H)))) -
      4 * (y / (1 - y)) + (5 * H - 9) / 2) : False := by
  have hH0 : 0 < H := by linarith
  have hu : (1 - 1 / (10 * H)) / (1 - (1 - 1 / (10 * H))) = 10 * H - 1 := by
    field_simp
    ring
  have hlo : 1 - 11 / (100 * H) ≤ y := by
    have hcalc : (1 - 1 / (100 * H)) * (1 - 1 / (10 * H)) =
        1 - 11 / (100 * H) + 1 / (1000 * H ^ 2) := by ring
    rw [hcalc] at hylo
    have : 0 ≤ 1 / (1000 * H ^ 2) := by positivity
    linarith
  have hv : 100 * H / 11 - 1 ≤ y / (1 - y) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - y)).mpr
    have hmul := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 100 * H)
    have hcancel : 100 * H * (11 / (100 * H)) = 11 :=
      mul_div_cancel₀ 11 (by positivity)
    nlinarith
  exact inverse_root_numeric_contradiction H _ _ hH0 hu hv hpositive

end ElementaryCharacterBound
end Erdos157.Elementary
