import Mathlib

/-!
# The short horizontal span for nearby straddling face normals

These lemmas use only scalar supporting-strip and coordinate inequalities.
In particular, the nonnegativity of the common excess and its upper bounds
on both gap coefficients are conclusions, not extra assumptions.
-/

namespace Puzzling139335.TwoSideFaces

/-- The two crossed strip bounds control the gap coefficients, including the
endpoint case where the normal dot product is exactly one half. -/
theorem crossed_gap_bounds (a b C lam mu : ℝ)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hC : 1 / 2 ≤ C)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + C * mu ≤ b - C * (1 - 2 * a))
    (h₂ : C * lam + mu ≤ a - C * (1 - 2 * b)) :
    0 ≤ a + b - 1 / 2 ∧
      lam ≤ a + b - 1 / 2 ∧ mu ≤ a + b - 1 / 2 := by
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hl : 0 ≤ 1 - 2 * a := by linarith only [ha]
  have hr : 0 ≤ 1 - 2 * b := by linarith only [hb]
  have hCl := mul_le_mul_of_nonneg_right hC hl
  have hCr := mul_le_mul_of_nonneg_right hC hr
  have hClam := mul_nonneg hC0 hlam
  have hCmu := mul_nonneg hC0 hmu
  have hlam' : lam ≤ a + b - 1 / 2 := by
    nlinarith only [h₁, hCl, hCmu]
  have hmu' : mu ≤ a + b - 1 / 2 := by
    nlinarith only [h₂, hCr, hClam]
  exact ⟨le_trans hlam hlam', hlam', hmu'⟩

/-- The reversed source-face order has the same gap-coefficient bounds. -/
theorem reversed_crossed_gap_bounds (a b C lam mu : ℝ)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hC : 1 / 2 ≤ C)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + C * mu ≤ a - C * (1 - 2 * b))
    (h₂ : C * lam + mu ≤ b - C * (1 - 2 * a)) :
    0 ≤ a + b - 1 / 2 ∧
      lam ≤ a + b - 1 / 2 ∧ mu ≤ a + b - 1 / 2 := by
  have hh := crossed_gap_bounds a b C mu lam ha hb hC hmu hlam
    (by linarith only [h₂]) (by linarith only [h₁])
  exact ⟨hh.1, hh.2.2, hh.2.1⟩

/-- The rational span estimate is strictly below one once the gap
coefficients satisfy their proved common upper bound. -/
theorem horizontal_span_lt_one (c s d q a b lam mu : ℝ)
    (hc : 0 < c) (hc_one : c ≤ 1) (hs : 0 < s) (hs_one : s < 1)
    (hd : 0 < d) (hd_one : d ≤ 1) (hq : 0 < q) (hq_one : q < 1)
    (ha_width : a * (1 + s) ≤ c) (hb_width : b * (1 + q) ≤ d)
    (heps : 0 ≤ a + b - 1 / 2)
    (hlam : lam ≤ a + b - 1 / 2) (hmu : mu ≤ a + b - 1 / 2) :
    (1 - 2 * b) * s / (2 * c) + (1 - 2 * a) * q / (2 * d) +
      lam * s + mu * q < 1 := by
  let ε : ℝ := a + b - 1 / 2
  have hε : 0 ≤ ε := heps
  have h1s : 0 < 1 + s := by linarith only [hs]
  have h1q : 0 < 1 + q := by linarith only [hq]
  have hsc : s ≤ s / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hc_one hs.le]
  have hqd : q ≤ q / d := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hd_one hq.le]
  have hbracket : 0 ≤ s / c + q / d - s - q := by
    linarith only [hsc, hqd]
  have hpenalty := mul_nonneg hε hbracket
  have hlams : lam * s ≤ ε * s := mul_le_mul_of_nonneg_right hlam hs.le
  have hmuq : mu * q ≤ ε * q := mul_le_mul_of_nonneg_right hmu hq.le
  have hrewrite :
      (1 - 2 * b) * s / (2 * c) + (1 - 2 * a) * q / (2 * d) +
        ε * s + ε * q =
      a * s / c + b * q / d - ε * (s / c + q / d - s - q) := by
    dsimp [ε]
    field_simp [ne_of_gt hc, ne_of_gt hd]
    ring
  have hspan :
      (1 - 2 * b) * s / (2 * c) + (1 - 2 * a) * q / (2 * d) +
        lam * s + mu * q ≤ a * s / c + b * q / d := by
    linarith only [hlams, hmuq, hrewrite, hpenalty]
  have has : a * s / c ≤ s / (1 + s) := by
    apply (div_le_div_iff₀ hc h1s).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ha_width hs.le]
  have hbq : b * q / d ≤ q / (1 + q) := by
    apply (div_le_div_iff₀ hd h1q).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb_width hq.le]
  have hsfrac : s / (1 + s) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ h1s).mpr
    linarith only [hs_one]
  have hqfrac : q / (1 + q) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ h1q).mpr
    linarith only [hq_one]
  linarith only [hspan, has, hbq, hsfrac, hqfrac]

/-- Scalar impossibility for the natural source-face association when
the normal dot product is at least one half. -/
theorem nearby_straddle_impossible (c s d q a b C lam mu : ℝ)
    (hc : 0 < c) (hc_one : c ≤ 1) (hs : 0 < s) (hs_one : s < 1)
    (hd : 0 < d) (hd_one : d ≤ 1) (hq : 0 < q) (hq_one : q < 1)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hC : 1 / 2 ≤ C)
    (ha_width : a * (1 + s) ≤ c) (hb_width : b * (1 + q) ≤ d)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + C * mu ≤ b - C * (1 - 2 * a))
    (h₂ : C * lam + mu ≤ a - C * (1 - 2 * b))
    (hspan : 1 ≤ (1 - 2 * b) * s / (2 * c) +
      (1 - 2 * a) * q / (2 * d) + lam * s + mu * q) : False := by
  obtain ⟨heps, hlam', hmu'⟩ := crossed_gap_bounds a b C lam mu ha hb hC hlam hmu h₁ h₂
  have hh := horizontal_span_lt_one c s d q a b lam mu
    hc hc_one hs hs_one hd hd_one hq hq_one ha_width hb_width heps hlam' hmu'
  exact (not_lt_of_ge hspan) hh

/-- Scalar impossibility for reversed straddling faces with the same
inclusive dot-product bound. No separate half-cosine bounds are needed. -/
theorem reversed_nearby_straddle_impossible (c s d q a b C lam mu : ℝ)
    (hc : 0 < c) (hc_one : c ≤ 1) (hs : 0 < s) (hs_one : s < 1)
    (hd : 0 < d) (hd_one : d ≤ 1) (hq : 0 < q) (hq_one : q < 1)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hC : 1 / 2 ≤ C)
    (ha_width : a * (1 + q) ≤ d) (hb_width : b * (1 + s) ≤ c)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h₁ : lam + C * mu ≤ a - C * (1 - 2 * b))
    (h₂ : C * lam + mu ≤ b - C * (1 - 2 * a))
    (hspan : 1 ≤ (1 - 2 * b) * q / (2 * d) +
      (1 - 2 * a) * s / (2 * c) + lam * q + mu * s) : False := by
  obtain ⟨heps, hlam', hmu'⟩ :=
    reversed_crossed_gap_bounds a b C lam mu ha hb hC hlam hmu h₁ h₂
  have hh := horizontal_span_lt_one d q c s a b lam mu
    hd hd_one hq hq_one hc hc_one hs hs_one ha_width hb_width heps hlam' hmu'
  exact (not_lt_of_ge hspan) hh

end Puzzling139335.TwoSideFaces
