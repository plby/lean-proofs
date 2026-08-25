import Mathlib

/-!
# Trigonometric inequalities for the N5 facet obstruction

The two acute angles lie below a quarter turn.  The estimates below separate
the two outgoing-face orientations and identify the necessary thirty-degree
threshold from the source contact bounds.
-/

namespace Puzzling139335.N5Facet

lemma acute_trig_pos {t : ℝ} (ht0 : 0 < t) (ht4 : t < Real.pi / 4) :
    0 < Real.cos t ∧ 0 < Real.sin t := by
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  · exact Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])

lemma suffix_trig_pos {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    0 < Real.cos t ∧ 0 < Real.sin t ∧ 0 < Real.cos ψ ∧ 0 < Real.sin ψ := by
  obtain ⟨hc, hs⟩ := acute_trig_pos ht0 (htψ.trans hψ4)
  obtain ⟨hp, hq⟩ := acute_trig_pos (ht0.trans htψ) hψ4
  exact ⟨hc, hs, hp, hq⟩

lemma sin_lt_cos {t : ℝ} (ht0 : 0 < t) (ht4 : t < Real.pi / 4) :
    Real.sin t < Real.cos t := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith) (by linarith)

lemma sin_lt_other_cos {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    Real.sin t < Real.cos ψ := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith) (by linarith)

lemma cos_add_sin_lt {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    Real.cos t + Real.sin t < Real.cos ψ + Real.sin ψ := by
  obtain ⟨hc, hs, hp, hq⟩ := suffix_trig_pos ht0 htψ hψ4
  have hdouble : Real.sin (2 * t) < Real.sin (2 * ψ) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  rw [Real.sin_two_mul, Real.sin_two_mul] at hdouble
  nlinarith only [hc, hs, hp, hq, hdouble,
    Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq ψ]

lemma suffix_coefficient_pos {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    0 < 1 - Real.sin t * (Real.cos ψ + Real.sin ψ) := by
  obtain ⟨hc, hs, hp, hq⟩ := suffix_trig_pos ht0 htψ hψ4
  have hsc := sin_lt_cos ht0 (htψ.trans hψ4)
  have hm := mul_lt_mul_of_pos_right hsc hp
  have hdot : Real.cos t * Real.cos ψ + Real.sin t * Real.sin ψ ≤ 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq ψ,
      sq_nonneg (Real.cos t - Real.cos ψ), sq_nonneg (Real.sin t - Real.sin ψ)]
  nlinarith only [hm, hdot]

lemma sin_sub_pos {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    0 < Real.sin (ψ - t) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

lemma sqrt_two_mul_sin_lt_cos_sub_sub_sin_sub {t ψ : ℝ}
    (ht0 : 0 < t) (htψ : t < ψ) (hψ4 : ψ < Real.pi / 4) :
    Real.sqrt 2 * Real.sin t < Real.cos (ψ - t) - Real.sin (ψ - t) := by
  have hcos : Real.cos (Real.pi / 4 - t) < Real.cos (ψ - t) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_pos]) (by linarith)
  have hsin : Real.sin (ψ - t) < Real.sin (Real.pi / 4 - t) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith)
  have hid : Real.cos (Real.pi / 4 - t) - Real.sin (Real.pi / 4 - t) =
      Real.sqrt 2 * Real.sin t := by
    rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  linarith

lemma sin_lt_cos_sub_sub_sin_sub {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) :
    Real.sin t < Real.cos (ψ - t) - Real.sin (ψ - t) := by
  have hs := (acute_trig_pos ht0 (htψ.trans hψ4)).2
  have hmul : Real.sin t < Real.sqrt 2 * Real.sin t := by
    nlinarith only [mul_lt_mul_of_pos_right Real.one_lt_sqrt_two hs]
  exact hmul.trans (sqrt_two_mul_sin_lt_cos_sub_sub_sin_sub ht0 htψ hψ4)

lemma sin_lt_two_mul_sin_mul_cos {t ψ : ℝ} (_ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) (ht6 : Real.pi / 6 < t) :
    Real.sin ψ < 2 * Real.sin t * Real.cos t := by
  have h : Real.sin ψ < Real.sin (2 * t) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith [Real.pi_pos])
  simpa only [Real.sin_two_mul] using h

lemma suffix_coefficients_lt {t ψ : ℝ} (ht0 : 0 < t) (htψ : t < ψ)
    (hψ4 : ψ < Real.pi / 4) (ht6 : Real.pi / 6 < t) :
    1 - Real.sin t * (Real.cos ψ + Real.sin ψ) <
      Real.cos t * (Real.cos ψ + Real.sin ψ) - Real.sin ψ := by
  obtain ⟨hc, hs⟩ := acute_trig_pos ht0 (htψ.trans hψ4)
  have hsum := cos_add_sin_lt ht0 htψ hψ4
  have hprod := mul_lt_mul_of_pos_left hsum (show 0 < Real.cos t + Real.sin t by linarith)
  have hdouble := sin_lt_two_mul_sin_mul_cos ht0 htψ hψ4 ht6
  nlinarith only [hprod, hdouble, Real.sin_sq_add_cos_sq t]

lemma contact_threshold_gap {t : ℝ} (ht0 : 0 < t) (ht4 : t < Real.pi / 4) :
    (1 - 1 / (Real.cos t + Real.sin t)) - Real.sin t / (1 + Real.cos t) =
      Real.sin t * (1 - 2 * Real.sin t) /
        ((Real.cos t + Real.sin t) * (1 + Real.cos t)) := by
  obtain ⟨hc, hs⟩ := acute_trig_pos ht0 ht4
  have hcs : Real.cos t + Real.sin t ≠ 0 := by positivity
  have h1c : 1 + Real.cos t ≠ 0 := by positivity
  field_simp
  nlinarith only [Real.sin_sq_add_cos_sq t]

lemma pi_div_six_lt_of_contact_bounds {t b : ℝ} (ht0 : 0 < t)
    (ht4 : t < Real.pi / 4) (_hb0 : 0 < b)
    (hbt : b < Real.sin t / (1 + Real.cos t))
    (hlength : (1 - b) * (Real.cos t + Real.sin t) < 1) :
    Real.pi / 6 < t := by
  obtain ⟨hc, hs⟩ := acute_trig_pos ht0 ht4
  have hcs : 0 < Real.cos t + Real.sin t := by positivity
  have h1c : 0 < 1 + Real.cos t := by positivity
  have hlength' : 1 - b < 1 / (Real.cos t + Real.sin t) :=
    (lt_div_iff₀ hcs).mpr hlength
  have hgap : (1 - 1 / (Real.cos t + Real.sin t)) -
      Real.sin t / (1 + Real.cos t) < 0 := by linarith
  rw [contact_threshold_gap ht0 ht4] at hgap
  have hnum : Real.sin t * (1 - 2 * Real.sin t) < 0 := by
    have := (div_lt_iff₀ (mul_pos hcs h1c)).mp hgap
    simpa only [zero_mul] using this
  have hhalf : 1 / 2 < Real.sin t := by
    have hh : Real.sin t * (1 - 2 * Real.sin t) < Real.sin t * 0 := by
      simpa only [mul_zero] using hnum
    have := lt_of_mul_lt_mul_left hh hs.le
    linarith
  by_contra h
  have hsin : Real.sin t ≤ Real.sin (Real.pi / 6) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (le_of_not_gt h)
  rw [Real.sin_pi_div_six] at hsin
  linarith

lemma contact_lt_remaining_mul_sin {t b : ℝ} (ht0 : 0 < t)
    (ht4 : t < Real.pi / 4) (hbt : b < Real.sin t / (1 + Real.cos t)) :
    b < (1 - b) * Real.sin t := by
  obtain ⟨hc, hs⟩ := acute_trig_pos ht0 ht4
  have hsc := sin_lt_cos ht0 ht4
  have hdiv : Real.sin t / (1 + Real.cos t) < Real.sin t / (1 + Real.sin t) :=
    div_lt_div_of_pos_left hs (by linarith) (by linarith)
  have hbound := (lt_div_iff₀ (show 0 < 1 + Real.sin t by linarith)).mp (hbt.trans hdiv)
  nlinarith only [hbound]

end Puzzling139335.N5Facet
