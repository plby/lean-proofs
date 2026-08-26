import ErdosProblems.Erdos421.ZetaPerronContour

/-! # An unconditional finite zeta contour estimate -/

namespace Erdos421

open Complex Set

theorem exists_zetaPerron_rectangle_bound :
    ∃ T₀ > 1, ∀ x t a b H δ : ℝ, 1 ≤ x → 1 / 2 ≤ a → a ≤ b → 0 < H →
      1 - δ ≤ a → b ≤ 1 + δ → T₀ + H ≤ |t| →
      δ ≤ logPowerZeroWidth (|t| + H) / 64 →
      ‖∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((b : ℂ) + y * I)‖ ≤
        4 * Real.pi * x ^ a * ((2 : ℝ) ^ 52 * (Real.log (|t| + H)) ^ 2) +
          2 * (b - a) * (x ^ b * ((2 : ℝ) ^ 52 * (Real.log (|t| + H)) ^ 2) / H ^ 2) := by
  obtain ⟨Tz, hTz, hzero⟩ := riemannZeta_eventually_ne_zero_log_power_strip
  obtain ⟨Td, hTd, hderiv⟩ := riemannZeta_eventually_log_derivative_bound
  let T₀ : ℝ := max Tz Td
  have hT₀ : 1 < T₀ := hTd.trans_le (le_max_right _ _)
  refine ⟨T₀, hT₀, ?_⟩
  intro x t a b H δ hx ha hab hH haδ hbδ ht hδ
  have hbounds : ∀ s ∈ Icc a b ×ℂ Icc (-H) H,
      T₀ ≤ |(s + t * I).im| ∧ |(s + t * I).im| ≤ |t| + H := by
    intro s hs
    have hi : |s.im| ≤ H := abs_le.mpr hs.2
    have hlow : T₀ ≤ |t + s.im| := by
      have h := abs_sub_abs_le_abs_sub t (t + s.im)
      simp only [sub_add_cancel_left, abs_neg] at h
      linarith
    have hhigh : |t + s.im| ≤ |t| + H :=
      (abs_add_le _ _).trans (add_le_add le_rfl hi)
    simpa only [add_im, mul_I_im, ofReal_re, add_comm s.im t] using And.intro hlow hhigh
  have hpole : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, s + t * I ≠ 1 := by
    intro s hs he
    have hl := (hbounds s hs).1
    rw [he, one_im, abs_zero] at hl
    linarith
  have hcontrol : ∀ s ∈ Icc a b ×ℂ Icc (-H) H,
      riemannZeta (s + t * I) ≠ 0 ∧
      ‖logDeriv riemannZeta (s + t * I)‖ ≤ (2 : ℝ) ^ 52 * (Real.log (|t| + H)) ^ 2 := by
    intro s hs
    let w : ℂ := s + t * I
    obtain ⟨hl, hu⟩ := hbounds s hs
    have hw1 : 1 < |w.im| := hT₀.trans_le hl
    have hwp : 0 < |w.im| := by linarith
    have hwidth := logPowerZeroWidth_antitone hw1 hu
    have hδw : δ ≤ logPowerZeroWidth |w.im| / 64 :=
      hδ.trans (div_le_div_of_nonneg_right hwidth (by norm_num))
    have hband : |w.re - 1| ≤ logPowerZeroWidth |w.im| / 64 := by
      have hwr : w.re = s.re := by simp [w]
      rw [hwr]
      apply abs_le.mpr
      constructor <;> linarith [hs.1.1, hs.1.2]
    have hz : riemannZeta w ≠ 0 := by
      have hδfull : δ ≤ logPowerZeroWidth |w.im| := by
        linarith [logPowerZeroWidth_pos hw1]
      have hreal : 1 - logPowerZeroWidth |w.im| ≤ w.re := by
        have hwr : w.re = s.re := by simp [w]
        rw [hwr]
        linarith [hs.1.1]
      have h := hzero w.im w.re ((le_max_left Tz Td).trans hl) hreal
      simpa only [re_add_im] using h
    have hd := hderiv w.im w.re ((le_max_right Tz Td).trans hl) hband
    simp only [re_add_im] at hd
    have hlog : (Real.log |w.im|) ^ 2 ≤ (Real.log (|t| + H)) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg hw1.le) (Real.log_le_log hwp hu) 2
    exact ⟨hz, hd.trans (mul_le_mul_of_nonneg_left hlog (by positivity))⟩
  exact zetaPerronIntegrand_rectangle_bound hx ha hab hH (by positivity) hpole
    (fun s hs ↦ (hcontrol s hs).1) (fun s hs ↦ (hcontrol s hs).2)

end Erdos421
