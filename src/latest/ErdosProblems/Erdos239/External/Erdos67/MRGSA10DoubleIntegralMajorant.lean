import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SecondSecondaryPrimeIntegral

/-!
# Double interval-integral majorants for GS A.10

This file records the elementary Bochner-integral estimate used after the
pointwise tailored Perron bound.  It is deliberately independent of the
arithmetic integrand.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Pull the norm through the two source interval integrals. -/
theorem norm_two_mul_doubleIntervalIntegral_le_doubleIntervalIntegral_norm
    {F : ℝ → ℝ → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hF : Continuous (Function.uncurry F)) :
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
      2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, ‖F alpha beta‖ := by
  have hinner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, F alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF
  have hnormInner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact continuous_norm.comp hF
  have houter : ‖∫ alpha in (0 : ℝ)..eta,
        ∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤
      ∫ alpha in (0 : ℝ)..eta,
        ‖∫ beta in (0 : ℝ)..eta, F alpha beta‖ :=
    intervalIntegral.norm_integral_le_integral_norm heta
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ‖∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤
        ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖ := by
    intro alpha _
    exact intervalIntegral.norm_integral_le_integral_norm heta
  have hmono :
      (∫ alpha in (0 : ℝ)..eta,
        ‖∫ beta in (0 : ℝ)..eta, F alpha beta‖) ≤
      ∫ alpha in (0 : ℝ)..eta,
        ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖ := by
    apply intervalIntegral.integral_mono_on heta
    · exact hinner.norm.intervalIntegrable 0 eta
    · exact hnormInner.intervalIntegrable 0 eta
    · exact hpoint
  calc
    ‖2 * ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ =
        2 * ‖∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖ :=
      mul_le_mul_of_nonneg_left (houter.trans hmono)
        (show (0 : ℝ) ≤ 2 by norm_num)

/-- Pointwise domination of the source integrand may be integrated over the
whole alpha--beta rectangle without introducing any extra constant. -/
theorem norm_two_mul_doubleIntervalIntegral_le_of_pointwise
    {F : ℝ → ℝ → ℂ} {G : ℝ → ℝ → ℝ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G))
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta, ‖F alpha beta‖ ≤ G alpha beta) :
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
      2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, G alpha beta := by
  have hnormInner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact continuous_norm.comp hF
  have hGInner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, G alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hG
  have hdouble :
      (∫ alpha in (0 : ℝ)..eta,
        ∫ beta in (0 : ℝ)..eta, ‖F alpha beta‖) ≤
      ∫ alpha in (0 : ℝ)..eta,
        ∫ beta in (0 : ℝ)..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact hnormInner.intervalIntegrable 0 eta
    · exact hGInner.intervalIntegrable 0 eta
    · intro alpha halpha
      apply intervalIntegral.integral_mono_on heta
      · exact (continuous_norm.comp
          (hF.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 eta
      · exact (hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      · exact hmajor alpha halpha
  exact (norm_two_mul_doubleIntervalIntegral_le_doubleIntervalIntegral_norm
      heta hF).trans
    (mul_le_mul_of_nonneg_left hdouble (show (0 : ℝ) ≤ 2 by norm_num))

/-- Uniform domination on the source square gives its exact area factor. -/
theorem norm_two_mul_doubleIntervalIntegral_le_two_mul_sq_mul
    {F : ℝ → ℝ → ℂ} {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hF : Continuous (Function.uncurry F))
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta, ‖F alpha beta‖ ≤ B) :
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
      2 * eta ^ 2 * B := by
  have h := norm_two_mul_doubleIntervalIntegral_le_of_pointwise
    (F := F) (G := fun _ _ ↦ B) heta hF continuous_const hmajor
  calc
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
        2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, B := h
    _ = 2 * eta ^ 2 * B := by
      simp only [intervalIntegral.integral_const, sub_zero]
      ring

/-- Pointwise errors may be averaged before taking absolute values.  This is
the form used to retain the source factor `X^(1-alpha-beta)` in the Perron
truncation error. -/
theorem norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise
    {P Q : ℝ → ℝ → ℂ} {G : ℝ → ℝ → ℝ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hP : Continuous (Function.uncurry P))
    (hQ : Continuous (Function.uncurry Q))
    (hG : Continuous (Function.uncurry G))
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta) :
    ‖2 * (∫ alpha in 0..eta, ∫ beta in 0..eta, P alpha beta) -
        2 * (∫ alpha in 0..eta, ∫ beta in 0..eta, Q alpha beta)‖ ≤
      2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, G alpha beta := by
  have hPinner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, P alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hP
  have hQinner : Continuous (fun alpha : ℝ ↦
      ∫ beta in (0 : ℝ)..eta, Q alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hQ
  have hEq :
      (∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, (P alpha beta - Q alpha beta)) =
        (∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, P alpha beta) -
        ∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, Q alpha beta := by
    calc
      (∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, (P alpha beta - Q alpha beta)) =
          ∫ alpha in (0 : ℝ)..eta,
            ((∫ beta in (0 : ℝ)..eta, P alpha beta) -
              ∫ beta in (0 : ℝ)..eta, Q alpha beta) := by
        apply intervalIntegral.integral_congr
        intro alpha _
        change (∫ beta in (0 : ℝ)..eta,
            (P alpha beta - Q alpha beta)) =
          (∫ beta in (0 : ℝ)..eta, P alpha beta) -
            ∫ beta in (0 : ℝ)..eta, Q alpha beta
        exact intervalIntegral.integral_sub
          ((hP.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
          ((hQ.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
      _ = _ := intervalIntegral.integral_sub
        (hPinner.intervalIntegrable 0 eta) (hQinner.intervalIntegrable 0 eta)
  have hdiff : Continuous (Function.uncurry (fun alpha beta ↦
      P alpha beta - Q alpha beta)) := hP.sub hQ
  have hbound := norm_two_mul_doubleIntervalIntegral_le_of_pointwise
    (F := fun alpha beta ↦ P alpha beta - Q alpha beta)
    (G := G) heta hdiff hG hmajor
  rw [hEq] at hbound
  simpa only [mul_sub] using hbound

end

end Erdos67.MRHalaszBands
