import Wikipedia.HopfProblem.SpecialPeriodsTauCuspLift

/-!
# Positive-width logarithmic modular lifts

Rescaling the genuine logarithmic coordinate by the cusp width preserves
the analytic correction and its normalization. Clockwise translation by
one width becomes translation by minus one in the constructed modular lift.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

def correctedLogarithmWidth (w : ℝ) (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  s / w + h (Function.Periodic.qParam w s)

theorem correctedLogarithmWidth_eq_correctedLogarithm
    (w : ℝ) (h : ℂ → ℂ) (s : ℂ) :
    correctedLogarithmWidth w h s = correctedLogarithm h (s / w) := by
  simp only [correctedLogarithmWidth, correctedLogarithm, qParam_eq_exponential_div]

theorem correctedLogarithmWidth_exponential (w : ℝ) (h : ℂ → ℂ) (s : ℂ) :
    exponential (correctedLogarithmWidth w h s) =
      Function.Periodic.qParam w s * exponential (h (Function.Periodic.qParam w s)) := by
  rw [correctedLogarithmWidth_eq_correctedLogarithm, correctedLogarithm_exponential,
    ← qParam_eq_exponential_div]

theorem correctedLogarithmWidth_analyticAt (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ}
    (hs : ‖Function.Periodic.qParam w s‖ < r) :
    AnalyticAt ℂ (correctedLogarithmWidth w h) s := by
  have hs' : s / w ∈ CuspFamily.logBase r := by
    rw [CuspFamily.mem_logBase]
    simpa only [qParam_eq_exponential_div] using hs
  have hcomp := (correctedLogarithm_analyticAt hh hs').comp
    (f := fun z : ℂ => z / (w : ℂ))
    (show AnalyticAt ℂ (fun z : ℂ => z / (w : ℂ)) s from analyticAt_id.div_const)
  have hfun : correctedLogarithmWidth w h =
      correctedLogarithm h ∘ (fun z : ℂ => z / (w : ℂ)) :=
    funext (correctedLogarithmWidth_eq_correctedLogarithm w h)
  rw [hfun]
  exact hcomp

theorem correctedLogarithmWidth_analyticOnNhd (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (correctedLogarithmWidth w h)
      {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  fun _ hs => correctedLogarithmWidth_analyticAt w hh hs

theorem div_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    (s - (k : ℂ) * w) / w = s / w - k := by
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  rw [sub_div, mul_div_cancel_right₀ _ hwC]

theorem qParam_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    Function.Periodic.qParam w (s - (k : ℂ) * w) = Function.Periodic.qParam w s := by
  rw [qParam_eq_exponential_div, div_sub_int_mul_width w hw,
    CuspFamily.exponential_sub_int, qParam_eq_exponential_div]

theorem correctedLogarithmWidth_sub_int_mul_width
    (w : ℝ) (hw : w ≠ 0) (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithmWidth w h (s - (k : ℂ) * w) = correctedLogarithmWidth w h s - k := by
  simp only [correctedLogarithmWidth_eq_correctedLogarithm, div_sub_int_mul_width w hw,
    correctedLogarithm_sub_int]

/-- The genuine logarithmic lift for a positive cusp width, with arbitrary
source and target radii and the same normalized analytic correction. -/
theorem exists_simplePole_logarithmic_lift_width (w : ℝ) (hw : 0 < w)
    {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0)
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      h 0 = logarithm (1 / a 0) ∧
      (∀ t ∈ Metric.ball 0 r, exponential (h t) = simplePoleUnit a t) ∧
      ∀ s ∈ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r},
        exponential (correctedLogarithmWidth w h s) =
          simplePoleQ a (Function.Periodic.qParam w s) ∧
        0 < (correctedLogarithmWidth w h s).im ∧
        ‖exponential (correctedLogarithmWidth w h s)‖ < R ∧
        modularJ (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s)) =
          a (Function.Periodic.qParam w s) / Function.Periodic.qParam w s := by
  obtain ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, hτ⟩ :=
    exists_simplePole_logarithmic_lift ha ha0 hR hr₀
  refine ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, ?_⟩
  intro s hs
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  obtain ⟨z, rfl⟩ := mul_right_surjective₀ hwC s
  have hz : z ∈ CuspFamily.logBase r := by
    apply (CuspFamily.mem_logBase r z).mpr
    simpa only [mem_ofPred_eq, qParam_eq_exponential_div,
      mul_div_cancel_right₀ _ hwC] using hs
  simpa only [correctedLogarithmWidth_eq_correctedLogarithm,
    qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using hτ z hz

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
