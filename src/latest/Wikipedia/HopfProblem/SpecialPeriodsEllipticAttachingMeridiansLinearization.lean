import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An actual local deformation of a noncritical analytic coordinate

At a simple zero, the derivative estimate gives a positive disc on which
linear interpolation between the analytic map and its linear part never
meets the central value away from zero. The whole interpolation remains
within distance one half of that value. This constructs the local
deformation used to compare genuine chart meridians with round circles;
no winding number or homotopy classification is assumed.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

/-- Quantitative control on an actual analytic coordinate near its center. -/
structure LinearizationControl (f : ℂ → ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  derivative_ne_zero : deriv f 0 ≠ 0
  continuousOn : ContinuousOn f (Metric.ball 0 radius)
  error : ∀ z : ℂ, ‖z‖ < radius →
    ‖f z - f 0 - deriv f 0 * z‖ ≤ ‖deriv f 0‖ / 2 * ‖z‖
  image_small : ∀ z : ℂ, ‖z‖ < radius → ‖f z - f 0‖ < 1 / 2
  linear_small : ∀ z : ℂ, ‖z‖ < radius → ‖deriv f 0 * z‖ < 1 / 2

/-- The required disc follows from the actual derivative and continuity
estimates of the supplied noncritical analytic function. -/
theorem nonempty_linearizationControl {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) : Nonempty (LinearizationControl f) := by
  have hderiv := hf.differentiableAt.hasDerivAt
  have herr : ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖f z - f 0 - deriv f 0 * z‖ ≤ ‖deriv f 0‖ / 2 * ‖z‖ := by
    simpa only [sub_zero, smul_eq_mul, mul_comm] using
      hderiv.isLittleO.bound (half_pos (norm_pos_iff.mpr hd))
  have hv : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - f 0‖ < 1 / 2 := by
    have h : ContinuousAt (fun z : ℂ => ‖f z - f 0‖) 0 :=
      (hf.continuousAt.sub continuousAt_const).norm
    exact h.eventually (gt_mem_nhds (by simp : ‖f 0 - f 0‖ < (1 / 2 : ℝ)))
  have hl : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv f 0 * z‖ < 1 / 2 := by
    have h : ContinuousAt (fun z : ℂ => ‖deriv f 0 * z‖) 0 :=
      (continuousAt_const.mul continuousAt_id).norm
    exact h.eventually (gt_mem_nhds (by simp : ‖deriv f 0 * (0 : ℂ)‖ < (1 / 2 : ℝ)))
  obtain ⟨r, hr, hs⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_continuousAt.and (herr.and (hv.and hl)))
  refine ⟨{
    radius := r
    radius_pos := hr
    derivative_ne_zero := hd
    continuousOn := ?_
    error := ?_
    image_small := ?_
    linear_small := ?_ }⟩
  · intro z hz
    exact (hs (by simpa only [Metric.mem_ball] using hz)).1.continuousWithinAt
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.1
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.2.1
  · intro z hz
    exact (hs (by simpa only [dist_zero_right] using hz)).2.2.2

/-- A selected positive disc, with all its estimates already proved. -/
def analyticLinearizationControl {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) : LinearizationControl f :=
  Classical.choice (nonempty_linearizationControl hf hd)

/-- The literal straight-line interpolation of the analytic and linear maps. -/
def interpolate (f : ℂ → ℂ) (s : unitInterval) (z : ℂ) : ℂ :=
  (((1 - (s : ℝ) : ℝ) : ℂ) * f z) +
    ((s : ℝ) : ℂ) * (f 0 + deriv f 0 * z)

@[simp] theorem interpolate_zero (f : ℂ → ℂ) (z : ℂ) : interpolate f 0 z = f z := by
  simp [interpolate]

@[simp] theorem interpolate_one (f : ℂ → ℂ) (z : ℂ) :
    interpolate f 1 z = f 0 + deriv f 0 * z := by
  simp [interpolate]

theorem interpolate_sub_linear (f : ℂ → ℂ) (s : unitInterval) (z : ℂ) :
    interpolate f s z - f 0 - deriv f 0 * z =
      (((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0 - deriv f 0 * z)) := by
  simp only [interpolate, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem interpolate_sub_center (f : ℂ → ℂ) (s : unitInterval) (z : ℂ) :
    interpolate f s z - f 0 =
      (((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0)) +
        ((s : ℝ) : ℂ) * (deriv f 0 * z) := by
  simp only [interpolate, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem norm_coe_interval (s : unitInterval) : ‖((s : ℝ) : ℂ)‖ = (s : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.property.1]

private theorem norm_one_sub_coe_interval (s : unitInterval) :
    ‖(((1 - (s : ℝ) : ℝ) : ℂ))‖ = 1 - (s : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr s.property.2)]

namespace LinearizationControl

variable {f : ℂ → ℂ} (D : LinearizationControl f)

/-- The same strict-relative-error control holds throughout the actual
linear interpolation, including both endpoints. -/
theorem interpolate_error (s : unitInterval) {z : ℂ} (hz : ‖z‖ < D.radius) :
    ‖interpolate f s z - f 0 - deriv f 0 * z‖ ≤ ‖deriv f 0‖ / 2 * ‖z‖ := by
  rw [interpolate_sub_linear, norm_mul, norm_one_sub_coe_interval]
  calc
    (1 - (s : ℝ)) * ‖f z - f 0 - deriv f 0 * z‖ ≤
        1 * ‖f z - f 0 - deriv f 0 * z‖ :=
      mul_le_mul_of_nonneg_right (by linarith [s.property.1]) (norm_nonneg _)
    _ ≤ ‖deriv f 0‖ / 2 * ‖z‖ := by simpa only [one_mul] using D.error z hz

/-- No nonzero point of the small coordinate disc crosses the puncture
during the constructed deformation. -/
theorem interpolate_ne_center (s : unitInterval) {z : ℂ}
    (hz : ‖z‖ < D.radius) (hz0 : z ≠ 0) : interpolate f s z ≠ f 0 := by
  intro h
  have he := D.interpolate_error s hz
  rw [h, sub_self, zero_sub, norm_neg, norm_mul] at he
  have hprod : 0 < ‖deriv f 0‖ * ‖z‖ :=
    mul_pos (norm_pos_iff.mpr D.derivative_ne_zero) (norm_pos_iff.mpr hz0)
  nlinarith

/-- The full deformation stays in the fixed small disc about its center. -/
theorem interpolate_norm_le (s : unitInterval) {z : ℂ} (hz : ‖z‖ < D.radius) :
    ‖interpolate f s z - f 0‖ ≤ 1 / 2 := by
  rw [interpolate_sub_center]
  calc
    ‖(((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0)) +
        ((s : ℝ) : ℂ) * (deriv f 0 * z)‖ ≤
      ‖(((1 - (s : ℝ) : ℝ) : ℂ) * (f z - f 0))‖ +
        ‖((s : ℝ) : ℂ) * (deriv f 0 * z)‖ := norm_add_le _ _
    _ = (1 - (s : ℝ)) * ‖f z - f 0‖ + (s : ℝ) * ‖deriv f 0 * z‖ := by
      rw [norm_mul, norm_mul, norm_one_sub_coe_interval, norm_coe_interval]
    _ ≤ (1 - (s : ℝ)) * (1 / 2) + (s : ℝ) * (1 / 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (D.image_small z hz).le
          (sub_nonneg.mpr s.property.2))
        (mul_le_mul_of_nonneg_left (D.linear_small z hz).le s.property.1)
    _ = 1 / 2 := by ring

end LinearizationControl

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
