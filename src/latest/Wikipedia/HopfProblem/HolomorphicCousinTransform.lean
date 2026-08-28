import Wikipedia.HopfProblem.HolomorphicCousinTransformKernel

/-!
# The two analytic branches of a circle Cauchy transform

The Cauchy transform of boundary data is analytic on each component of the
complement of the integration circle. Its exterior branch extends analytically
over infinity and vanishes there. All functions are defined by actual circle
integrals.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology NNReal

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The normalized Cauchy transform of data on the circle of radius `R`. -/
def cauchyTransform (h : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ w in C(0, R), (w - z)⁻¹ * h w

/-- Off the integration circle the Cauchy kernel preserves circle integrability. -/
theorem cauchyKernel_circleIntegrable {h : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hh : CircleIntegrable h 0 R) (hz : ‖z‖ ≠ |R|) :
    CircleIntegrable (fun w => (w - z)⁻¹ * h w) 0 R := by
  apply hh.continuousOn_mul
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro w hw
  apply sub_ne_zero.mpr
  intro he
  change w = z at he
  subst w
  exact hz (by simpa only [mem_sphere, dist_zero_right] using hw)

/-- Only the boundary values contribute to the transform. -/
theorem cauchyTransform_congr {h k : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hhk : EqOn h k (sphere 0 R)) (z : ℂ) :
    cauchyTransform h R z = cauchyTransform k R z := by
  unfold cauchyTransform
  congr 1
  exact circleIntegral.integral_congr hR (fun w hw => by rw [hhk hw])

/-- Circle integrability alone gives analyticity of the interior branch. -/
theorem cauchyTransform_analyticOnNhd_interior {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : CircleIntegrable h 0 R) :
    AnalyticOnNhd ℂ (cauchyTransform h R) (ball 0 R) := by
  let r : ℝ≥0 := ⟨R, hR.le⟩
  have hr : 0 < r := hR
  intro z hz
  have hz' : z ∈ eball (0 : ℂ) (r : ENNReal) := by
    rw [Metric.eball_coe]
    exact hz
  have ha := (hasFPowerSeriesOn_cauchy_integral (R := r) hh hr).analyticAt_of_mem hz'
  change AnalyticAt ℂ
    (fun w => (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ t in C(0, R), (t - w)⁻¹ * h t) z
  convert! ha using 1

/-- The Cauchy kernel in the coordinate `u = z⁻¹` at infinity. -/
theorem cauchyKernel_inv {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    (-z⁻¹) * (1 - w * z⁻¹)⁻¹ = (w - z)⁻¹ := by
  by_cases hw : w = z
  · subst w
    simp [hz]
  · have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
    have hu : 1 - w * z⁻¹ ≠ 0 := by
      intro he
      have he' := (sub_eq_zero.mp he)
      have he'' := congrArg (fun t : ℂ => t * z) he'
      simp only [one_mul, mul_assoc, inv_mul_cancel₀ hz, mul_one] at he''
      exact hw he''.symm
    field_simp
    ring

/-- The reciprocal-coordinate integral is exactly the exterior Cauchy transform. -/
theorem infinityKernel_inv (h : ℂ → ℂ) (R : ℝ) {z : ℂ} (hz : z ≠ 0) :
    infinityKernel h R z⁻¹ = cauchyTransform h R z := by
  have heq : (fun w : ℂ => (-z⁻¹) * (1 - w * z⁻¹)⁻¹ * h w) =
      (fun w : ℂ => (w - z)⁻¹ * h w) := by
    funext w
    rw [cauchyKernel_inv hz]
  unfold infinityKernel cauchyTransform
  rw [heq]

/-- Analyticity of the exterior branch under the circle-integrability hypothesis. -/
theorem cauchyTransform_analyticOnNhd_exterior_of_circleIntegrable
    {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hh : CircleIntegrable h 0 R) :
    AnalyticOnNhd ℂ (cauchyTransform h R) {z | R < ‖z‖} := by
  intro z hz
  have hzpos : 0 < ‖z‖ := hR.trans hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hinv : z⁻¹ ∈ ball 0 R⁻¹ := by
    simp only [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_inv₀ hzpos hR).2 hz
  have ha := ((analyticOnNhd_infinityKernel_of_circleIntegrable hR hh) z⁻¹ hinv).comp
    (analyticAt_inv hz0)
  apply ha.congr
  filter_upwards [eventually_ne_nhds hz0] with w hw
  exact infinityKernel_inv h R hw

/-- Boundary continuity gives an analytic exterior branch. -/
theorem cauchyTransform_analyticOnNhd_exterior {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : ContinuousOn h (sphere 0 R)) :
    AnalyticOnNhd ℂ (cauchyTransform h R) {z | R < ‖z‖} :=
  cauchyTransform_analyticOnNhd_exterior_of_circleIntegrable hR (hh.circleIntegrable hR.le)

/-- The exterior Cauchy transform extends analytically over infinity, with value zero. -/
theorem cauchyTransform_extension_at_infinity_of_circleIntegrable
    {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hh : CircleIntegrable h 0 R) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 R⁻¹) ∧ G 0 = 0 ∧
      ∀ z, R < ‖z‖ → G z⁻¹ = cauchyTransform h R z := by
  refine ⟨infinityKernel h R, analyticOnNhd_infinityKernel_of_circleIntegrable hR hh,
    infinityKernel_zero h R, ?_⟩
  intro z hz
  exact infinityKernel_inv h R (norm_pos_iff.mp (hR.trans hz))

/-- The same extension theorem for continuous boundary data. -/
theorem cauchyTransform_extension_at_infinity {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : ContinuousOn h (sphere 0 R)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 R⁻¹) ∧ G 0 = 0 ∧
      ∀ z, R < ‖z‖ → G z⁻¹ = cauchyTransform h R z :=
  cauchyTransform_extension_at_infinity_of_circleIntegrable hR (hh.circleIntegrable hR.le)

end Wikipedia.HopfProblem.HolomorphicCousin
