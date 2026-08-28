import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The Cauchy kernel in the reciprocal coordinate

The integral with kernel `-u / (1 - w * u)` is holomorphic for
`‖u‖ < R⁻¹` and vanishes at zero.  The proof differentiates the actual
contour integral, using a uniform positive lower bound for its denominator.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology Interval

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The exterior Cauchy transform written in the coordinate `u = z⁻¹`. -/
def infinityKernel (h : ℂ → ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ w in C(0, R), (-u) * (1 - w * u)⁻¹ * h w

@[simp] theorem infinityKernel_zero (h : ℂ → ℂ) (R : ℝ) :
    infinityKernel h R 0 = 0 := by
  simp [infinityKernel, circleIntegral]

private theorem denominator_ne_zero {R : ℝ} (hR : 0 < R)
    {u w : ℂ} (hu : u ∈ ball 0 R⁻¹) (hw : w ∈ sphere 0 R) :
    1 - w * u ≠ 0 := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  have hw' : ‖w‖ = R := by simpa using hw
  have hmul : ‖w * u‖ < 1 := by
    rw [norm_mul, hw']
    calc
      R * ‖u‖ < R * R⁻¹ := mul_lt_mul_of_pos_left hu' hR
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro heq
  have hwu : w * u = 1 := (sub_eq_zero.mp heq).symm
  simp [hwu] at hmul

private theorem denominator_lower_bound {R r : ℝ} (hR : 0 < R)
    {x w : ℂ} (hx : x ∈ ball 0 r) (hw : w ∈ sphere 0 R) :
    1 - R * r ≤ ‖1 - w * x‖ := by
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa using hx)
  have hw' : ‖w‖ = R := by simpa using hw
  calc
    1 - R * r ≤ 1 - R * ‖x‖ := by gcongr
    _ = ‖(1 : ℂ)‖ - ‖w * x‖ := by rw [norm_one, norm_mul, hw']
    _ ≤ ‖1 - w * x‖ := norm_sub_norm_le _ _

private theorem reciprocal_kernel_hasDerivAt {w x : ℂ} (hne : 1 - w * x ≠ 0) :
    HasDerivAt (fun y : ℂ => -y * (1 - w * y)⁻¹)
      ((-1 : ℂ) / (1 - w * x) ^ 2) x := by
  have hn : HasDerivAt (fun y : ℂ => -y) (-1) x := (hasDerivAt_id x).neg
  have hd : HasDerivAt (fun y : ℂ => 1 - w * y) (-w) x := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id x).const_mul w).const_sub 1
  have hnum : (-1 : ℂ) * (1 - w * x) - -x * -w = -1 := by ring
  simpa only [Pi.div_apply, hnum, div_eq_mul_inv] using! hn.div hd hne

/-- Differentiation of the reciprocal-coordinate contour integral. -/
theorem hasDerivAt_infinityKernel {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : CircleIntegrable h 0 R) {u : ℂ} (hu : u ∈ ball 0 R⁻¹) :
    HasDerivAt (infinityKernel h R)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ w in C(0, R), ((-1 : ℂ) / (1 - w * u) ^ 2) * h w) u := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  obtain ⟨r, hur, hrR⟩ := exists_between hu'
  have hsub : ball (0 : ℂ) r ⊆ ball 0 R⁻¹ := ball_subset_ball hrR.le
  have hd : 0 < 1 - R * r := by
    have hlt : R * r < 1 := by
      calc
        R * r < R * R⁻¹ := mul_lt_mul_of_pos_left hrR hR
        _ = 1 := mul_inv_cancel₀ hR.ne'
    linarith
  have hcircle (θ : ℝ) : circleMap 0 R θ ∈ sphere 0 R := by
    simp [norm_circleMap_zero, abs_of_pos hR]
  have hgm : AEStronglyMeasurable (fun θ => h (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * Real.pi))) :=
    (intervalIntegrable_iff.mp hh).aestronglyMeasurable
  have hcont : ContinuousOn (fun w : ℂ => -u * (1 - w * u)⁻¹)
      (sphere 0 |R|) := by
    have hc : ContinuousOn (fun w : ℂ => 1 - w * u) (sphere 0 |R|) :=
      continuousOn_const.sub (continuousOn_id.mul_const u)
    refine continuousOn_const.mul (hc.inv₀ ?_)
    intro w hw
    exact denominator_ne_zero hR hu (by simpa only [abs_of_pos hR] using hw)
  have hint : CircleIntegrable (fun w : ℂ => -u * (1 - w * u)⁻¹ * h w) 0 R :=
    hh.continuousOn_mul hcont
  change HasDerivAt (fun x => infinityKernel h R x) _ u
  simp only [infinityKernel, circleIntegral, deriv_circleMap, smul_eq_mul]
  apply HasDerivAt.const_mul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ => (circleMap 0 R θ * Complex.I) *
      (((-1 : ℂ) / (1 - circleMap 0 R θ * x) ^ 2) * h (circleMap 0 R θ)))
    (bound := fun θ => R * ((1 - R * r) ^ 2)⁻¹ * ‖h (circleMap 0 R θ)‖)
    (isOpen_ball.mem_nhds (by simpa using hur : u ∈ ball 0 r))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x
    simp only [← mul_assoc]
    apply AEStronglyMeasurable.mul _ hgm
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · simpa only [deriv_circleMap, smul_eq_mul, mul_assoc] using hint.out
  · simp only [← mul_assoc]
    apply AEStronglyMeasurable.mul _ hgm
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with θ _ x hx
    simp only [norm_mul, norm_div, norm_neg, norm_one, norm_I,
      norm_circleMap_zero, abs_of_pos hR, norm_pow, one_div, mul_assoc, one_mul]
    gcongr
    exact denominator_lower_bound hR hx (hcircle θ)
  · exact hh.norm.const_mul _
  · filter_upwards with θ _ x hx
    have hk := reciprocal_kernel_hasDerivAt
      (denominator_ne_zero hR (hsub hx) (hcircle θ))
    simpa only [mul_assoc] using
      (hk.const_mul (circleMap 0 R θ * Complex.I)).mul_const (h (circleMap 0 R θ))

/-- Circle integrability suffices for holomorphy of the reciprocal-coordinate kernel. -/
theorem analyticOnNhd_infinityKernel_of_circleIntegrable {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : CircleIntegrable h 0 R) :
    AnalyticOnNhd ℂ (infinityKernel h R) (ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro u hu
  exact (hasDerivAt_infinityKernel hR hh hu).differentiableAt.differentiableWithinAt

/-- Boundary continuity gives a holomorphic kernel on the reciprocal disc. -/
theorem analyticOnNhd_infinityKernel {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : ContinuousOn h (sphere 0 R)) :
    AnalyticOnNhd ℂ (infinityKernel h R) (ball 0 R⁻¹) :=
  analyticOnNhd_infinityKernel_of_circleIntegrable hR (hh.circleIntegrable hR.le)

end Wikipedia.HopfProblem.HolomorphicCousin
