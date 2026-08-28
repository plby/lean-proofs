import Wikipedia.HopfProblem.HolomorphicCousinConvolution
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The compactly supported Cauchy--Green integral at infinity

The explicit integral with kernel `u / (1 - w * u)` is analytic on the
reciprocal disc containing zero when the support of its integrand lies in a
bounded disc.  In particular, continuous compactly supported data give an
analytic function near infinity, with value zero at infinity.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The Cauchy--Green integral written in the reciprocal coordinate. -/
def cauchyGreenInfinity (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, u * (1 - w * u)⁻¹ * f w

@[simp] theorem cauchyGreenInfinity_zero (f : ℂ → ℂ) :
    cauchyGreenInfinity f 0 = 0 := by
  simp [cauchyGreenInfinity]

private theorem area_denominator_ne_zero {R : ℝ} (hR : 0 < R)
    {u w : ℂ} (hu : u ∈ ball 0 R⁻¹) (hw : ‖w‖ ≤ R) :
    1 - w * u ≠ 0 := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  have hmul : ‖w * u‖ < 1 := by
    rw [norm_mul]
    calc
      ‖w‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg u)
      _ < R * R⁻¹ := mul_lt_mul_of_pos_left hu' hR
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro heq
  have hwu : w * u = 1 := (sub_eq_zero.mp heq).symm
  simp [hwu] at hmul

private theorem area_denominator_lower_bound {R r : ℝ} (hR : 0 < R)
    {x w : ℂ} (hx : x ∈ ball 0 r) (hw : ‖w‖ ≤ R) :
    1 - R * r ≤ ‖1 - w * x‖ := by
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa using hx)
  have hmul : ‖w * x‖ ≤ R * r := by
    rw [norm_mul]
    exact mul_le_mul hw hx' (norm_nonneg x) hR.le
  calc
    1 - R * r ≤ 1 - ‖w * x‖ := sub_le_sub_left hmul 1
    _ = ‖(1 : ℂ)‖ - ‖w * x‖ := by rw [norm_one]
    _ ≤ ‖1 - w * x‖ := norm_sub_norm_le _ _

private theorem area_reciprocal_kernel_hasDerivAt {w x : ℂ}
    (hne : 1 - w * x ≠ 0) :
    HasDerivAt (fun y : ℂ => y * (1 - w * y)⁻¹)
      (1 / (1 - w * x) ^ 2) x := by
  have hn : HasDerivAt (fun y : ℂ => y) 1 x := hasDerivAt_id x
  have hd : HasDerivAt (fun y : ℂ => 1 - w * y) (-w) x := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id x).const_mul w).const_sub 1
  have hnum : (1 : ℂ) * (1 - w * x) - x * -w = 1 := by ring
  simpa only [Pi.div_apply, hnum, div_eq_mul_inv] using! hn.div hd hne

/-- Differentiation under the area integral, with a support bound. -/
theorem hasDerivAt_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R)
    {u : ℂ} (hu : u ∈ ball 0 R⁻¹) :
    HasDerivAt (cauchyGreenInfinity f)
      ((1 / (Real.pi : ℂ)) * ∫ w : ℂ, (1 / (1 - w * u) ^ 2) * f w) u := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  obtain ⟨r, hur, hrR⟩ := exists_between hu'
  have hsub : ball (0 : ℂ) r ⊆ ball 0 R⁻¹ := ball_subset_ball hrR.le
  have humem : u ∈ ball (0 : ℂ) r := by simpa using hur
  have hd : 0 < 1 - R * r := by
    have hlt : R * r < 1 := by
      calc
        R * r < R * R⁻¹ := mul_lt_mul_of_pos_left hrR hR
        _ = 1 := mul_inv_cancel₀ hR.ne'
    linarith
  have hmeas (x : ℂ) :
      AEStronglyMeasurable (fun w : ℂ => x * (1 - w * x)⁻¹ * f w) volume := by
    apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hint : Integrable (fun w : ℂ => u * (1 - w * u)⁻¹ * f w) := by
    refine (hf.norm.const_mul (‖u‖ * (1 - R * r)⁻¹)).mono' (hmeas u) ?_
    filter_upwards with w
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv]
      gcongr
      exact area_denominator_lower_bound hR humem hwb
  change HasDerivAt (fun x => cauchyGreenInfinity f x) _ u
  simp only [cauchyGreenInfinity]
  apply HasDerivAt.const_mul
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x w : ℂ => (1 / (1 - w * x) ^ 2) * f w)
    (bound := fun w : ℂ => ((1 - R * r) ^ 2)⁻¹ * ‖f w‖)
    (isOpen_ball.mem_nhds humem) (Eventually.of_forall hmeas) hint ?_ ?_ ?_ ?_).2
  · apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv, norm_pow, one_div]
      gcongr
      exact area_denominator_lower_bound hR hx hwb
  · exact hf.norm.const_mul _
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simpa only [hw, mul_zero] using hasDerivAt_const x (0 : ℂ)
    · exact (area_reciprocal_kernel_hasDerivAt
        (area_denominator_ne_zero hR (hsub hx) (hbound w hw))).mul_const (f w)

/-- Integrable data with bounded support give an analytic reciprocal-coordinate integral. -/
theorem analyticOnNhd_cauchyGreenInfinity_of_integrable {f : ℂ → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro u hu
  exact (hasDerivAt_cauchyGreenInfinity hf hR hbound hu).differentiableAt.differentiableWithinAt

/-- Continuous compactly supported data give analyticity on the entire reciprocal disc. -/
theorem analyticOnNhd_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (ball 0 R⁻¹) :=
  analyticOnNhd_cauchyGreenInfinity_of_integrable
    (hf.integrable_of_hasCompactSupport hfc) hR hbound

/-- The reciprocal-coordinate integral is analytic at infinity without choosing a support radius. -/
theorem analyticAt_cauchyGreenInfinity_zero {f : ℂ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    AnalyticAt ℂ (cauchyGreenInfinity f) 0 := by
  obtain ⟨R, hR, hbound⟩ := hfc.isBounded.exists_pos_norm_lt
  exact analyticOnNhd_cauchyGreenInfinity hf hfc hR
    (fun w hw => (hbound w (subset_tsupport f hw)).le) 0 (mem_ball_self (inv_pos.mpr hR))

/-- The reciprocal formula agrees with the actual Cauchy--Green integral off zero.
No regularity assumption is needed for the change of variables itself. -/
theorem cauchyGreenInfinity_inv (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    cauchyGreenInfinity f z⁻¹ = cauchyGreen f z := by
  unfold cauchyGreenInfinity cauchyGreen
  congr 1
  calc
    (∫ w : ℂ, z⁻¹ * (1 - w * z⁻¹)⁻¹ * f w) =
        ∫ w : ℂ, (z - w)⁻¹ * f w := by
      apply integral_congr_ae
      filter_upwards with w
      have hden : 1 - w * z⁻¹ = (z - w) * z⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hz]
      rw [hden, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    _ = ∫ w : ℂ, w⁻¹ * f (z - w) := by
      simpa only [sub_sub_self] using
        integral_sub_left_eq_self (fun w : ℂ => w⁻¹ * f (z - w)) volume z

end Wikipedia.HopfProblem.HolomorphicCousin
