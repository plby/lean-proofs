import ErdosProblems.Erdos1038.CircleCenteredArcIntegral
import ErdosProblems.Erdos1038.CircleBathtub
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Boundary control for the Abel circle kernel

This file puts the regularized real kernel on `AddCircle (2π)`, proves
its exact coordinate formula, and identifies its boundary value with
`log 2` minus the nonnegative logarithmic deficit away from the diagonal.
-/

set_option warningAsError false

open Metric Set MeasureTheory Filter

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Abel regularization of the logarithmic kernel on the additive circle. -/
def circleAbelLogKernelOn
    (rho : ℝ) (x y : AngleCircle) : ℝ :=
  Real.log ‖(1 : ℂ) -
    (rho : ℂ) * (AddCircle.toCircle (x - y) : ℂ)‖

lemma circleAbelLogKernelOn_coe_coe
    (rho theta phi : ℝ) :
    circleAbelLogKernelOn rho
        (theta : AngleCircle) (phi : AngleCircle) =
      circleAbelLogKernel rho (theta - phi) := by
  unfold circleAbelLogKernelOn circleAbelLogKernel
  rw [← AddCircle.coe_sub, AddCircle.toCircle_apply_mk]
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [div_self htwoPi, one_mul, Circle.coe_exp]

lemma measurable_circleAbelLogKernelOn (rho : ℝ) :
    Measurable (Function.uncurry (circleAbelLogKernelOn rho)) := by
  unfold circleAbelLogKernelOn
  have hcircle : Continuous (fun p : AngleCircle × AngleCircle ↦
      (AddCircle.toCircle (p.1 - p.2) : ℂ)) :=
    (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
      (continuous_fst.sub continuous_snd)
  have hinner : Continuous (fun p : AngleCircle × AngleCircle ↦
      (1 : ℂ) - (rho : ℂ) *
        (AddCircle.toCircle (p.1 - p.2) : ℂ)) :=
    continuous_const.sub (continuous_const.mul hcircle)
  exact Real.measurable_log.comp hinner.norm.measurable

/-- For an interior Abel radius the circle kernel is continuous. -/
theorem continuous_circleAbelLogKernelOn
    {rho : ℝ} (hrho : |rho| < 1) :
    Continuous (Function.uncurry (circleAbelLogKernelOn rho)) := by
  rw [continuous_iff_continuousAt]
  intro p
  let z : Circle := AddCircle.toCircle (p.1 - p.2)
  have harg : (1 : ℂ) - (rho : ℂ) * (z : ℂ) ≠ 0 := by
    intro hzero
    have heq : (1 : ℂ) = (rho : ℂ) * (z : ℂ) :=
      sub_eq_zero.mp hzero
    have hnorm := congrArg norm heq
    rw [norm_one, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at hnorm
    linarith
  have hnorm : ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr harg
  have hcircle : Continuous (fun p : AngleCircle × AngleCircle ↦
      (AddCircle.toCircle (p.1 - p.2) : ℂ)) :=
    (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
      (continuous_fst.sub continuous_snd)
  have hinner : ContinuousAt (fun p : AngleCircle × AngleCircle ↦
      (1 : ℂ) - (rho : ℂ) *
        (AddCircle.toCircle (p.1 - p.2) : ℂ)) p :=
    (continuous_const.sub (continuous_const.mul hcircle)).continuousAt
  unfold circleAbelLogKernelOn Function.uncurry
  have hnormCont : ContinuousAt
      (fun q : AngleCircle × AngleCircle ↦
        ‖(1 : ℂ) - (rho : ℂ) *
          (AddCircle.toCircle (q.1 - q.2) : ℂ)‖) p :=
    hinner.norm
  exact (Real.continuousAt_log hnorm).comp'
    (f := fun q : AngleCircle × AngleCircle ↦
      ‖(1 : ℂ) - (rho : ℂ) *
        (AddCircle.toCircle (q.1 - q.2) : ℂ)‖) hnormCont

private lemma angleCircle_has_centered_representative (z : AngleCircle) :
    ∃ theta : ℝ, theta ∈ Icc (-Real.pi) Real.pi ∧
      (theta : AngleCircle) = z := by
  have hz : z ∈ ((↑) : ℝ → AngleCircle) ''
      Icc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [AddCircle.coe_image_Icc_eq]
    exact mem_univ z
  rcases hz with ⟨theta, htheta, hcoe⟩
  refine ⟨theta, ?_, hcoe⟩
  simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using! htheta

private lemma norm_toCircle_centered_representative
    {theta : ℝ} (htheta : theta ∈ Icc (-Real.pi) Real.pi) :
    ‖((AddCircle.toCircle (theta : AngleCircle) : Circle) : ℂ) - 1‖ =
      2 * Real.sin (|theta| / 2) := by
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have habs : |theta / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change -Real.pi ≤ theta ∧ theta ≤ Real.pi at htheta
    have hthetaAbs : |theta| ≤ Real.pi := abs_le.mpr htheta
    linarith [Real.pi_pos]
  rw [AddCircle.toCircle_apply_mk, div_self htwoPi, one_mul,
    Circle.coe_exp]
  rw [show (theta : ℂ) * Complex.I = Complex.I * theta by ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi habs, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private lemma dist_eq_abs_centered_representative
    {x y : AngleCircle} {theta : ℝ}
    (htheta : theta ∈ Icc (-Real.pi) Real.pi)
    (hcoe : (theta : AngleCircle) = x - y) :
    dist y x = |theta| := by
  rw [dist_eq_norm]
  have hyx : y - x = -(x - y) := by abel
  rw [hyx, norm_neg, ← hcoe]
  exact (AddCircle.norm_coe_eq_abs_iff
    (2 * Real.pi) (by positivity)).2 (by
      rw [abs_of_pos Real.two_pi_pos]
      change -Real.pi ≤ theta ∧ theta ≤ Real.pi at htheta
      have habs : |theta| ≤ Real.pi := abs_le.mpr htheta
      linarith)

/-- The chordal boundary norm is twice the sine of half the intrinsic
circle distance. -/
theorem norm_one_sub_toCircle_eq_two_sin_half_dist
    (x y : AngleCircle) :
    ‖(1 : ℂ) - (AddCircle.toCircle (x - y) : ℂ)‖ =
      2 * Real.sin (dist y x / 2) := by
  obtain ⟨theta, htheta, hcoe⟩ :=
    angleCircle_has_centered_representative (x - y)
  have hdist : dist y x = |theta| :=
    dist_eq_abs_centered_representative htheta hcoe
  rw [hdist, ← hcoe, norm_sub_rev]
  exact norm_toCircle_centered_representative htheta

private lemma norm_one_sub_rho_circle_sq
    (rho : ℝ) (z : Circle) :
    ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ^ 2 =
      (1 - rho) ^ 2 + rho * ‖(1 : ℂ) - (z : ℂ)‖ ^ 2 := by
  have hzNorm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  have hzSq : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ ↦ t ^ 2) hzNorm
    change ‖(z : ℂ)‖ ^ 2 = (1 : ℝ) ^ 2 at hsquare
    rw [Complex.sq_norm, Complex.normSq_apply] at hsquare
    norm_num at hsquare ⊢
    simpa only [pow_two] using! hsquare
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.one_im, zero_mul, sub_zero, zero_sub,
    Complex.mul_im]
  nlinarith [sq_nonneg (1 - rho), sq_nonneg rho]

private lemma half_boundary_norm_le_abel_norm
    {rho : ℝ} (hrhoLower : (1 / 2 : ℝ) ≤ rho)
    (z : Circle) :
    ‖(1 : ℂ) - (z : ℂ)‖ / 2 ≤
      ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ := by
  have hidentity := norm_one_sub_rho_circle_sq rho z
  have hleft : 0 ≤ ‖(1 : ℂ) - (z : ℂ)‖ / 2 := by positivity
  have hright : 0 ≤ ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ := norm_nonneg _
  have hsquare :
      (‖(1 : ℂ) - (z : ℂ)‖ / 2) ^ 2 ≤
        ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ^ 2 := by
    rw [hidentity]
    nlinarith [sq_nonneg (1 - rho),
      sq_nonneg ‖(1 : ℂ) - (z : ℂ)‖]
  nlinarith

private lemma abel_norm_le_two
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (z : Circle) :
    ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ≤ 2 := by
  calc
    ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ≤
        ‖(1 : ℂ)‖ + ‖(rho : ℂ) * (z : ℂ)‖ := norm_sub_le _ _
    _ = 1 + |rho| := by
      rw [norm_one, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    _ = 1 + rho := by rw [abs_of_nonneg hrho0]
    _ ≤ 2 := by linarith

/-- Uniform integrable domination of the Abel kernel away from the
diagonal, valid throughout the final half of the radial approach. -/
theorem abs_circleAbelLogKernelOn_le_log_two_add_deficit
    {rho : ℝ} (hrhoLower : (1 / 2 : ℝ) ≤ rho)
    (hrhoUpper : rho ≤ 1) {x y : AngleCircle} (hxy : x ≠ y) :
    |circleAbelLogKernelOn rho x y| ≤
      Real.log 2 + circleLogDeficitAt x y := by
  have hrho0 : 0 ≤ rho := le_trans (by norm_num) hrhoLower
  have hdist0 : 0 < dist y x := dist_pos.mpr hxy.symm
  have hdistPi : dist y x ≤ Real.pi := addCircle_dist_le_pi x y
  have hsin : 0 < Real.sin (dist y x / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · linarith [Real.pi_pos]
  let z : Circle := AddCircle.toCircle (x - y)
  have hlowerNorm : Real.sin (dist y x / 2) ≤
      ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ := by
    have hhalf := half_boundary_norm_le_abel_norm hrhoLower z
    rw [show ‖(1 : ℂ) - (z : ℂ)‖ =
        2 * Real.sin (dist y x / 2) by
      exact norm_one_sub_toCircle_eq_two_sin_half_dist x y] at hhalf
    linarith
  have hupperNorm : ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ ≤ 2 :=
    abel_norm_le_two hrho0 hrhoUpper z
  have hnormPos : 0 < ‖(1 : ℂ) - (rho : ℂ) * (z : ℂ)‖ :=
    lt_of_lt_of_le hsin hlowerNorm
  have hlowerLog : Real.log (Real.sin (dist y x / 2)) ≤
      circleAbelLogKernelOn rho x y := by
    unfold circleAbelLogKernelOn
    exact Real.strictMonoOn_log.monotoneOn hsin hnormPos hlowerNorm
  have hupperLog : circleAbelLogKernelOn rho x y ≤ Real.log 2 := by
    unfold circleAbelLogKernelOn
    exact Real.strictMonoOn_log.monotoneOn hnormPos (by norm_num) hupperNorm
  have hdeficit0 := circleLogDeficitAt_nonneg x y
  have hnegLog : 0 ≤ -Real.log (Real.sin (dist y x / 2)) := by
    simpa only [circleLogDeficitAt] using! hdeficit0
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold circleLogDeficitAt
  rw [abs_le]
  constructor <;> linarith

/-- At distinct points, the boundary Abel kernel is exactly `log 2`
minus the circle deficit. -/
theorem circleAbelLogKernelOn_one_eq_log_two_sub_deficit
    {x y : AngleCircle} (hxy : x ≠ y) :
    circleAbelLogKernelOn 1 x y =
      Real.log 2 - circleLogDeficitAt x y := by
  obtain ⟨theta, htheta, hcoe⟩ :=
    angleCircle_has_centered_representative (x - y)
  have htheta0 : theta ≠ 0 := by
    intro hzero
    apply hxy
    have hsub : x - y = 0 := by
      simpa [hzero] using! hcoe.symm
    exact sub_eq_zero.mp hsub
  have habs0 : 0 < |theta| := abs_pos.mpr htheta0
  have habsPi : |theta| ≤ Real.pi := by
    rw [abs_le]
    exact htheta
  have hsin : 0 < Real.sin (|theta| / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · linarith [Real.pi_pos]
  have hnorm :
      ‖(1 : ℂ) -
          (AddCircle.toCircle (x - y) : ℂ)‖ =
        2 * Real.sin (|theta| / 2) := by
    rw [← hcoe]
    rw [norm_sub_rev]
    exact norm_toCircle_centered_representative htheta
  have hdist : dist y x = |theta| :=
    dist_eq_abs_centered_representative htheta hcoe
  unfold circleAbelLogKernelOn circleLogDeficitAt
  rw [Complex.ofReal_one, one_mul]
  change Real.log ‖(1 : ℂ) -
      (AddCircle.toCircle (x - y) : ℂ)‖ =
    Real.log 2 - -Real.log (Real.sin (dist y x / 2))
  rw [hnorm, hdist, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsin.ne']
  ring

/-- Pointwise convergence of the circle Abel kernel at every
off-diagonal pair. -/
theorem tendsto_circleAbelLogKernelOn_one
    {x y : AngleCircle} (hxy : x ≠ y) :
    Tendsto (fun rho : ℝ ↦ circleAbelLogKernelOn rho x y)
      (nhdsWithin 1 (Iio 1))
      (nhds (circleAbelLogKernelOn 1 x y)) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hcircle : AddCircle.toCircle (x - y) ≠ 1 := by
    intro h
    apply hsub
    apply AddCircle.injective_toCircle (T := 2 * Real.pi)
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    simpa only [AddCircle.toCircle_zero] using! h
  have hcircleComplex :
      (AddCircle.toCircle (x - y) : ℂ) ≠ 1 := by
    intro h
    apply hcircle
    exact Subtype.ext h
  have harg : (1 : ℂ) -
      (1 : ℂ) * (AddCircle.toCircle (x - y) : ℂ) ≠ 0 := by
    simp only [one_mul]
    exact sub_ne_zero.mpr hcircleComplex.symm
  have hnorm : ‖(1 : ℂ) -
      (1 : ℂ) * (AddCircle.toCircle (x - y) : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr harg
  have hcont : ContinuousAt
      (fun rho : ℝ ↦ circleAbelLogKernelOn rho x y) 1 := by
    unfold circleAbelLogKernelOn
    have hinner : ContinuousAt (fun rho : ℝ ↦
        (1 : ℂ) - (rho : ℂ) *
          (AddCircle.toCircle (x - y) : ℂ)) 1 := by
      fun_prop
    have hnormCont : ContinuousAt (fun rho : ℝ ↦
        ‖(1 : ℂ) - (rho : ℂ) *
          (AddCircle.toCircle (x - y) : ℂ)‖) 1 :=
      hinner.norm
    exact (Real.continuousAt_log hnorm).comp'
      (f := fun rho : ℝ ↦
        ‖(1 : ℂ) - (rho : ℂ) *
          (AddCircle.toCircle (x - y) : ℂ)‖) hnormCont
  exact tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto

end

end Erdos1038
