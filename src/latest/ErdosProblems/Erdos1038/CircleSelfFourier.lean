import ErdosProblems.Erdos1038.CircleCenteredFourier
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The diagonal centered-arc Fourier energy

This file identifies the diagonal Fourier series `circleArcEnergy Q Q`
with the one-dimensional self-energy used in the circle block.
-/

set_option warningAsError false

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma integral_one_sub_mul_cos_mul {a : ℝ} (ha : a ≠ 0) :
    (∫ t : ℝ in 0..1, (1 - t) * Real.cos (a * t)) =
      (1 - Real.cos a) / a ^ 2 := by
  let F : ℝ → ℝ := fun t ↦
    (1 - t) * Real.sin (a * t) / a - Real.cos (a * t) / a ^ 2
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F ((1 - t) * Real.cos (a * t)) t := by
    intro t _ht
    have harg : HasDerivAt (fun s : ℝ ↦ a * s) a t :=
      by
        convert! (hasDerivAt_id t).const_mul a using 1
        all_goals simp
    have hsin : HasDerivAt (fun s : ℝ ↦ Real.sin (a * s))
        (Real.cos (a * t) * a) t :=
      (Real.hasDerivAt_sin (a * t)).comp t harg
    have hcos : HasDerivAt (fun s : ℝ ↦ Real.cos (a * s))
        (-Real.sin (a * t) * a) t :=
      (Real.hasDerivAt_cos (a * t)).comp t harg
    have honeSub : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t :=
      by
        convert! (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1
        all_goals simp
    have h := (honeSub.mul hsin).div_const a |>.sub (hcos.div_const (a ^ 2))
    convert! h using 1
    all_goals try dsimp [F]
    all_goals field_simp [ha]
    all_goals ring
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * Real.cos (a * t)) volume 0 1 :=
    (by fun_prop : Continuous
      (fun t : ℝ ↦ (1 - t) * Real.cos (a * t))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  simp
  field_simp [ha]
  ring

lemma integral_one_sub_mul_cos_two_positiveFrequency
    {Q : ℝ} (hQ : 0 < Q) (n : ℕ) :
    (∫ t : ℝ in 0..1,
      (1 - t) * Real.cos
        (2 * ((n + 1 : ℕ) : ℝ) * Q * t)) =
      Real.sinc (((n + 1 : ℕ) : ℝ) * Q) ^ 2 / 2 := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmQ : ((n + 1 : ℕ) : ℝ) * Q ≠ 0 :=
    (mul_pos hm hQ).ne'
  rw [integral_one_sub_mul_cos_mul (by positivity :
    2 * ((n + 1 : ℕ) : ℝ) * Q ≠ 0)]
  rw [show 2 * ((n + 1 : ℕ) : ℝ) * Q =
      2 * (((n + 1 : ℕ) : ℝ) * Q) by ring,
    Real.cos_two_mul', Real.sinc_of_ne_zero hmQ]
  have hunit := Real.sin_sq_add_cos_sq (((n + 1 : ℕ) : ℝ) * Q)
  field_simp [hmQ]
  nlinarith

/-! ## Interior Abel self-energy -/

/-- The triangular one-dimensional average of the regularized circle
kernel.  The factor `2 * (1 - t)` is the normalized self-convolution
profile of a centered interval. -/
def circleAbelSelfEnergy (rho Q : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1,
    (2 * (1 - t)) * circleAbelLogKernel rho (2 * Q * t)

private def circleAbelSelfKernelTerm
    (rho Q : ℝ) (n : ℕ) : C(ℝ, ℝ) where
  toFun t :=
    (2 * (1 - t)) *
      (-(rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t)) /
          ((n + 1 : ℕ) : ℝ)))
  continuous_toFun := by fun_prop

private lemma summable_abs_pow_succ_self {rho : ℝ} (hrho : |rho| < 1) :
    Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) := by
  have hgeom := summable_geometric_of_lt_one (abs_nonneg rho) hrho
  exact (hgeom.mul_left |rho|).congr fun n ↦ by
    rw [pow_succ]
    ring

private lemma circleAbelSelfKernelTerm_norm_restrict_le
    {rho Q : ℝ} (n : ℕ) :
    ‖(circleAbelSelfKernelTerm rho Q n).restrict
        (⟨uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖ ≤
      2 * |rho| ^ (n + 1) := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num)
    (pow_nonneg (abs_nonneg rho) _))).2
  intro t
  have ht : t.1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using! t.2
  have hone : |1 - t.1| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.2])]
    linarith [ht.1]
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcos : |Real.cos
      (((n + 1 : ℕ) : ℝ) * (2 * Q * t.1))| ≤ 1 :=
    Real.abs_cos_le_one _
  change
    |(2 * (1 - t.1)) *
      (-(rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t.1)) /
          ((n + 1 : ℕ) : ℝ)))| ≤
      2 * |rho| ^ (n + 1)
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_neg, abs_div, abs_mul, abs_pow, abs_of_pos hm]
  calc
    2 * |1 - t.1| *
          (|rho| ^ (n + 1) *
            |Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t.1))| /
              ((n + 1 : ℕ) : ℝ)) ≤
        2 * 1 * (|rho| ^ (n + 1) * 1 / 1) := by
      gcongr
      norm_num
    _ = 2 * |rho| ^ (n + 1) := by ring

private lemma summable_circleAbelSelfKernelTerm_restrict_norm
    {rho Q : ℝ} (hrho : |rho| < 1) :
    Summable (fun n : ℕ ↦
      ‖(circleAbelSelfKernelTerm rho Q n).restrict
        (⟨uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
  have hmajor : Summable (fun n : ℕ ↦ 2 * |rho| ^ (n + 1)) :=
    (summable_abs_pow_succ_self hrho).mul_left 2
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact circleAbelSelfKernelTerm_norm_restrict_le n

lemma circleAbelSelfEnergy_eq_tsum_integral
    {rho : ℝ} (hrho : |rho| < 1) (Q : ℝ) :
    circleAbelSelfEnergy rho Q =
      ∑' n : ℕ, ∫ t : ℝ in 0..1,
        circleAbelSelfKernelTerm rho Q n t := by
  calc
    circleAbelSelfEnergy rho Q =
        ∫ t : ℝ in 0..1,
          ∑' n : ℕ, circleAbelSelfKernelTerm rho Q n t := by
      unfold circleAbelSelfEnergy
      apply intervalIntegral.integral_congr
      intro t _ht
      change
        (2 * (1 - t)) * circleAbelLogKernel rho (2 * Q * t) =
          ∑' n : ℕ, (2 * (1 - t)) *
            (-(rho ^ (n + 1) *
              Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t)) /
                ((n + 1 : ℕ) : ℝ)))
      rw [circleAbelLogKernel_eq_tsum hrho]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in 0..1,
          circleAbelSelfKernelTerm rho Q n t := by
      have hswap :=
        intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
          (a := (0 : ℝ)) (b := 1)
          (f := fun n : ℕ ↦ circleAbelSelfKernelTerm rho Q n)
          (summable_circleAbelSelfKernelTerm_restrict_norm hrho)
      exact hswap.symm

lemma integral_circleAbelSelfKernelTerm_eq
    (rho : ℝ) {Q : ℝ} (hQ : 0 < Q) (n : ℕ) :
    (∫ t : ℝ in 0..1, circleAbelSelfKernelTerm rho Q n t) =
      -(rho ^ (n + 1) * circleSincTerm Q Q n) := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  change (∫ t : ℝ in 0..1,
    (2 * (1 - t)) *
      (-(rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t)) /
          ((n + 1 : ℕ) : ℝ)))) = _
  rw [show (fun t : ℝ ↦
      (2 * (1 - t)) *
        (-(rho ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * (2 * Q * t)) /
            ((n + 1 : ℕ) : ℝ)))) =
      fun t ↦ (-(2 * rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ))) *
        ((1 - t) * Real.cos
          (2 * ((n + 1 : ℕ) : ℝ) * Q * t)) by
    funext t
    ring_nf]
  rw [intervalIntegral.integral_const_mul,
    integral_one_sub_mul_cos_two_positiveFrequency hQ n]
  unfold circleSincTerm
  field_simp [hm.ne']

/-- In the open unit disk, the triangular Abel self-average equals the
diagonal Abel Fourier energy term by term. -/
theorem circleAbelSelfEnergy_eq_circleAbelArcEnergy
    {rho Q : ℝ} (hrho : |rho| < 1) (hQ : 0 < Q) :
    circleAbelSelfEnergy rho Q = circleAbelArcEnergy rho Q Q := by
  rw [circleAbelSelfEnergy_eq_tsum_integral hrho Q]
  simp_rw [integral_circleAbelSelfKernelTerm_eq rho hQ]
  unfold circleAbelArcEnergy
  rw [← tsum_neg]

/-! ## Passage to the logarithmic boundary -/

lemma circleAbelLogKernel_one_two_mul_eq
    {Q t : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (ht0 : 0 < t) (ht1 : t < 1) :
    circleAbelLogKernel 1 (2 * Q * t) =
      Real.log (2 * Real.sin (Q * t)) := by
  have hQt0 : 0 < Q * t := mul_pos hQ ht0
  have hQtPi : Q * t < Real.pi := calc
    Q * t ≤ Real.pi * t := mul_le_mul_of_nonneg_right hQpi ht0.le
    _ < Real.pi * 1 := mul_lt_mul_of_pos_left ht1 Real.pi_pos
    _ = Real.pi := mul_one _
  have hsin : 0 < Real.sin (Q * t) :=
    Real.sin_pos_of_pos_of_lt_pi hQt0 hQtPi
  unfold circleAbelLogKernel
  rw [Complex.ofReal_one, one_mul, norm_sub_rev]
  rw [show ((2 * Q * t : ℝ) : ℂ) * Complex.I =
      Complex.I * (2 * Q * t : ℝ) by ring,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs,
    show 2 * Q * t / 2 = Q * t by ring,
    abs_of_pos (mul_pos (by norm_num) hsin)]

private lemma coe_two_mul_ne_zero
    {Q t : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ((2 * Q * t : ℝ) : AngleCircle) ≠ 0 := by
  have hu0 : 0 < 2 * Q * t := by positivity
  have huT : 2 * Q * t < 2 * Real.pi := by
    nlinarith [mul_le_mul_of_nonneg_right hQpi ht0.le,
      mul_lt_mul_of_pos_left ht1 Real.pi_pos]
  intro hzero
  have hreal : 2 * Q * t = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := 2 * Real.pi)
      (show 2 * Q * t ∈ Ico (0 : ℝ) (2 * Real.pi) from
        ⟨hu0.le, huT⟩)).mp hzero
  linarith

private lemma circleLogDeficitAt_two_mul_coe_zero_eq
    {Q t : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (ht0 : 0 < t) (ht1 : t < 1) :
    circleLogDeficitAt ((2 * Q * t : ℝ) : AngleCircle) 0 =
      -Real.log (Real.sin (Q * t)) := by
  have hsin : 0 < Real.sin (Q * t) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hQ ht0
    · calc
        Q * t ≤ Real.pi * t :=
          mul_le_mul_of_nonneg_right hQpi ht0.le
        _ < Real.pi * 1 := mul_lt_mul_of_pos_left ht1 Real.pi_pos
        _ = Real.pi := mul_one _
  have hboundary := circleAbelLogKernelOn_one_eq_log_two_sub_deficit
    (x := ((2 * Q * t : ℝ) : AngleCircle))
    (y := (0 : AngleCircle))
    (coe_two_mul_ne_zero hQ hQpi ht0 ht1)
  have hcoord : circleAbelLogKernelOn 1
      ((2 * Q * t : ℝ) : AngleCircle) 0 =
      circleAbelLogKernel 1 (2 * Q * t) := by
    simpa only [AddCircle.coe_zero, sub_zero] using!
      circleAbelLogKernelOn_coe_coe 1 (2 * Q * t) 0
  rw [hcoord, circleAbelLogKernel_one_two_mul_eq hQ hQpi ht0 ht1,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsin.ne'] at hboundary
  linarith

private lemma abs_circleAbelLogKernel_two_mul_le
    {rho Q t : ℝ} (hrhoLower : (1 / 2 : ℝ) ≤ rho)
    (hrhoUpper : rho ≤ 1)
    (hQ : 0 < Q) (hQpi : Q ≤ Real.pi)
    (ht0 : 0 < t) (ht1 : t < 1) :
    |circleAbelLogKernel rho (2 * Q * t)| ≤
      Real.log 2 - Real.log (Real.sin (Q * t)) := by
  have hbound := abs_circleAbelLogKernelOn_le_log_two_add_deficit
    (x := ((2 * Q * t : ℝ) : AngleCircle))
    (y := (0 : AngleCircle))
    hrhoLower hrhoUpper (coe_two_mul_ne_zero hQ hQpi ht0 ht1)
  have hcoord : circleAbelLogKernelOn rho
      ((2 * Q * t : ℝ) : AngleCircle) 0 =
      circleAbelLogKernel rho (2 * Q * t) := by
    simpa only [AddCircle.coe_zero, sub_zero] using!
      circleAbelLogKernelOn_coe_coe rho (2 * Q * t) 0
  rw [hcoord,
    circleLogDeficitAt_two_mul_coe_zero_eq hQ hQpi ht0 ht1] at hbound
  linarith

private def circleSelfDominatingFunction (Q t : ℝ) : ℝ :=
  2 * (Real.log 2 - Real.log (Real.sin (Q * t)))

private lemma intervalIntegrable_circleSelfDominatingFunction
    {Q : ℝ} (hQ : 0 < Q) :
    IntervalIntegrable (circleSelfDominatingFunction Q) volume 0 1 := by
  have hsin := (intervalIntegrable_log_sin
    (a := (0 : ℝ)) (b := Q)).comp_mul_left (c := Q)
  have hsin' : IntervalIntegrable
      (fun t : ℝ ↦ Real.log (Real.sin (Q * t))) volume 0 1 := by
    simpa [Function.comp_apply, hQ.ne'] using! hsin
  have hconst : IntervalIntegrable
      (fun _t : ℝ ↦ Real.log 2) volume 0 1 := intervalIntegrable_const
  exact (hconst.sub hsin').const_mul 2

private lemma measurable_circleAbelLogKernel_real (rho : ℝ) :
    Measurable (circleAbelLogKernel rho) := by
  unfold circleAbelLogKernel
  exact Real.measurable_log.comp
    ((by fun_prop : Continuous (fun u : ℝ ↦
      (1 : ℂ) - (rho : ℂ) * Complex.exp (u * Complex.I))).norm.measurable)

/-- The triangular Abel self-average converges to the logarithmic
self-energy as the Abel radius tends to one from below. -/
theorem tendsto_circleAbelSelfEnergy_one
    {Q : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi) :
    Tendsto (fun rho : ℝ ↦ circleAbelSelfEnergy rho Q)
      (nhdsWithin 1 (Iio 1)) (nhds (circleSelfEnergy Q)) := by
  let mu : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ := fun rho t ↦
    (2 * (1 - t)) * circleAbelLogKernel rho (2 * Q * t)
  let f : ℝ → ℝ := fun t ↦ 2 * circleSelfEnergyIntegrand Q t
  have hnear : Ioi (1 / 2 : ℝ) ∈ nhdsWithin 1 (Iio 1) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  have hDCT : Tendsto
      (fun rho : ℝ ↦ ∫ t, F rho t ∂mu)
      (nhdsWithin 1 (Iio 1))
      (nhds (∫ t, f t ∂mu)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (circleSelfDominatingFunction Q)
    · exact Filter.Eventually.of_forall fun rho ↦
        (by
          have hkernel : Measurable (fun t : ℝ ↦
              circleAbelLogKernel rho (2 * Q * t)) :=
            (measurable_circleAbelLogKernel_real rho).comp (by fun_prop)
          exact ((by fun_prop : Measurable (fun t : ℝ ↦ 2 * (1 - t))).mul
            hkernel).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin, hnear] with
        rho hrhoUpper hrhoLower
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hkernel := abs_circleAbelLogKernel_two_mul_le
        hrhoLower.le hrhoUpper.le hQ hQpi ht.1 ht.2
      have hkernelNonneg :
          0 ≤ Real.log 2 - Real.log (Real.sin (Q * t)) :=
        (abs_nonneg _).trans hkernel
      have hfactor : |2 * (1 - t)| ≤ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      dsimp only [F, circleSelfDominatingFunction]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hfactor hkernel (abs_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 2)
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (f := circleSelfDominatingFunction Q)
        (by norm_num : (0 : ℝ) ≤ 1)).mp
          (intervalIntegrable_circleSelfDominatingFunction hQ)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hxy := coe_two_mul_ne_zero hQ hQpi ht.1 ht.2
      have htendOn := tendsto_circleAbelLogKernelOn_one
        (x := ((2 * Q * t : ℝ) : AngleCircle))
        (y := (0 : AngleCircle)) hxy
      have hcoord (rho : ℝ) : circleAbelLogKernelOn rho
          ((2 * Q * t : ℝ) : AngleCircle) 0 =
          circleAbelLogKernel rho (2 * Q * t) := by
        simpa only [AddCircle.coe_zero, sub_zero] using!
          circleAbelLogKernelOn_coe_coe rho (2 * Q * t) 0
      have htend : Tendsto
          (fun rho : ℝ ↦ circleAbelLogKernel rho (2 * Q * t))
          (nhdsWithin 1 (Iio 1))
          (nhds (Real.log (2 * Real.sin (Q * t)))) := by
        have htendKernel := htendOn.congr'
          (Filter.Eventually.of_forall fun rho ↦ hcoord rho)
        simpa only [hcoord 1,
          circleAbelLogKernel_one_two_mul_eq hQ hQpi ht.1 ht.2] using!
            htendKernel
      have hweighted := htend.const_mul (2 * (1 - t))
      dsimp only [F, f, circleSelfEnergyIntegrand]
      convert! hweighted using 1
      ring_nf
  have hsource (rho : ℝ) :
      (∫ t, F rho t ∂mu) = circleAbelSelfEnergy rho Q := by
    dsimp only [F, mu]
    rw [circleAbelSelfEnergy]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  have htarget : (∫ t, f t ∂mu) = circleSelfEnergy Q := by
    dsimp only [f, mu]
    unfold circleSelfEnergy
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [htarget] at hDCT
  exact hDCT.congr' (Filter.Eventually.of_forall fun rho ↦
    hsource rho)

/-- The diagonal centered-arc Fourier series is exactly the triangular
logarithmic self-energy used in the circle block. -/
theorem circleArcEnergy_self_eq_circleSelfEnergy
    {Q : ℝ} (hQ : 0 < Q) (hQpi : Q ≤ Real.pi) :
    circleArcEnergy Q Q = circleSelfEnergy Q := by
  have hself := tendsto_circleAbelSelfEnergy_one hQ hQpi
  have harc := tendsto_circleAbelArcEnergy_one hQ hQ
  have hnear : Ioi (-1 : ℝ) ∈ nhdsWithin 1 (Iio 1) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  have heq : ∀ᶠ rho in nhdsWithin 1 (Iio 1),
      circleAbelSelfEnergy rho Q = circleAbelArcEnergy rho Q Q := by
    filter_upwards [self_mem_nhdsWithin, hnear] with
      rho hrhoUpper hrhoLower
    exact circleAbelSelfEnergy_eq_circleAbelArcEnergy
      (by
        rw [abs_lt]
        exact ⟨hrhoLower, hrhoUpper⟩)
      hQ
  have harcToSelf : Tendsto
      (fun rho : ℝ ↦ circleAbelArcEnergy rho Q Q)
      (nhdsWithin 1 (Iio 1)) (nhds (circleSelfEnergy Q)) :=
    hself.congr' heq
  exact tendsto_nhds_unique harc harcToSelf

end

end Erdos1038
