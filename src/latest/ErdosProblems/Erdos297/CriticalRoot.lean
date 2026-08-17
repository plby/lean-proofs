/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement

/-!
# Erdős Problem 297: the unique critical parameter

This file proves, independently of the counting argument, that the integral
equation defining the sharp exponent has a unique positive solution.  The
only delicate endpoint is `x = 0`; there the flat function
`expNegInvGlue` supplies the continuous extension of
`exp (-lam / x) / x`.
-/

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Erdos297

noncomputable section

private def criticalScaledGlue (lam x : ℝ) : ℝ :=
  expNegInvGlue (x / lam)

private def criticalScaledGlueDiv (lam x : ℝ) : ℝ :=
  lam⁻¹ * ((x / lam)⁻¹ * expNegInvGlue (x / lam))

private theorem continuous_criticalScaledGlue (lam : ℝ) :
    Continuous (criticalScaledGlue lam) := by
  have hglue : Continuous expNegInvGlue := by
    simpa using
      (expNegInvGlue.continuous_polynomial_eval_inv_mul (1 : Polynomial ℝ))
  exact hglue.comp (continuous_id.div_const lam)

private theorem continuous_criticalScaledGlueDiv (lam : ℝ) :
    Continuous (criticalScaledGlueDiv lam) := by
  have hflat : Continuous (fun y : ℝ ↦ y⁻¹ * expNegInvGlue y) := by
    simpa using
      (expNegInvGlue.continuous_polynomial_eval_inv_mul
        (Polynomial.X : Polynomial ℝ))
  exact continuous_const.mul (hflat.comp (continuous_id.div_const lam))

private theorem criticalScaledGlue_nonneg (lam x : ℝ) :
    0 ≤ criticalScaledGlue lam x :=
  expNegInvGlue.nonneg _

private theorem critical_selectionProbability_eq_scaledGlue
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    selectionProbability lam x =
      criticalScaledGlue lam x / (1 + criticalScaledGlue lam x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [selectionProbability, criticalScaledGlue]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hquot : 0 < x / lam := div_pos hxpos hlam
    simp only [selectionProbability, hx0, if_false, criticalScaledGlue,
      expNegInvGlue, if_neg (not_le.mpr hquot)]
    rw [show lam / x = -(-lam / x) by ring, Real.exp_neg]
    have hexp : Real.exp (-lam / x) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring

private theorem critical_momentKernel_eq_scaledGlue
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    momentKernel lam x =
      criticalScaledGlueDiv lam x / (1 + criticalScaledGlue lam x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [momentKernel, criticalScaledGlueDiv, criticalScaledGlue]
  · rw [momentKernel, if_neg hx0,
      critical_selectionProbability_eq_scaledGlue hlam hx]
    have hlam0 : lam ≠ 0 := ne_of_gt hlam
    have hnum :
        criticalScaledGlueDiv lam x = criticalScaledGlue lam x / x := by
      simp only [criticalScaledGlueDiv, criticalScaledGlue, div_eq_mul_inv]
      field_simp
    rw [hnum]
    ring

/-- The flat endpoint extension makes the moment kernel continuous in `x`
on the closed unit interval whenever the parameter is positive. -/
theorem criticalRoot_continuousOn_momentKernel {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (momentKernel lam) (Icc 0 1) := by
  have hden : Continuous (fun x ↦ 1 + criticalScaledGlue lam x) :=
    continuous_const.add (continuous_criticalScaledGlue lam)
  have hrepr : Continuous
      (fun x ↦ criticalScaledGlueDiv lam x /
        (1 + criticalScaledGlue lam x)) :=
    (continuous_criticalScaledGlueDiv lam).div hden fun x ↦ by
      exact ne_of_gt (by linarith [criticalScaledGlue_nonneg lam x])
  exact hrepr.continuousOn.congr fun x hx ↦
    critical_momentKernel_eq_scaledGlue hlam hx.1

private theorem criticalRoot_intervalIntegral_eq_moment (lam : ℝ) :
    (∫ x in (0 : ℝ)..1, momentKernel lam x) = moment lam := by
  rw [moment, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

private theorem criticalRoot_momentKernel_nonneg
    {lam x : ℝ} (_hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    0 ≤ momentKernel lam x := by
  by_cases hx0 : x = 0
  · subst x
    simp [momentKernel]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    simp only [momentKernel, hx0, if_false, selectionProbability]
    positivity

private theorem criticalRoot_momentKernel_le_inv
    {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Icc (0 : ℝ) 1) :
    momentKernel lam x ≤ lam⁻¹ := by
  by_cases hx0 : x = 0
  · subst x
    simp [momentKernel, hlam.le]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hzexp : lam / x ≤ Real.exp (lam / x) := by
      calc
        lam / x ≤ lam / x + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ Real.exp (lam / x) := Real.add_one_le_exp _
    have hden : lam ≤ x * (1 + Real.exp (lam / x)) := by
      calc
        lam = x * (lam / x) := by field_simp
        _ ≤ x * Real.exp (lam / x) :=
          mul_le_mul_of_nonneg_left hzexp hxpos.le
        _ ≤ x * (1 + Real.exp (lam / x)) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left zero_le_one) hxpos.le
    simp only [momentKernel, hx0, if_false, selectionProbability,
      div_eq_mul_inv]
    have hrearrange :
        (1 + Real.exp (lam * x⁻¹))⁻¹ * x⁻¹ =
          (x * (1 + Real.exp (lam / x)))⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, mul_comm]
    rw [one_mul, hrearrange]
    exact inv_anti₀ hlam hden

private theorem criticalRoot_intervalIntegrable_momentKernel
    {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (momentKernel lam) volume 0 1 :=
  (criticalRoot_continuousOn_momentKernel hlam).intervalIntegrable_of_Icc
    zero_le_one

/-- The moment depends continuously on the positive parameter.  The proof
uses a parameter-local lower bound for `lam`, hence a constant integrable
dominator on `[0,1]`. -/
theorem criticalRoot_continuousOn_moment {a b : ℝ} (ha : 0 < a) :
    ContinuousOn moment (Icc a b) := by
  have hparam : ContinuousOn
      (fun lam : ℝ ↦ ∫ x in (0 : ℝ)..1, momentKernel lam x)
      (Icc a b) := by
    intro lam hlam
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ : ℝ ↦ a⁻¹)
    · filter_upwards [self_mem_nhdsWithin] with mu hmu
      simpa only [uIoc_of_le zero_le_one] using
        (criticalRoot_intervalIntegrable_momentKernel
          (ha.trans_le hmu.1)).1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with mu hmu
      filter_upwards with x hx
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [uIoc] using hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (criticalRoot_momentKernel_nonneg
          (ha.trans_le hmu.1).le hx'.1.le)]
      exact criticalRoot_momentKernel_le_inv (ha.trans_le hmu.1)
        ⟨hx'.1.le, hx'.2⟩ |>.trans (inv_anti₀ ha hmu.1)
    · exact intervalIntegrable_const
    · filter_upwards with x hx
      by_cases hx0 : x = 0
      · subst x
        simpa [momentKernel] using
          (continuousWithinAt_const :
            ContinuousWithinAt (fun _ : ℝ ↦ (0 : ℝ)) (Icc a b) lam)
      · have hxpos : 0 < x := by
          have : x ∈ Ioc (0 : ℝ) 1 := by
            simpa [uIoc] using hx
          exact this.1
        simp only [momentKernel, hx0, if_false, selectionProbability]
        have hinner : ContinuousAt
            (fun mu : ℝ ↦ 1 + Real.exp (mu / x)) lam := by fun_prop
        have hinner_ne : 1 + Real.exp (lam / x) ≠ 0 := by positivity
        exact ((continuousAt_const.div hinner hinner_ne).div_const x).continuousWithinAt
  exact hparam.congr fun lam _ ↦
    (criticalRoot_intervalIntegral_eq_moment lam).symm

private theorem criticalRoot_momentKernel_lt
    {lam mu x : ℝ} (_hlam : 0 < lam) (_hmu : 0 < mu)
    (hlm : lam < mu) (hx : 0 < x) :
    momentKernel mu x < momentKernel lam x := by
  have hexp : Real.exp (lam / x) < Real.exp (mu / x) := by
    exact Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hx).2 hlm)
  have hden :
      x * (1 + Real.exp (lam / x)) <
        x * (1 + Real.exp (mu / x)) := by
    exact mul_lt_mul_of_pos_left (by linarith) hx
  have hdenpos : 0 < x * (1 + Real.exp (lam / x)) := by positivity
  have hdenpos' : 0 < x * (1 + Real.exp (mu / x)) := by positivity
  simp only [momentKernel, hx.ne', if_false, selectionProbability,
    div_eq_mul_inv]
  have hmu_rearrange :
      (1 + Real.exp (mu * x⁻¹))⁻¹ * x⁻¹ =
        (x * (1 + Real.exp (mu / x)))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, mul_comm]
  have hlam_rearrange :
      (1 + Real.exp (lam * x⁻¹))⁻¹ * x⁻¹ =
        (x * (1 + Real.exp (lam / x)))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, mul_comm]
  simp only [one_mul]
  rw [hmu_rearrange, hlam_rearrange]
  exact (inv_lt_inv₀ hdenpos' hdenpos).2 hden

/-- The moment is strictly decreasing on the positive half-line. -/
theorem criticalRoot_strictAntiOn_moment :
    StrictAntiOn moment (Ioi (0 : ℝ)) := by
  intro lam hlam mu hmu hlm
  rw [← criticalRoot_intervalIntegral_eq_moment,
    ← criticalRoot_intervalIntegral_eq_moment]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := (0 : ℝ)) (b := 1) zero_lt_one
      (criticalRoot_continuousOn_momentKernel hmu)
      (criticalRoot_continuousOn_momentKernel hlam)
  · intro x hx
    exact (criticalRoot_momentKernel_lt hlam hmu hlm hx.1).le
  · refine ⟨1, right_mem_Icc.mpr zero_le_one, ?_⟩
    exact criticalRoot_momentKernel_lt hlam hmu hlm zero_lt_one

private theorem criticalRoot_moment_two_lt_one : moment 2 < 1 := by
  rw [← criticalRoot_intervalIntegral_eq_moment]
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    (criticalRoot_intervalIntegrable_momentKernel (by norm_num : (0 : ℝ) < 2))
    intervalIntegrable_const
    (fun x hx ↦ criticalRoot_momentKernel_le_inv
      (by norm_num : (0 : ℝ) < 2) hx)
  norm_num at hmono ⊢
  linarith

private theorem criticalRoot_smallParameter_pos :
    0 < Real.exp (-8 : ℝ) := Real.exp_pos _

private theorem criticalRoot_smallParameter_le_one :
    Real.exp (-8 : ℝ) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by norm_num)

private theorem criticalRoot_small_kernel_bound
    {x : ℝ} (hx : x ∈ Icc (Real.exp (-8 : ℝ)) 1) :
    (4 * x)⁻¹ ≤ momentKernel (Real.exp (-8 : ℝ)) x := by
  let lam : ℝ := Real.exp (-8 : ℝ)
  have hlam : 0 < lam := Real.exp_pos _
  have hxpos : 0 < x := hlam.trans_le hx.1
  have hratio : lam / x ≤ 1 := (div_le_one hxpos).2 hx.1
  have hexp : Real.exp (lam / x) < 3 :=
    (Real.exp_le_exp.mpr hratio).trans_lt Real.exp_one_lt_three
  have hden : x * (1 + Real.exp (lam / x)) ≤ 4 * x := by
    nlinarith [Real.exp_pos (lam / x)]
  have hdenpos : 0 < x * (1 + Real.exp (lam / x)) := by positivity
  have h4pos : 0 < 4 * x := by positivity
  simp only [momentKernel, hxpos.ne', if_false, selectionProbability,
    div_eq_mul_inv]
  have hrearrange :
      (1 + Real.exp (lam * x⁻¹))⁻¹ * x⁻¹ =
        (x * (1 + Real.exp (lam / x)))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, mul_comm]
  rw [one_mul, hrearrange]
  exact (inv_le_inv₀ h4pos hdenpos).2 hden

private theorem criticalRoot_integral_inv_four_mul :
    (∫ x in Real.exp (-8 : ℝ)..1, (4 * x)⁻¹) = 2 := by
  have hlam : 0 < Real.exp (-8 : ℝ) := Real.exp_pos _
  have hderiv : ∀ x ∈ [[Real.exp (-8 : ℝ), (1 : ℝ)]],
      HasDerivAt (fun y : ℝ ↦ (1 / 4 : ℝ) * Real.log y) (4 * x)⁻¹ x := by
    intro x hx
    have hxpos : 0 < x := by
      have hx' : x ∈ Icc (Real.exp (-8 : ℝ)) 1 := by
        simpa [uIcc_of_le criticalRoot_smallParameter_le_one] using hx
      exact hlam.trans_le hx'.1
    simpa [mul_inv, mul_comm] using
      (Real.hasDerivAt_log hxpos.ne').const_mul (1 / 4 : ℝ)
  have hint : IntervalIntegrable (fun x : ℝ ↦ (4 * x)⁻¹)
      volume (Real.exp (-8 : ℝ)) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.mul continuousOn_id).inv₀ fun x hx ↦ by
      have hxpos : 0 < x := by
        have hx' : x ∈ Icc (Real.exp (-8 : ℝ)) 1 := by
          simpa [uIcc_of_le criticalRoot_smallParameter_le_one] using hx
        exact hlam.trans_le hx'.1
      exact mul_ne_zero (by norm_num) hxpos.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [Real.log_one, Real.log_exp]
  norm_num

private theorem criticalRoot_one_lt_moment_small :
    1 < moment (Real.exp (-8 : ℝ)) := by
  let lam : ℝ := Real.exp (-8 : ℝ)
  have hlam : 0 < lam := Real.exp_pos _
  have hlam1 : lam ≤ 1 := criticalRoot_smallParameter_le_one
  have hkernelInt := criticalRoot_intervalIntegrable_momentKernel hlam
  have hsub_le_full :
      (∫ x in lam..1, momentKernel lam x) ≤
        ∫ x in (0 : ℝ)..1, momentKernel lam x := by
    apply intervalIntegral.integral_mono_interval hlam.le hlam1 le_rfl
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact criticalRoot_momentKernel_nonneg hlam.le hx.1.le
    · exact hkernelInt
  have hlower :
      (∫ x in lam..1, (4 * x)⁻¹) ≤
        ∫ x in lam..1, momentKernel lam x := by
    apply intervalIntegral.integral_mono_on hlam1
    · apply ContinuousOn.intervalIntegrable
      exact (continuousOn_const.mul continuousOn_id).inv₀ fun x hx ↦ by
        have hxpos : 0 < x := by
          have hx' : x ∈ Icc lam 1 := by
            simpa [uIcc_of_le hlam1] using hx
          exact hlam.trans_le hx'.1
        exact mul_ne_zero (by norm_num) hxpos.ne'
    · exact hkernelInt.mono_set (by
        rw [uIcc_of_le hlam1, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hlam.le le_rfl)
    · intro x hx
      exact criticalRoot_small_kernel_bound hx
  rw [criticalRoot_intervalIntegral_eq_moment] at hsub_le_full
  have htwo : (∫ x in lam..1, (4 * x)⁻¹) = 2 := by
    simpa [lam] using criticalRoot_integral_inv_four_mul
  rw [htwo] at hlower
  linarith

/-- There exists exactly one positive solution of the critical moment
equation. -/
theorem exists_isUniqueCriticalParameter :
    ∃ lam : ℝ, IsUniqueCriticalParameter lam := by
  let a : ℝ := Real.exp (-8 : ℝ)
  have ha : 0 < a := Real.exp_pos _
  have hab : a ≤ 2 := by
    exact criticalRoot_smallParameter_le_one.trans (by norm_num)
  have hcont : ContinuousOn moment (Icc a 2) :=
    criticalRoot_continuousOn_moment ha
  have hone : (1 : ℝ) ∈ Icc (moment 2) (moment a) := by
    constructor
    · exact (criticalRoot_moment_two_lt_one).le
    · have hsmall := criticalRoot_one_lt_moment_small
      simpa [a] using hsmall.le
  rcases intermediate_value_Icc' hab hcont hone with ⟨lam, hlamI, hlam⟩
  refine ⟨lam, ⟨⟨ha.trans_le hlamI.1, hlam⟩, ?_⟩⟩
  intro mu hmu
  rcases lt_trichotomy mu lam with hlt | heq | hgt
  · have := criticalRoot_strictAntiOn_moment hmu.1
        (ha.trans_le hlamI.1) hlt
    linarith [hmu.2]
  · exact heq
  · have := criticalRoot_strictAntiOn_moment
        (ha.trans_le hlamI.1) hmu.1 hgt
    linarith [hmu.2]

end

end Erdos297

#print axioms Erdos297.exists_isUniqueCriticalParameter
