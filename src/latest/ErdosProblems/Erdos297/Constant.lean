/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Erdős Problem 297: the analytic constant

This file develops the logistic moment and pressure appearing in the sharp
exponent.  In particular, it proves that the moment equation has a unique
positive solution.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos297

noncomputable section

lemma momentKernel_eq (lam : ℝ) {x : ℝ} (hx : x ≠ 0) :
    momentKernel lam x = (x * (1 + Real.exp (lam / x)))⁻¹ := by
  simp [momentKernel, selectionProbability, hx, div_eq_mul_inv]

lemma momentKernel_zero (lam : ℝ) : momentKernel lam 0 = 0 := by
  simp [momentKernel]

lemma measurable_momentKernel (lam : ℝ) : Measurable (momentKernel lam) := by
  rw [show momentKernel lam = fun x : ℝ =>
      if x = 0 then 0 else (1 + Real.exp (lam / x))⁻¹ / x by
    funext x
    by_cases hx : x = 0 <;> simp [momentKernel, selectionProbability, hx]]
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  have hdiv : Measurable (fun x : ℝ => lam / x) := measurable_const.div measurable_id
  have hexp : Measurable (fun x : ℝ => Real.exp (lam / x)) := hdiv.exp
  have hadd : Measurable (fun x : ℝ => 1 + Real.exp (lam / x)) :=
    measurable_const.add hexp
  exact hadd.inv.div measurable_id

lemma momentKernel_nonneg {lam x : ℝ} (hx : 0 ≤ x) :
    0 ≤ momentKernel lam x := by
  by_cases h0 : x = 0
  · subst x
    simp [momentKernel]
  rw [momentKernel_eq lam h0]
  positivity

lemma momentKernel_le_inv {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Icc (0 : ℝ) 1) :
    momentKernel lam x ≤ lam⁻¹ := by
  by_cases h0 : x = 0
  · subst x
    simp [momentKernel, hlam.le]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
  have hzexp : lam / x ≤ Real.exp (lam / x) := by
    calc
      lam / x ≤ lam / x + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp (lam / x) := Real.add_one_le_exp _
  have hden : lam ≤ x * (1 + Real.exp (lam / x)) := by
    calc
      lam = x * (lam / x) := by field_simp
      _ ≤ x * Real.exp (lam / x) := mul_le_mul_of_nonneg_left hzexp hxpos.le
      _ ≤ x * (1 + Real.exp (lam / x)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hxpos.le
  rw [momentKernel_eq lam h0]
  exact inv_anti₀ hlam hden

lemma integrableOn_momentKernel {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (momentKernel lam) (Icc (0 : ℝ) 1) := by
  rw [IntegrableOn]
  apply Integrable.mono' (integrable_const (c := lam⁻¹))
  · exact (measurable_momentKernel lam).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (momentKernel_nonneg hx.1)]
    exact momentKernel_le_inv hlam hx

lemma intervalIntegrable_momentKernel {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (momentKernel lam) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  exact integrableOn_momentKernel hlam

lemma moment_eq_intervalIntegral (lam : ℝ) :
    moment lam = ∫ x in (0 : ℝ)..1, momentKernel lam x := by
  rw [moment, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

lemma momentKernel_strictAnti_parameter {a b x : ℝ}
    (hab : a < b) (hx : 0 < x) :
    momentKernel b x < momentKernel a x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [momentKernel_eq b hx0, momentKernel_eq a hx0]
  apply (inv_lt_inv₀ (by positivity) (by positivity)).2
  exact mul_lt_mul_of_pos_left
    (add_lt_add_right (Real.exp_lt_exp.mpr (div_lt_div_of_pos_right hab hx)) 1) hx

theorem strictAntiOn_moment : StrictAntiOn moment (Ioi 0) := by
  intro a ha b hb hab
  rw [moment_eq_intervalIntegral, moment_eq_intervalIntegral]
  apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
      zero_le_one (intervalIntegrable_momentKernel hb)
      (intervalIntegrable_momentKernel ha)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (momentKernel_strictAnti_parameter hab hx.1).le
  · have hmeas : MeasurableSet {x : ℝ | momentKernel b x < momentKernel a x} :=
      measurableSet_lt (measurable_momentKernel b) (measurable_momentKernel a)
    rw [Measure.restrict_apply hmeas, inter_eq_right.mpr]
    · simp
    · intro x hx
      exact momentKernel_strictAnti_parameter hab hx.1

lemma continuousOn_moment_Icc :
    ContinuousOn moment (Icc ((1 : ℝ) / 100) 2) := by
  intro lam hlam
  have hcont : ContinuousWithinAt
      (fun y : ℝ ↦ ∫ x in (0 : ℝ)..1, momentKernel y x)
      (Icc ((1 : ℝ) / 100) 2) lam := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ : ℝ ↦ (100 : ℝ))
    · exact Eventually.of_forall fun y ↦
        (measurable_momentKernel y).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards with x
      intro hx
      rw [uIoc_of_le zero_le_one] at hx
      have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
      rw [Real.norm_eq_abs, abs_of_nonneg (momentKernel_nonneg hx.1.le)]
      calc
        momentKernel y x ≤ y⁻¹ := momentKernel_le_inv hypos (Ioc_subset_Icc_self hx)
        _ ≤ (((1 : ℝ) / 100))⁻¹ := inv_anti₀ (by norm_num) hy.1
        _ = 100 := by norm_num
    · exact intervalIntegrable_const
    · filter_upwards with x
      intro hx
      rw [uIoc_of_le zero_le_one] at hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      simp only [momentKernel, selectionProbability, hx0, if_false]
      have hquot : ContinuousAt (fun y : ℝ ↦ y / x) lam :=
        continuousAt_id.div_const x
      have hexp : ContinuousAt (fun y : ℝ ↦ Real.exp (y / x)) lam :=
        Real.continuous_exp.continuousAt.comp hquot
      have hden : ContinuousAt (fun y : ℝ ↦ 1 + Real.exp (y / x)) lam :=
        continuousAt_const.add hexp
      have hinv : ContinuousAt
          (fun y : ℝ ↦ (1 + Real.exp (y / x))⁻¹) lam := by
        exact hden.tendsto.inv₀ (by positivity)
      simpa only [one_div] using (hinv.div_const x).continuousWithinAt
  simpa only [← moment_eq_intervalIntegral] using hcont

lemma moment_two_lt_one : moment 2 < 1 := by
  rw [moment_eq_intervalIntegral]
  calc
    (∫ x in (0 : ℝ)..1, momentKernel 2 x) ≤
        ∫ _x in (0 : ℝ)..1, (2 : ℝ)⁻¹ := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_momentKernel (by norm_num)) intervalIntegrable_const
      intro x hx
      exact momentKernel_le_inv (by norm_num) hx
    _ = (2 : ℝ)⁻¹ := by simp
    _ < 1 := by norm_num

lemma moment_one_div_hundred_gt_one : 1 < moment ((1 : ℝ) / 100) := by
  let lam : ℝ := (1 : ℝ) / 100
  have hlam : 0 < lam := by dsimp [lam]; norm_num
  have hlam1 : lam ≤ 1 := by dsimp [lam]; norm_num
  have hfullInt := intervalIntegrable_momentKernel hlam
  have hcompInt : IntervalIntegrable (fun x : ℝ ↦ (4 * x)⁻¹) volume lam 1 := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro x hx
      rw [uIcc_of_le hlam1] at hx
      exact mul_ne_zero (by norm_num) (ne_of_gt (hlam.trans_le hx.1))
    · fun_prop
  have hkernelLower : ∀ x ∈ Icc lam 1, (4 * x)⁻¹ < momentKernel lam x := by
    intro x hx
    have hxpos : 0 < x := hlam.trans_le hx.1
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hratio : lam / x ≤ 1 := (div_le_one hxpos).2 hx.1
    rw [momentKernel_eq lam hx0]
    apply (inv_lt_inv₀ (by positivity) (by positivity)).2
    have hexp : Real.exp (lam / x) < 3 :=
      (Real.exp_le_exp.mpr hratio).trans_lt Real.exp_one_lt_three
    nlinarith
  have hlog : (4 : ℝ) < Real.log 100 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    calc
      Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 ^ (4 : ℕ) := by
        gcongr
        exact Real.exp_one_lt_three
      _ < 100 := by norm_num
  have hcompValue : 1 < ∫ x in lam..1, (4 * x)⁻¹ := by
    calc
      1 < (4 : ℝ)⁻¹ * Real.log (1 / lam) := by
        dsimp [lam]
        norm_num only [one_div, inv_div, inv_one, one_mul]
        nlinarith
      _ = ∫ x in lam..1, (4 * x)⁻¹ := by
        rw [show (fun x : ℝ ↦ (4 * x)⁻¹) = fun x ↦ (4 : ℝ)⁻¹ * x⁻¹ by
          funext x
          simp only [mul_inv_rev, mul_comm],
          intervalIntegral.integral_const_mul,
          integral_inv_of_pos hlam zero_lt_one]
  have hsub : (∫ x in lam..1, momentKernel lam x) ≤
      ∫ x in (0 : ℝ)..1, momentKernel lam x := by
    apply intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := 1)
        hlam.le hlam1 le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact momentKernel_nonneg hx.1.le
    · exact hfullInt
  rw [moment_eq_intervalIntegral]
  exact hcompValue.trans_le <|
    (intervalIntegral.integral_mono_on hlam1 hcompInt
      (hfullInt.mono_set (by
        rw [uIcc_of_le hlam1, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hlam.le le_rfl))
      fun x hx ↦ (hkernelLower x hx).le).trans hsub

/-- The moment equation defining the sharp exponent has exactly one positive
solution. -/
theorem exists_unique_criticalParameter :
    ∃ lam : ℝ, IsUniqueCriticalParameter lam := by
  have hinterval : ((1 : ℝ) / 100) ≤ 2 := by norm_num
  have hone_mem : (1 : ℝ) ∈
      Icc (moment 2) (moment ((1 : ℝ) / 100)) :=
    ⟨moment_two_lt_one.le, moment_one_div_hundred_gt_one.le⟩
  obtain ⟨lam, hlamIcc, hlamMoment⟩ :=
    (intermediate_value_Icc' hinterval continuousOn_moment_Icc) hone_mem
  have hlamPos : 0 < lam :=
    (by norm_num : (0 : ℝ) < 1 / 100).trans_le hlamIcc.1
  refine ⟨lam, ⟨⟨hlamPos, hlamMoment⟩, ?_⟩⟩
  intro mu hmu
  exact strictAntiOn_moment.injOn hmu.1 hlamPos
    (hmu.2.trans hlamMoment.symm)

end

end Erdos297

#print axioms Erdos297.exists_unique_criticalParameter
