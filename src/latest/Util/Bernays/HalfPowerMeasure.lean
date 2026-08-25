import Util.Bernays.CutoffConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The measure for the half-power Tauberian law

Pushing the Gaussian density `exp (-t²) / sqrt π` forward by `t ↦ exp (-t²)`
gives a measure on `[0,1]` with moments `1 / sqrt (k+1)`. The weighted cutoff
at `exp (-1)` has integral `2 / sqrt π`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped unitInterval NNReal

namespace Bernays

noncomputable def expNegSq (t : ℝ) : I :=
  ⟨exp (-(t ^ 2)), (exp_pos _).le, exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))⟩

theorem continuous_expNegSq : Continuous expNegSq := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp (continuous_id.pow 2).neg

noncomputable def halfPowerMeasure : FiniteMeasure I :=
  FiniteMeasure.map (⟨gaussianReal 0 (1 / 2), inferInstance⟩ : FiniteMeasure ℝ) expNegSq

theorem gaussianPDFReal_half (t : ℝ) :
    gaussianPDFReal 0 (1 / 2) t = (sqrt π)⁻¹ * exp (-(t ^ 2)) := by
  have hv : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  simp only [gaussianPDFReal, hv, sub_zero,
    show 2 * π * (1 / 2 : ℝ) = π by ring,
    show 2 * (1 / 2 : ℝ) = 1 by norm_num, div_one]

theorem halfPowerMeasure_integral (f : I → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(halfPowerMeasure : Measure I)) =
      (sqrt π)⁻¹ * ∫ t : ℝ, exp (-(t ^ 2)) * f (expNegSq t) := by
  change (∫ x, f x ∂(gaussianReal 0 (1 / 2)).map expNegSq) = _
  rw [integral_map continuous_expNegSq.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal_half, mul_assoc, integral_const_mul]

theorem halfPowerMeasure_moment (k : ℕ) :
    (∫ x : I, (x : ℝ) ^ k ∂(halfPowerMeasure : Measure I)) =
      1 / sqrt ((k : ℝ) + 1) := by
  rw [halfPowerMeasure_integral (fun x : I => (x : ℝ) ^ k) (by fun_prop)]
  have heq (t : ℝ) : exp (-(t ^ 2)) * (expNegSq t : ℝ) ^ k =
      exp (-((k : ℝ) + 1) * t ^ 2) := by
    change exp (-(t ^ 2)) * exp (-(t ^ 2)) ^ k = _
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [heq]
  rw [integral_gaussian, sqrt_div pi_pos.le]
  have hπ : sqrt π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  field_simp

noncomputable def reciprocalCutWeight (a : ℝ) (ha : 0 < a) : C(I, ℝ) where
  toFun x := (max a (x : ℝ))⁻¹
  continuous_toFun := (continuous_const.max continuous_subtype_val).inv₀
    (fun x => (ha.trans_le (le_max_left a (x : ℝ))).ne')

theorem reciprocalCutWeight_nonneg (a : ℝ) (ha : 0 < a) (x : I) :
    0 ≤ reciprocalCutWeight a ha x :=
  inv_nonneg.mpr (ha.le.trans (le_max_left _ _))

theorem halfPowerMeasure_null_cutoff :
    (halfPowerMeasure : Measure I) {x : I | (x : ℝ) = exp (-1)} = 0 := by
  change ((gaussianReal 0 (1 / 2)).map expNegSq) _ = 0
  rw [Measure.map_apply continuous_expNegSq.measurable
    (measurableSet_eq_fun continuous_subtype_val.measurable measurable_const)]
  have : NullSingletonClass (gaussianReal 0 (1 / 2)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  apply measure_mono_null (t := ({-1, 1} : Set ℝ))
  · intro t ht
    change exp (-(t ^ 2)) = exp (-1) at ht
    have he := Real.exp_injective ht
    have hm : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with hm | hm
    · have : t = 1 := by linarith
      simp [this]
    · have : t = -1 := by linarith
      simp [this]
  · exact (Set.toFinite ({-1, 1} : Set ℝ)).measure_zero (gaussianReal 0 (1 / 2))

theorem cutoff_reciprocal_expNegSq (t : ℝ) :
    exp (-(t ^ 2)) *
      cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) (expNegSq t) =
      (Set.Icc (-1) 1).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  have he : exp (-1) ≤ exp (-(t ^ 2)) ↔ t ∈ Set.Icc (-1) 1 := by
    rw [Real.exp_le_exp, Set.mem_Icc]
    constructor
    · intro ht
      constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
    · rintro ⟨hl, hu⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ t + 1)]
  change exp (-(t ^ 2)) *
    (if exp (-1) ≤ exp (-(t ^ 2)) then (max (exp (-1)) (exp (-(t ^ 2))))⁻¹ else 0) = _
  by_cases ht : t ∈ Set.Icc (-1) 1
  · rw [if_pos (he.mpr ht), max_eq_right (he.mpr ht),
      mul_inv_cancel₀ (exp_ne_zero _), Set.indicator_of_mem ht]
  · rw [if_neg (fun h => ht (he.mp h)), mul_zero, Set.indicator_of_notMem ht]

theorem halfPowerMeasure_cutoff_integral :
    (∫ x, cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) x
      ∂(halfPowerMeasure : Measure I)) = 2 / sqrt π := by
  rw [halfPowerMeasure_integral]
  · simp_rw [cutoff_reciprocal_expNegSq]
    rw [integral_indicator measurableSet_Icc, integral_const]
    norm_num [Measure.real, Real.volume_Icc]
    ring
  · exact (reciprocalCutWeight (exp (-1)) (exp_pos _)).continuous.measurable.ite
      (measurableSet_le measurable_const continuous_subtype_val.measurable) measurable_const

end Bernays
