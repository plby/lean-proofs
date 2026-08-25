import Util.Bernays.HalfPowerMeasure

/-!
# Compact measures associated with a Laplace transform

For a positive measure on the nonnegative real line, exponential weighting and
the map `y ↦ exp (-s*y)` turn ratios of its Laplace transform into moments on
the compact unit interval. This is the transform step in the Tauberian proof.
-/

open MeasureTheory Filter Topology Real
open scoped unitInterval NNReal ENNReal

namespace Bernays

noncomputable def laplace (μ : Measure ℝ≥0) (s : ℝ) : ℝ :=
  ∫ y : ℝ≥0, exp (-s * y) ∂μ

theorem laplace_nonneg (μ : Measure ℝ≥0) (s : ℝ) : 0 ≤ laplace μ s :=
  integral_nonneg fun _ => (exp_pos _).le

noncomputable def expNegMul (s : ℝ) (hs : 0 < s) (y : ℝ≥0) : I :=
  ⟨exp (-s * y), (exp_pos _).le,
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) y.coe_nonneg)⟩

theorem continuous_expNegMul (s : ℝ) (hs : 0 < s) : Continuous (expNegMul s hs) := by
  apply Continuous.subtype_mk
  exact continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)

noncomputable def laplaceWeightedMeasure (μ : Measure ℝ≥0) (s : ℝ)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) : FiniteMeasure ℝ≥0 :=
  ⟨μ.withDensity (fun y : ℝ≥0 => ENNReal.ofReal (exp (-s * y))),
    isFiniteMeasure_withDensity
      ((lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
        (Filter.Eventually.of_forall fun _ => (exp_pos _).le)).mpr h)⟩

noncomputable def compactLaplaceMeasure (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) : FiniteMeasure I :=
  ((laplace μ s).toNNReal)⁻¹ •
    FiniteMeasure.map (laplaceWeightedMeasure μ s h) (expNegMul s hs)

theorem compactLaplaceMeasure_integral (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ)
    (f : I → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      (laplace μ s)⁻¹ * ∫ y : ℝ≥0, exp (-s * y) * f (expNegMul s hs y) ∂μ := by
  rw [compactLaplaceMeasure, FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_inv, Real.coe_toNNReal _ (laplace_nonneg μ s)]
  change (laplace μ s)⁻¹ *
    (∫ x, f x ∂(μ.withDensity (fun y : ℝ≥0 => ENNReal.ofReal (exp (-s * y)))).map
      (expNegMul s hs)) = _
  rw [integral_map (continuous_expNegMul s hs).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]

theorem compactLaplaceMeasure_moment (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) (k : ℕ) :
    (∫ x : I, (x : ℝ) ^ k ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      laplace μ (((k : ℝ) + 1) * s) / laplace μ s := by
  rw [compactLaplaceMeasure_integral μ s hs h (fun x : I => (x : ℝ) ^ k) (by fun_prop)]
  have heq (y : ℝ≥0) : exp (-s * y) * (expNegMul s hs y : ℝ) ^ k =
      exp (-(((k : ℝ) + 1) * s) * y) := by
    change exp (-s * y) * exp (-s * y) ^ k = _
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [heq]
  change (laplace μ s)⁻¹ * laplace μ (((k : ℝ) + 1) * s) = _
  ring

theorem expNegMul_mem_cutoff_iff (s : ℝ) (hs : 0 < s) (y : ℝ≥0) :
    exp (-1) ≤ (expNegMul s hs y : ℝ) ↔ (y : ℝ) ≤ s⁻¹ := by
  change exp (-1) ≤ exp (-s * y) ↔ _
  rw [Real.exp_le_exp]
  constructor
  · intro hy
    rw [← one_div]
    apply (le_div_iff₀ hs).mpr
    change (y : ℝ) * s ≤ 1
    nlinarith
  · intro hy
    rw [← one_div] at hy
    have hys : (y : ℝ) * s ≤ 1 := (le_div_iff₀ hs).mp hy
    nlinarith

theorem compactLaplaceMeasure_cutoff (μ : Measure ℝ≥0) (s : ℝ) (hs : 0 < s)
    (h : Integrable (fun y : ℝ≥0 => exp (-s * y)) μ) :
    (∫ x, cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) x
      ∂(compactLaplaceMeasure μ s hs h : Measure I)) =
      μ.real {y : ℝ≥0 | (y : ℝ) ≤ s⁻¹} / laplace μ s := by
  rw [compactLaplaceMeasure_integral]
  · have heq (y : ℝ≥0) : exp (-s * y) *
        cutoff (reciprocalCutWeight (exp (-1)) (exp_pos _)) (exp (-1)) (expNegMul s hs y) =
        {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}.indicator (fun _ => (1 : ℝ)) y := by
      change exp (-s * y) *
        (if exp (-1) ≤ exp (-s * y) then (max (exp (-1)) (exp (-s * y)))⁻¹ else 0) = _
      by_cases hy : (y : ℝ) ≤ s⁻¹
      · have he := (expNegMul_mem_cutoff_iff s hs y).mpr hy
        change exp (-1) ≤ exp (-s * y) at he
        rw [if_pos he, max_eq_right he, mul_inv_cancel₀ (exp_ne_zero _),
          Set.indicator_of_mem (s := {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}) hy]
      · have he : ¬ exp (-1) ≤ exp (-s * y) :=
          fun h => hy ((expNegMul_mem_cutoff_iff s hs y).mp h)
        rw [if_neg he, mul_zero,
          Set.indicator_of_notMem (s := {z : ℝ≥0 | (z : ℝ) ≤ s⁻¹}) hy]
    simp_rw [heq]
    rw [integral_indicator (measurableSet_le NNReal.continuous_coe.measurable measurable_const),
      integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      div_eq_mul_inv, mul_comm]
  · exact (reciprocalCutWeight (exp (-1)) (exp_pos _)).continuous.measurable.ite
      (measurableSet_le measurable_const continuous_subtype_val.measurable) measurable_const

end Bernays
