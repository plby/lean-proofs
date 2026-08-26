import ErdosProblems.Erdos520.HarperCDFProduct
import ErdosProblems.Erdos520.HarperGaussianBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Erdos
namespace Problem520

/-! # Uniform CDF regularity of a nondegenerate Gaussian -/

/-- A Gaussian CDF is Lipschitz with the deliberately coarse constant
`1 / sqrt variance`. -/
theorem abs_cdf_gaussianReal_sub_le_inv_sqrt
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ) :
    |cdf (gaussianReal m v) x - cdf (gaussianReal m v) y| ≤
      (Real.sqrt (v : ℝ))⁻¹ * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := this y x hyx
    simpa only [abs_sub_comm] using! h
  have hmono : cdf (gaussianReal m v) x ≤ cdf (gaussianReal m v) y :=
    monotone_cdf (gaussianReal m v) hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub,
    abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
  rw [← measureReal_Ioc_eq_cdf_sub (gaussianReal m v) hxy]
  calc
    (gaussianReal m v).real (Ioc x y) ≤
        (gaussianReal m v).real (Icc x y) :=
      measureReal_mono Ioc_subset_Icc_self
    _ ≤ (y - x) / Real.sqrt (v : ℝ) :=
      gaussianReal_real_Icc_le_inv_sqrt m hv hxy
    _ = (Real.sqrt (v : ℝ))⁻¹ * (y - x) := by ring

/-- A coarse pointwise lower bound for centered Gaussian densities whose
variance lies in Harper's eventual scheduled interval. -/
theorem gaussianPDFReal_zero_ge_of_variance_mem
    {v : ℝ≥0} (hvLower : (1 / 3 : ℝ) ≤ (v : ℝ))
    (hvUpper : (v : ℝ) ≤ 3 / 8)
    {a delta x : ℝ} (hdelta1 : delta ≤ 1)
    (hx : x ∈ Ioc a (a + delta)) :
    (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
      gaussianPDFReal 0 v x := by
  have hv : v ≠ 0 := by
    intro hzero
    simp only [hzero, NNReal.coe_zero] at hvLower
    norm_num at hvLower
  have hvpos : 0 < (v : ℝ) := by linarith
  have hdenpos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_pos.2
    positivity
  have hinside : 2 * Real.pi * (v : ℝ) ≤ 4 := by
    calc
      2 * Real.pi * (v : ℝ) ≤ 2 * Real.pi * (3 / 8 : ℝ) := by gcongr
      _ ≤ 4 := by nlinarith [Real.pi_lt_four]
  have hdensqrt : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith [hinside]
  have hcoef : (1 / 2 : ℝ) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    simpa only [one_div] using!
      one_div_le_one_div_of_le hdenpos hdensqrt
  have hxsub0 : 0 ≤ x - a := by linarith [hx.1]
  have hxsub : x - a ≤ delta := by linarith [hx.2]
  have hxabs : |x| ≤ |a| + 1 := by
    calc
      |x| = |a + (x - a)| := by ring_nf
      _ ≤ |a| + |x - a| := abs_add_le _ _
      _ = |a| + (x - a) := by rw [abs_of_nonneg hxsub0]
      _ ≤ |a| + delta := by linarith
      _ ≤ |a| + 1 := by linarith
  have hxsq : x ^ 2 ≤ (|a| + 1) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hbase : 0 ≤ (|a| + 1) ^ 2 := sq_nonneg _
  have hdenLower : (2 / 3 : ℝ) ≤ 2 * (v : ℝ) := by linarith
  have hquot : x ^ 2 / (2 * (v : ℝ)) ≤ 2 * (|a| + 1) ^ 2 := by
    calc
      x ^ 2 / (2 * (v : ℝ)) ≤
          (|a| + 1) ^ 2 / (2 * (v : ℝ)) := by gcongr
      _ ≤ (|a| + 1) ^ 2 / (2 / 3 : ℝ) := by
        exact div_le_div_of_nonneg_left hbase (by norm_num) hdenLower
      _ ≤ 2 * (|a| + 1) ^ 2 := by
        rw [div_eq_mul_inv]
        norm_num
        nlinarith
  have hexp : Real.exp (-2 * (|a| + 1) ^ 2) ≤
      Real.exp (-x ^ 2 / (2 * (v : ℝ))) := by
    apply Real.exp_le_exp.mpr
    calc
      -2 * (|a| + 1) ^ 2 = -(2 * (|a| + 1) ^ 2) := by ring
      _ ≤ -(x ^ 2 / (2 * (v : ℝ))) := neg_le_neg hquot
      _ = -x ^ 2 / (2 * (v : ℝ)) := by ring
  unfold gaussianPDFReal
  simp only [sub_zero]
  exact mul_le_mul hcoef hexp (by positivity) (by positivity)

/-- Every interval of length `delta ≤ 1` in the moderate range has an
explicit Gaussian mass lower bound, uniformly for variances in `[1/3,3/8]`. -/
theorem gaussianReal_real_Ioc_ge_of_variance_mem
    {v : ℝ≥0} (hvLower : (1 / 3 : ℝ) ≤ (v : ℝ))
    (hvUpper : (v : ℝ) ≤ 3 / 8)
    {a delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
      (gaussianReal 0 v).real (Ioc a (a + delta)) := by
  have hv : v ≠ 0 := by
    intro hzero
    simp only [hzero, NNReal.coe_zero] at hvLower
    norm_num at hvLower
  rw [Measure.real, gaussianReal_apply_eq_integral 0 hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) =
          ∫ _x in Ioc a (a + delta),
            (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a + delta - a)]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ x in Ioc a (a + delta), gaussianPDFReal 0 v x := by
        apply setIntegral_mono_on
        · exact MeasureTheory.integrableOn_const
            (μ := volume) (s := Ioc a (a + delta))
            (C := (1 / 2 : ℝ) * Real.exp (-2 * (|a| + 1) ^ 2))
            (hs := by rw [Real.volume_Ioc]; simp)
        · exact (integrable_gaussianPDFReal 0 v).integrableOn
        · exact measurableSet_Ioc
        · intro x hx
          exact gaussianPDFReal_zero_ge_of_variance_mem
            hvLower hvUpper hdelta1 hx
  · exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 v x

end Problem520
end Erdos
