/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A Gaussian smoothing inequality for the small-ball estimate in Erdős 521.
Formal proof: Codex.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem integrable_gaussianSmoothing (μ : Measure ℝ) [IsFiniteMeasure μ] (δ : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (-((x / δ) ^ 2) / 2)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x / δ)])

theorem gaussianSmoothing_identity (μ : Measure ℝ) [IsFiniteMeasure μ] (δ : ℝ) :
    ((∫ x : ℝ, Real.exp (-((x / δ) ^ 2) / 2) ∂μ : ℝ) : ℂ) =
      ∫ t : ℝ, charFun μ (t / δ) ∂(gaussianReal 0 1) := by
  let kernel : ℝ → ℝ → ℂ := fun x t ↦ Complex.exp (((t / δ * x : ℝ) : ℂ) * Complex.I)
  have hkernel : Integrable (Function.uncurry kernel) (μ.prod (gaussianReal 0 1)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (by dsimp [kernel, Function.uncurry]; fun_prop)
    exact Filter.Eventually.of_forall fun p ↦ by simp [Function.uncurry, kernel, Complex.norm_exp]
  have hgaussian (x : ℝ) : ∫ t : ℝ, kernel x t ∂(gaussianReal 0 1) =
      (Real.exp (-((x / δ) ^ 2) / 2) : ℂ) := by
    have harg : (fun t ↦ kernel x t) =
        (fun t : ℝ ↦ Complex.exp (((x / δ * t : ℝ) : ℂ) * Complex.I)) := by
      funext t
      dsimp [kernel]
      rw [show t / δ * x = x / δ * t by ring]
    rw [harg]
    simp only [Complex.ofReal_mul]
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp [Complex.ofReal_exp]
    congr 1
    ring
  rw [← integral_complex_ofReal]
  calc
    (∫ x : ℝ, (Real.exp (-((x / δ) ^ 2) / 2) : ℂ) ∂μ) =
        ∫ x : ℝ, ∫ t : ℝ, kernel x t ∂(gaussianReal 0 1) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ (hgaussian x).symm
    _ = ∫ t : ℝ, ∫ x : ℝ, kernel x t ∂μ ∂(gaussianReal 0 1) :=
      integral_integral_swap hkernel
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ by
        simp [kernel, charFun_apply_real]

theorem smallBall_le_gaussianSmoothing (μ : Measure ℝ) [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {x : ℝ | |x| ≤ δ} ≤
      Real.exp (1 / 2) * ∫ x : ℝ, Real.exp (-((x / δ) ^ 2) / 2) ∂μ := by
  let S : Set ℝ := {x | |x| ≤ δ}
  have hS : MeasurableSet S := by measurability
  have hpoint (x : ℝ) : S.indicator (fun _ ↦ (1 : ℝ)) x ≤
      Real.exp (1 / 2) * Real.exp (-((x / δ) ^ 2) / 2) := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, ← Real.exp_add, Real.one_le_exp_iff]
      have hx' : |x / δ| ≤ 1 := by
        rw [abs_div, abs_of_pos hδ, div_le_one hδ]
        exact hx
      have hsq : (x / δ) ^ 2 ≤ 1 := by nlinarith [sq_abs (x / δ), abs_nonneg (x / δ)]
      linarith
    · rw [Set.indicator_of_notMem hx]
      positivity
  have h := integral_mono ((integrable_const (1 : ℝ)).indicator hS)
    ((integrable_gaussianSmoothing μ δ).const_mul (Real.exp (1 / 2))) hpoint
  simpa only [integral_indicator_const _ hS, smul_eq_mul, mul_one,
    integral_const_mul, S] using h

/-- A probability small ball is bounded by a Gaussian average of the modulus
of the characteristic function. The proof uses Fubini, with a bounded kernel. -/
theorem smallBall_le_charFun_gaussian (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {x : ℝ | |x| ≤ δ} ≤
      Real.exp (1 / 2) * ∫ t : ℝ, ‖charFun μ (t / δ)‖ ∂(gaussianReal 0 1) := by
  apply (smallBall_le_gaussianSmoothing μ hδ).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hnorm : ‖((∫ x : ℝ, Real.exp (-((x / δ) ^ 2) / 2) ∂μ : ℝ) : ℂ)‖ =
      ∫ x : ℝ, Real.exp (-((x / δ) ^ 2) / 2) ∂μ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact integral_nonneg fun _ ↦ (Real.exp_pos _).le
  rw [← hnorm, gaussianSmoothing_identity]
  exact norm_integral_le_integral_norm _

theorem standardGaussian_hasSubgaussianMGF :
    HasSubgaussianMGF (fun x : ℝ ↦ x) 1 (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by simp [mgf_fun_id_gaussianReal]

theorem standardGaussian_abs_tail {A : ℝ} (hA : 0 ≤ A) :
    (gaussianReal 0 1).real {t : ℝ | A ≤ |t|} ≤ 2 * Real.exp (-A ^ 2 / 2) := by
  have heq : {t : ℝ | A ≤ |t|} = {t : ℝ | A ≤ t} ∪ {t : ℝ | A ≤ -t} := by
    ext t
    simp [le_abs]
  rw [heq]
  have hpos := standardGaussian_hasSubgaussianMGF.measure_ge_le hA
  have hneg := standardGaussian_hasSubgaussianMGF.neg.measure_ge_le hA
  have hunion := measureReal_union_le (μ := gaussianReal 0 1)
    {t : ℝ | A ≤ t} {t : ℝ | A ≤ -t}
  simp only [NNReal.coe_one, mul_one, Pi.neg_apply] at hpos hneg
  linarith

theorem standardGaussian_density_le_one (t : ℝ) : gaussianPDFReal 0 1 t ≤ 1 := by
  rw [gaussianPDFReal]
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    apply Real.one_le_sqrt.mpr
    norm_num
    linarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
  have hexp : Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    norm_num
    nlinarith [sq_nonneg t]
  exact (mul_le_mul hinv hexp (Real.exp_pos _).le zero_le_one).trans_eq (mul_one 1)

theorem integral_standardGaussian_exp_neg_sq_le {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, Real.exp (-a * t ^ 2) ∂(gaussianReal 0 1)) ≤ Real.sqrt (Real.pi / a) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have hweight : Integrable (fun t ↦ gaussianPDFReal 0 1 t * Real.exp (-a * t ^ 2)) := by
    apply (integrable_gaussianPDFReal 0 1).mul_bdd (c := 1) (by fun_prop)
    exact Filter.Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le)
        (sq_nonneg t))
  calc
    (∫ t : ℝ, gaussianPDFReal 0 1 t * Real.exp (-a * t ^ 2)) ≤
        ∫ t : ℝ, Real.exp (-a * t ^ 2) := by
      apply integral_mono hweight (integrable_exp_neg_mul_sq ha)
      intro t
      exact mul_le_of_le_one_left (Real.exp_pos _).le (standardGaussian_density_le_one t)
    _ = _ := integral_gaussian a

end Erdos521
