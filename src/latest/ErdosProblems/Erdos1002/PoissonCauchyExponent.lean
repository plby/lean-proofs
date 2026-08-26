import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.CauchyAnalysis
import ErdosProblems.Erdos1002.CompoundPoisson
import ErdosProblems.Erdos1002.Sawtooth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The real integral in the Poisson--Cauchy exponent

This file proves, by an absolutely convergent Tonelli argument, the singular
integral which fixes the scale of the limiting Cauchy law.  The proof avoids
the conditionally convergent Dirichlet integral: it represents `u⁻²` by a
positive Laplace integral and reduces the answer to
`∫ s in Ioi 0, (1 + s²)⁻¹ = π / 2`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

private def laplaceCosKernel (s u : ℝ) : ℝ :=
  s * Real.exp (-s * u) * (1 - Real.cos u)

private theorem laplaceCosKernel_nonneg {s u : ℝ} (hs : 0 ≤ s) :
    0 ≤ laplaceCosKernel s u := by
  unfold laplaceCosKernel
  exact mul_nonneg (mul_nonneg hs (Real.exp_pos _).le) (sub_nonneg.mpr (Real.cos_le_one u))

private theorem measurable_laplaceCosKernel :
    Measurable (fun z : ℝ × ℝ ↦ laplaceCosKernel z.1 z.2) := by
  unfold laplaceCosKernel
  fun_prop

private theorem integral_laplace_first (u : ℝ) (hu : 0 < u) :
    ∫ s : ℝ in Ioi 0, laplaceCosKernel s u = (1 - Real.cos u) / u ^ 2 := by
  have hbase := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (1 : ℝ)) (b := u) (by norm_num) (by norm_num) hu
  have hrewrite :
      (fun s : ℝ ↦ laplaceCosKernel s u) =
        fun s : ℝ ↦ (1 - Real.cos u) *
          (s ^ (1 : ℝ) * Real.exp (-u * s ^ (1 : ℝ))) := by
    funext s
    unfold laplaceCosKernel
    simp only [Real.rpow_one]
    have hexp : Real.exp (-s * u) = Real.exp (-u * s) := by
      congr 1
      ring
    rw [hexp]
    ring
  rw [hrewrite, integral_const_mul, hbase]
  norm_num [Real.Gamma_two]
  rfl

private theorem integrableOn_laplace_first (u : ℝ) (hu : 0 < u) :
    IntegrableOn (fun s : ℝ ↦ laplaceCosKernel s u) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun s : ℝ ↦ s ^ (1 : ℝ) * Real.exp (-u * s ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (b := u) (by norm_num) (by norm_num) hu
  have hmul : IntegrableOn
      (fun s : ℝ ↦ (1 - Real.cos u) *
        (s ^ (1 : ℝ) * Real.exp (-u * s ^ (1 : ℝ)))) (Ioi 0) :=
    Integrable.const_mul hbase (1 - Real.cos u)
  refine hmul.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  unfold laplaceCosKernel
  simp only [Real.rpow_one]
  have hexp : Real.exp (-s * u) = Real.exp (-u * s) := by
    congr 1
    ring
  rw [hexp]
  ring

private theorem integral_exp_cos_Ioi (s : ℝ) (hs : 0 < s) :
    ∫ u : ℝ in Ioi 0, Real.exp (-s * u) * Real.cos u = s / (s ^ 2 + 1) := by
  let c : ℂ := (-s : ℝ) + Complex.I
  have hc : c.re < 0 := by simp [c, hs]
  have hint : IntegrableOn (fun u : ℝ ↦ Complex.exp (c * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hc 0
  have hfun :
      (fun u : ℝ ↦ (Complex.exp (c * u)).re) =
        fun u : ℝ ↦ Real.exp (-s * u) * Real.cos u := by
    funext u
    rw [Complex.exp_re]
    simp [c]
  calc
    (∫ u : ℝ in Ioi 0, Real.exp (-s * u) * Real.cos u) =
        ∫ u : ℝ in Ioi 0, (Complex.exp (c * u)).re := by rw [hfun]
    _ = (∫ u : ℝ in Ioi 0, Complex.exp (c * u)).re := integral_re hint
    _ = (-Complex.exp (c * (0 : ℝ)) / c).re := by
      rw [integral_exp_mul_complex_Ioi hc]
    _ = s / (s ^ 2 + 1) := by
      simp only [neg_div, Complex.neg_re]
      simp [Complex.normSq, c]
      field_simp

private theorem integrableOn_exp_cos_Ioi (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u) * Real.cos u) (Ioi 0) := by
  have hbase := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  refine hbase.mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with u
  simpa only [Real.norm_eq_abs] using! Real.abs_cos_le_one u

private theorem integral_laplace_second (s : ℝ) (hs : 0 < s) :
    ∫ u : ℝ in Ioi 0, laplaceCosKernel s u = (1 + s ^ 2)⁻¹ := by
  have hexp :
      ∫ u : ℝ in Ioi 0, Real.exp (-s * u) = 1 / s := by
    rw [integral_exp_mul_Ioi (a := -s) (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hs.ne']
  have hExpInt := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  have hCosInt := integrableOn_exp_cos_Ioi s hs
  unfold laplaceCosKernel
  calc
    (∫ u : ℝ in Ioi 0, s * Real.exp (-s * u) * (1 - Real.cos u)) =
        ∫ u : ℝ in Ioi 0,
          s * (Real.exp (-s * u) - Real.exp (-s * u) * Real.cos u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      ring
    _ = s * (∫ u : ℝ in Ioi 0,
          Real.exp (-s * u) - Real.exp (-s * u) * Real.cos u) := by
      rw [integral_const_mul]
    _ = s * ((∫ u : ℝ in Ioi 0, Real.exp (-s * u)) -
          ∫ u : ℝ in Ioi 0, Real.exp (-s * u) * Real.cos u) := by
      rw [← integral_sub hExpInt hCosInt]
    _ = (1 + s ^ 2)⁻¹ := by
      rw [hexp, integral_exp_cos_Ioi s hs]
      field_simp [hs.ne']
      ring

private theorem integrableOn_laplace_second (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦ laplaceCosKernel s u) (Ioi 0) := by
  have hExpInt := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  have hCosInt := integrableOn_exp_cos_Ioi s hs
  have hsub := hExpInt.sub hCosInt
  have hmul : IntegrableOn
      (fun u : ℝ ↦ s *
        (Real.exp (-s * u) - Real.exp (-s * u) * Real.cos u)) (Ioi 0) :=
    Integrable.const_mul hsub s
  refine hmul.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  unfold laplaceCosKernel
  ring

private theorem one_sub_cos_div_sq_facts :
    IntegrableOn (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) (Ioi 0) ∧
      ∫ u : ℝ in Ioi 0, (1 - Real.cos u) / u ^ 2 = Real.pi / 2 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (laplaceCosKernel z.1 z.2)
  have hF : Measurable F := by
    exact measurable_laplaceCosKernel.ennreal_ofReal
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := μ)
    (f := fun s u ↦ F (s, u)) hF.aemeasurable
  have hfirst (u : ℝ) (hu : 0 < u) :
      (∫⁻ s, F (s, u) ∂μ) = ENNReal.ofReal ((1 - Real.cos u) / u ^ 2) := by
    rw [show (∫⁻ s, F (s, u) ∂μ) =
        ∫⁻ s in Ioi 0, ENNReal.ofReal (laplaceCosKernel s u) by rfl]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_laplace_first u hu)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact laplaceCosKernel_nonneg hs.le)]
    rw [integral_laplace_first u hu]
  have hsecond (s : ℝ) (hs : 0 < s) :
      (∫⁻ u, F (s, u) ∂μ) = ENNReal.ofReal ((1 + s ^ 2)⁻¹) := by
    rw [show (∫⁻ u, F (s, u) ∂μ) =
        ∫⁻ u in Ioi 0, ENNReal.ofReal (laplaceCosKernel s u) by rfl]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_laplace_second s hs)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact laplaceCosKernel_nonneg hs.le)]
    rw [integral_laplace_second s hs]
  have hlin :
      (∫⁻ u, ENNReal.ofReal ((1 - Real.cos u) / u ^ 2) ∂μ) =
        ∫⁻ s, ENNReal.ofReal ((1 + s ^ 2)⁻¹) ∂μ := by
    calc
      (∫⁻ u, ENNReal.ofReal ((1 - Real.cos u) / u ^ 2) ∂μ) =
          ∫⁻ u, (∫⁻ s, F (s, u) ∂μ) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact (hfirst u hu).symm
      _ = ∫⁻ s, (∫⁻ u, F (s, u) ∂μ) ∂μ := hswap.symm
      _ = ∫⁻ s, ENNReal.ofReal ((1 + s ^ 2)⁻¹) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hsecond s hs
  have hnonneg : ∀ᵐ u ∂μ, 0 ≤ (1 - Real.cos u) / u ^ 2 := by
    filter_upwards with u
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one u)) (sq_nonneg u)
  have hrhs :
      (∫⁻ s, ENNReal.ofReal ((1 + s ^ 2)⁻¹) ∂μ) =
        ENNReal.ofReal (Real.pi / 2) := by
    rw [show (∫⁻ s, ENNReal.ofReal ((1 + s ^ 2)⁻¹) ∂μ) =
        ∫⁻ s in Ioi 0, ENNReal.ofReal ((1 + s ^ 2)⁻¹) by rfl]
    rw [← ofReal_integral_eq_lintegral_ofReal
      integrable_inv_one_add_sq.integrableOn]
    · simp
    · filter_upwards with s
      positivity
  have htargetInt : Integrable (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) μ := by
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) μ :=
      ((measurable_const.sub Real.continuous_cos.measurable).div
        (measurable_id.pow_const 2)).aestronglyMeasurable
    rw [← lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg]
    rw [hlin, hrhs]
    exact ENNReal.ofReal_ne_top
  refine ⟨htargetInt, ?_⟩
  rw [← ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg_of_ae hnonneg) (by positivity)]
  rw [ofReal_integral_eq_lintegral_ofReal htargetInt hnonneg]
  rw [hlin, hrhs]

private theorem integrableOn_one_sub_cos_div_sq :
    IntegrableOn (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) (Ioi 0) :=
  one_sub_cos_div_sq_facts.1

private theorem integral_one_sub_cos_div_sq :
    ∫ u : ℝ in Ioi 0, (1 - Real.cos u) / u ^ 2 = Real.pi / 2 :=
  one_sub_cos_div_sq_facts.2

private theorem integrableOn_Ioi_cos_inv_sub_one (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun ξ : ℝ ↦ Real.cos (a / ξ) - 1) (Ioi 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  let h : ℝ → ℝ := fun u ↦ (1 - Real.cos u) / u ^ 2
  have hcomp : IntegrableOn (fun x : ℝ ↦ h (a * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff h 0 ha).2 (by
      simpa [h] using! integrableOn_one_sub_cos_div_sq)
  have hmain0 : IntegrableOn (fun x : ℝ ↦ -(a ^ 2 * h (a * x))) (Ioi 0) :=
    (Integrable.const_mul hcomp (a ^ 2)).neg
  have hmain : IntegrableOn
      (fun x : ℝ ↦ (Real.cos (a * x) - 1) / x ^ 2) (Ioi 0) := by
    refine hmain0.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : x ≠ 0 := hx.ne'
      dsimp [h]
      field_simp [ha.ne', hx0]
      all_goals ring)
  apply (integrableOn_Ioi_comp_rpow_iff
    (fun ξ : ℝ ↦ Real.cos (a / ξ) - 1) (p := (-1 : ℝ)) (by norm_num)).mp
  refine hmain.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : x ≠ 0 := hx.ne'
    simp only [abs_neg, abs_one, one_mul, sub_eq_add_neg]
    norm_num
    rw [Real.rpow_neg hx.le]
    simp only [Real.rpow_one]
    field_simp [hx0])

theorem integral_Ioi_cos_inv_sub_one (a : ℝ) (ha : 0 ≤ a) :
    ∫ ξ : ℝ in Ioi 0, (Real.cos (a / ξ) - 1) = -Real.pi * a / 2 := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have hinv := integral_comp_rpow_Ioi
    (g := fun ξ : ℝ ↦ Real.cos (a / ξ) - 1) (p := (-1 : ℝ)) (by norm_num)
  have hinv' :
      (∫ x : ℝ in Ioi 0, (Real.cos (a * x) - 1) / x ^ 2) =
        ∫ ξ : ℝ in Ioi 0, (Real.cos (a / ξ) - 1) := by
    rw [← hinv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    simp only [abs_neg, abs_one, one_mul, sub_eq_add_neg]
    norm_num
    rw [Real.rpow_neg hx.le]
    simp only [Real.rpow_one]
    field_simp [hx0]
  rw [← hinv']
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ ↦ (1 - Real.cos u) / u ^ 2) 0 ha
  have hscale' :
      (∫ x : ℝ in Ioi 0, (1 - Real.cos (a * x)) / (a * x) ^ 2) =
        a⁻¹ * (Real.pi / 2) := by
    simpa only [mul_zero, inv_smul_smul₀, smul_eq_mul,
      integral_one_sub_cos_div_sq] using! hscale
  calc
    (∫ x : ℝ in Ioi 0, (Real.cos (a * x) - 1) / x ^ 2) =
        -(∫ x : ℝ in Ioi 0, (1 - Real.cos (a * x)) / x ^ 2) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      ring
    _ = -(a ^ 2 *
        ∫ x : ℝ in Ioi 0, (1 - Real.cos (a * x)) / (a * x) ^ 2) := by
      congr 1
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := hx.ne'
      field_simp [ha.ne', hx0]
    _ = -Real.pi * a / 2 := by
      rw [hscale']
      field_simp [ha.ne']

/-- The compact truncations converge to the singular integral.  This is the
one-dimensional dominated-convergence step used in the Poisson exponent. -/
theorem tendsto_intervalIntegral_cos_inv_sub_one (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun A : ℝ ↦ ∫ ξ : ℝ in 0..A, (Real.cos (a / ξ) - 1)) atTop
      (𝓝 (-Real.pi * a / 2)) := by
  rw [← integral_Ioi_cos_inv_sub_one a ha]
  exact intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_Ioi_cos_inv_sub_one a ha) tendsto_id

/-- Integration over the uniform Bernoulli mark gives the exact unnormalised
Poisson exponent.  The order here is mark first, then the positive resonance
coordinate; all inner integrals are absolutely convergent. -/
theorem intervalIntegral_integral_Ioi_bernoulliMark_exponent (t : ℝ) :
    (∫ u : ℝ in 0..1,
      ∫ ξ : ℝ in Ioi 0, (Real.cos (t * bernoulliMark u / ξ) - 1)) =
        -Real.pi * |t| / 24 := by
  have hinner (u : ℝ) :
      (∫ ξ : ℝ in Ioi 0, (Real.cos (t * bernoulliMark u / ξ) - 1)) =
        -Real.pi * (|t| * bernoulliMark u) / 2 := by
    have ha : 0 ≤ |t| * bernoulliMark u :=
      mul_nonneg (abs_nonneg t) (bernoulliMark_nonneg u)
    rw [← integral_Ioi_cos_inv_sub_one (|t| * bernoulliMark u) ha]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ hξ
    have hξabs : |ξ| = ξ := abs_of_pos hξ
    have habs : |t * bernoulliMark u / ξ| = |t| * bernoulliMark u / ξ := by
      rw [abs_div, abs_mul, abs_of_nonneg (bernoulliMark_nonneg u),
        hξabs]
    change Real.cos (t * bernoulliMark u / ξ) - 1 =
      Real.cos (|t| * bernoulliMark u / ξ) - 1
    rw [← Real.cos_abs (t * bernoulliMark u / ξ), habs]
  rw [show (fun u : ℝ ↦
      ∫ ξ : ℝ in Ioi 0, (Real.cos (t * bernoulliMark u / ξ) - 1)) =
      (fun u : ℝ ↦ (-Real.pi * |t| / 2) * bernoulliMark u) by
        funext u
        rw [hinner]
        ring]
  calc
    (∫ u : ℝ in 0..1, (-Real.pi * |t| / 2) * bernoulliMark u) =
        (-Real.pi * |t| / 2) * (∫ u : ℝ in 0..1, bernoulliMark u) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -Real.pi * |t| / 24 := by
      rw [integral_bernoulliMark]
      ring

/-- After multiplying by the symmetric Poisson intensity
`2 / (π² / 6)`, the exponent is exactly that of the limiting Cauchy law. -/
theorem poissonCauchyExponent_eq (t : ℝ) :
    (2 / (Real.pi ^ 2 / 6)) *
        (∫ u : ℝ in 0..1,
          ∫ ξ : ℝ in Ioi 0, (Real.cos (t * bernoulliMark u / ξ) - 1)) =
      -|t| / (2 * Real.pi) := by
  rw [intervalIntegral_integral_Ioi_bernoulliMark_exponent]
  field_simp [Real.pi_ne_zero]
  ring

/-- The exponential of the computed Poisson exponent is the characteristic
function of `cauchyLimitProbability`. -/
theorem exp_poissonCauchyExponent_eq_charFun (t : ℝ) :
    Complex.exp
        ((2 / (Real.pi ^ 2 / 6)) *
          (∫ u : ℝ in 0..1,
            ∫ ξ : ℝ in Ioi 0,
              (Real.cos (t * bernoulliMark u / ξ) - 1)) : ℝ) =
      charFun (cauchyLimitProbability : Measure ℝ) t := by
  rw [poissonCauchyExponent_eq, charFun_cauchyLimitProbability]
  congr 1
  norm_cast
  ring

end

end Erdos1002
