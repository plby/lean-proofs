import Wikipedia.GreenTao.Sieve.SmoothCutoffFourierProductTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The archimedean cutoff normalizer integral

For Mathlib's analyst Fourier normalization, put

`F(t) = 𝓕 (x ↦ exp(x) χ(x))(t)`

and

`W(t) = 1 - 2 π i t`.

The one-pair archimedean factor in the Goldston--Yıldırım calculation is

`∫ t, ∫ u, F(t) F(u) W(t) W(u) /
  (2 - 2 π i (t + u))`.

This file identifies it with the derivative-square normalizer

`∫_{0 < x} |χ'(x)|² dx`.

The proof records both analytic ingredients explicitly.  First,
`W(t) F(t)` is the Fourier transform of
`x ↦ -exp(x) χ'(x)`.  Second, the reciprocal denominator is the Laplace
integral

`∫_{0 < x} exp((-2 + 2 π i (t + u))x) dx`.

The remaining argument is an absolutely convergent Fubini interchange.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform LineDeriv SchwartzMap

namespace SmoothSieveCutoff

/-! ## The differentiated Fourier input -/

/-- The linear Fourier weight dictated by Mathlib's `2π` convention. -/
noncomputable def cutoffDerivativeFrequencyWeight (t : ℝ) : ℂ :=
  1 - ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

/-- The differentiated spatial Schwartz function
`g - g' = -exp(x) χ'(x)`, where `g(x) = exp(x)χ(x)`. -/
noncomputable def cutoffDerivativeSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  χ.fourierInputSchwartz -
    ∂_{(1 : ℝ)} χ.fourierInputSchwartz

/-- Fourier inversion for an arbitrary complex Schwartz function on the
real line, written in the same explicit character convention as
`inverseFourierCharacter`. -/
theorem schwartz_eq_integral_fourier_mul_inverseFourierCharacter
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    f x =
      ∫ t : ℝ,
        𝓕 (f : ℝ → ℂ) t *
          inverseFourierCharacter x t := by
  have hinversion :
      𝓕⁻ (𝓕 (f : ℝ → ℂ)) x = f x :=
    f.integrable.fourierInv_fourier_eq
      (show Integrable (𝓕 (f : ℝ → ℂ)) by
        simpa only [SchwartzMap.fourier_coe] using
          (𝓕 f).integrable)
      f.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hinversion
  symm
  simpa only [inverseFourierCharacter,
    RCLike.inner_apply, conj_trivial,
    Complex.real_smul, smul_eq_mul, mul_comm] using
    hinversion

/-- Pointwise evaluation of the differentiated spatial Schwartz
function. -/
theorem cutoffDerivativeSchwartz_apply
    (χ : SmoothSieveCutoff) (x : ℝ) :
    χ.cutoffDerivativeSchwartz x =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
  have hχdiff :
      DifferentiableAt ℝ χ.toFun x :=
    (χ.smooth.differentiable (by simp)).differentiableAt
  have hreal :
      HasDerivAt
        (Real.exp * χ.toFun)
        (Real.exp x * χ.toFun x +
          Real.exp x * deriv χ.toFun x) x := by
    simpa only [Pi.mul_apply, mul_comm, add_comm] using
      (Real.hasDerivAt_exp x).mul hχdiff.hasDerivAt
  have hcomplex :
      deriv χ.fourierInput x =
        ((Real.exp x * χ.toFun x +
          Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
    change
      deriv
          (fun y : ℝ =>
            ((Real.exp y * χ.toFun y : ℝ) : ℂ)) x =
        _
    exact hreal.ofReal_comp.deriv
  rw [cutoffDerivativeSchwartz]
  change
    χ.fourierInput x -
        fderiv ℝ χ.fourierInput x (1 : ℝ) =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ)
  rw [fderiv_apply_one_eq_deriv, hcomplex]
  simp only [fourierInput]
  push_cast
  ring

/-- The Fourier transform of the differentiated spatial input is exactly
`W(t)F(t)`. -/
theorem fourier_cutoffDerivativeSchwartz_apply
    (χ : SmoothSieveCutoff) (t : ℝ) :
    (𝓕 χ.cutoffDerivativeSchwartz :
        𝓢(ℝ, ℂ)) t =
      χ.cutoffFourierTransform t *
        cutoffDerivativeFrequencyWeight t := by
  rw [cutoffDerivativeSchwartz]
  have hsub :
      (𝓕
          (χ.fourierInputSchwartz -
            ∂_{(1 : ℝ)}
              χ.fourierInputSchwartz) :
          𝓢(ℝ, ℂ)) =
        (𝓕 χ.fourierInputSchwartz : 𝓢(ℝ, ℂ)) -
          (𝓕
            (∂_{(1 : ℝ)}
              χ.fourierInputSchwartz) :
            𝓢(ℝ, ℂ)) := by
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      (SchwartzMap.fourierTransformCLM ℂ).map_sub
        χ.fourierInputSchwartz
        (∂_{(1 : ℝ)}
          χ.fourierInputSchwartz)
  rw [hsub]
  change
    (𝓕 χ.fourierInputSchwartz : 𝓢(ℝ, ℂ)) t -
        (𝓕
          (∂_{(1 : ℝ)}
            χ.fourierInputSchwartz) :
          𝓢(ℝ, ℂ)) t =
      _
  rw [← χ.cutoffFourierSchwartz_apply t]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp [cutoffFourierSchwartz,
    cutoffDerivativeFrequencyWeight,
    SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    RCLike.inner_apply, Complex.real_smul,
    smul_eq_mul]
  ring

/-- Ordinary-function version of
`fourier_cutoffDerivativeSchwartz_apply`. -/
theorem fourier_coe_cutoffDerivativeSchwartz_apply
    (χ : SmoothSieveCutoff) (t : ℝ) :
    𝓕 (χ.cutoffDerivativeSchwartz : ℝ → ℂ) t =
      χ.cutoffFourierTransform t *
        cutoffDerivativeFrequencyWeight t := by
  rw [← SchwartzMap.fourier_coe
    χ.cutoffDerivativeSchwartz]
  exact fourier_cutoffDerivativeSchwartz_apply χ t

/-- The inverse transform of `W(t)F(t)` is
`-exp(x)χ'(x)`. -/
theorem integral_cutoffFourierTransform_mul_derivativeWeight_mul_character
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ t : ℝ,
        χ.cutoffFourierTransform t *
          cutoffDerivativeFrequencyWeight t *
            inverseFourierCharacter x t) =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
  rw [← χ.cutoffDerivativeSchwartz_apply x,
    schwartz_eq_integral_fourier_mul_inverseFourierCharacter
      χ.cutoffDerivativeSchwartz x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change
      χ.cutoffFourierTransform t *
            cutoffDerivativeFrequencyWeight t *
          inverseFourierCharacter x t =
        𝓕 (χ.cutoffDerivativeSchwartz : ℝ → ℂ) t *
          inverseFourierCharacter x t
    rw [fourier_coe_cutoffDerivativeSchwartz_apply]

/-- The weighted Fourier transform remains integrable. -/
theorem integrable_cutoffFourierTransform_mul_derivativeWeight
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun t : ℝ =>
        χ.cutoffFourierTransform t *
          cutoffDerivativeFrequencyWeight t) := by
  have h :
      Integrable
        (fun t : ℝ =>
          𝓕 χ.cutoffDerivativeSchwartz t) := by
    change Integrable
      ((𝓕 χ.cutoffDerivativeSchwartz : 𝓢(ℝ, ℂ)) :
        ℝ → ℂ)
    exact (𝓕 χ.cutoffDerivativeSchwartz).integrable
  exact h.congr
    (Filter.Eventually.of_forall fun t => by
      change
        (𝓕 χ.cutoffDerivativeSchwartz :
            𝓢(ℝ, ℂ)) t =
          χ.cutoffFourierTransform t *
            cutoffDerivativeFrequencyWeight t
      rw [fourier_cutoffDerivativeSchwartz_apply])

/-! It is useful below to give the differentiated transform a short
name. -/

/-- The Fourier transform after applying the archimedean derivative
weight. -/
noncomputable def cutoffWeightedFourier
    (χ : SmoothSieveCutoff) (t : ℝ) : ℂ :=
  χ.cutoffFourierTransform t *
    cutoffDerivativeFrequencyWeight t

theorem cutoffWeightedFourier_integrable
    (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffWeightedFourier := by
  change Integrable
    (fun t : ℝ =>
      χ.cutoffFourierTransform t *
        cutoffDerivativeFrequencyWeight t)
  exact χ.integrable_cutoffFourierTransform_mul_derivativeWeight

theorem cutoffWeightedFourier_continuous
    (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffWeightedFourier := by
  apply χ.cutoffFourierTransform_continuous.mul
  unfold cutoffDerivativeFrequencyWeight
  fun_prop

/-- Multiplication by an inverse Fourier character preserves
integrability of the differentiated transform. -/
theorem integrable_cutoffWeightedFourier_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ =>
        χ.cutoffWeightedFourier t *
          inverseFourierCharacter x t) := by
  refine χ.cutoffWeightedFourier_integrable.mul_bdd
    (c := 1) ?_ ?_
  · exact
      (continuous_inverseFourierCharacter x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_inverseFourierCharacter]

/-- Fourier inversion for the abbreviated differentiated transform. -/
theorem integral_cutoffWeightedFourier_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ t : ℝ,
        χ.cutoffWeightedFourier t *
          inverseFourierCharacter x t) =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
  simpa only [cutoffWeightedFourier] using
    χ.integral_cutoffFourierTransform_mul_derivativeWeight_mul_character x

/-! ## The Laplace kernel -/

/-- The complex denominator of the one-pair archimedean kernel. -/
noncomputable def cutoffNormalizerDenominator
    (t u : ℝ) : ℂ :=
  2 -
    ((2 * Real.pi * (t + u) : ℝ) : ℂ) *
      Complex.I

/-- The one-pair Fourier kernel in Mathlib's analyst normalization. -/
noncomputable def cutoffNormalizerKernel
    (t u : ℝ) : ℂ :=
  cutoffDerivativeFrequencyWeight t *
      cutoffDerivativeFrequencyWeight u /
    cutoffNormalizerDenominator t u

/-- The exponent in the Laplace representation of the reciprocal
denominator. -/
noncomputable def cutoffNormalizerLaplaceExponent
    (t u : ℝ) : ℂ :=
  -2 +
    ((2 * Real.pi * (t + u) : ℝ) : ℂ) *
      Complex.I

@[simp]
theorem cutoffNormalizerLaplaceExponent_re
    (t u : ℝ) :
    (cutoffNormalizerLaplaceExponent t u).re = -2 := by
  simp [cutoffNormalizerLaplaceExponent]

theorem cutoffNormalizerDenominator_eq_neg_exponent
    (t u : ℝ) :
    cutoffNormalizerDenominator t u =
      -cutoffNormalizerLaplaceExponent t u := by
  simp [cutoffNormalizerDenominator,
    cutoffNormalizerLaplaceExponent]
  ring

/-- Split the Laplace phase into its decaying real factor and the two
unitary inverse-Fourier characters. -/
theorem exp_cutoffNormalizerLaplaceExponent_mul_eq
    (t u x : ℝ) :
    Complex.exp
        (cutoffNormalizerLaplaceExponent t u * x) =
      (Real.exp (-2 * x) : ℂ) *
        inverseFourierCharacter x t *
        inverseFourierCharacter x u := by
  rw [inverseFourierCharacter, inverseFourierCharacter,
    Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  simp [cutoffNormalizerLaplaceExponent]
  ring

/-- Exact Laplace transform of the reciprocal denominator. -/
theorem integral_exp_cutoffNormalizerLaplaceExponent_Ioi
    (t u : ℝ) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp
          (cutoffNormalizerLaplaceExponent t u * x)) =
      (cutoffNormalizerDenominator t u)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi
    (a := cutoffNormalizerLaplaceExponent t u)
    (by simp)]
  rw [cutoffNormalizerDenominator_eq_neg_exponent]
  simp [div_eq_mul_inv]

/-- The scalar Laplace factor is integrable on the positive half-line. -/
theorem integrableOn_exp_cutoffNormalizerLaplaceExponent_Ioi
    (t u : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        Complex.exp
          (cutoffNormalizerLaplaceExponent t u * x))
      (Set.Ioi (0 : ℝ)) :=
  integrableOn_exp_mul_complex_Ioi (by simp) 0

/-- Exact Laplace representation of the full one-pair Fourier kernel. -/
theorem cutoffNormalizerKernel_eq_integral
    (t u : ℝ) :
    cutoffNormalizerKernel t u =
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp
            (cutoffNormalizerLaplaceExponent t u * x) *
          cutoffDerivativeFrequencyWeight t *
          cutoffDerivativeFrequencyWeight u := by
  rw [cutoffNormalizerKernel, div_eq_mul_inv,
    ← integral_exp_cutoffNormalizerLaplaceExponent_Ioi,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    ring

/-! ## Absolute convergence of the three-variable integral -/

/-- The full integrand after replacing the reciprocal denominator by its
Laplace integral.  The variables are ordered as `x, (t,u)` to make the
Fubini exchange explicit. -/
noncomputable def cutoffNormalizerTripleIntegrand
    (χ : SmoothSieveCutoff)
    (z : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.exp
      (cutoffNormalizerLaplaceExponent z.2.1 z.2.2 * z.1) *
    χ.cutoffWeightedFourier z.2.1 *
    χ.cutoffWeightedFourier z.2.2

theorem cutoffNormalizerTripleIntegrand_continuous
    (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffNormalizerTripleIntegrand := by
  unfold cutoffNormalizerTripleIntegrand
  apply Continuous.mul
  · apply Continuous.mul
    · apply Complex.continuous_exp.comp
      unfold cutoffNormalizerLaplaceExponent
      fun_prop
    · exact
        χ.cutoffWeightedFourier_continuous.comp
          continuous_snd.fst
  · exact
      χ.cutoffWeightedFourier_continuous.comp
        continuous_snd.snd

/-- Exact factorization of the norm of the three-variable integrand. -/
theorem norm_cutoffNormalizerTripleIntegrand
    (χ : SmoothSieveCutoff)
    (z : ℝ × (ℝ × ℝ)) :
    ‖χ.cutoffNormalizerTripleIntegrand z‖ =
      Real.exp (-2 * z.1) *
        ‖χ.cutoffWeightedFourier z.2.1‖ *
        ‖χ.cutoffWeightedFourier z.2.2‖ := by
  rw [cutoffNormalizerTripleIntegrand,
    exp_cutoffNormalizerLaplaceExponent_mul_eq,
    norm_mul, norm_mul, norm_mul, norm_mul,
    norm_inverseFourierCharacter,
    norm_inverseFourierCharacter]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_one]

/-- Absolute integrability on the positive Laplace half-line times the
two Fourier lines. -/
theorem cutoffNormalizerTripleIntegrand_integrable
    (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffNormalizerTripleIntegrand
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.prod volume)) := by
  have hx :
      Integrable
        (fun x : ℝ => Real.exp (-2 * x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [IntegrableOn] using
      (integrableOn_exp_mul_Ioi
        (a := (-2 : ℝ)) (by norm_num) 0)
  have htu :
      Integrable
        (fun z : ℝ × ℝ =>
          ‖χ.cutoffWeightedFourier z.1‖ *
            ‖χ.cutoffWeightedFourier z.2‖)
        (volume.prod volume) :=
    χ.cutoffWeightedFourier_integrable.norm.mul_prod
      χ.cutoffWeightedFourier_integrable.norm
  have hmajor :
      Integrable
        (fun z : ℝ × (ℝ × ℝ) =>
          Real.exp (-2 * z.1) *
            (‖χ.cutoffWeightedFourier z.2.1‖ *
              ‖χ.cutoffWeightedFourier z.2.2‖))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod
          (volume.prod volume)) :=
    hx.mul_prod htu
  refine
    (integrable_norm_iff
      χ.cutoffNormalizerTripleIntegrand_continuous.aestronglyMeasurable).mp ?_
  exact hmajor.congr
    (Filter.Eventually.of_forall fun z => by
      change
        Real.exp (-2 * z.1) *
              (‖χ.cutoffWeightedFourier z.2.1‖ *
                ‖χ.cutoffWeightedFourier z.2.2‖) =
          ‖χ.cutoffNormalizerTripleIntegrand z‖
      rw [norm_cutoffNormalizerTripleIntegrand]
      ring)

/-! ## Fubini and factorization -/

/-- The differentiated two-variable Fourier integrand. -/
noncomputable def cutoffNormalizerFourierIntegrand
    (χ : SmoothSieveCutoff) (t u : ℝ) : ℂ :=
  χ.cutoffWeightedFourier t *
      χ.cutoffWeightedFourier u /
    cutoffNormalizerDenominator t u

/-- Pointwise replacement of the reciprocal denominator by the
Laplace integral. -/
theorem cutoffNormalizerFourierIntegrand_eq_integral
    (χ : SmoothSieveCutoff) (t u : ℝ) :
    χ.cutoffNormalizerFourierIntegrand t u =
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        χ.cutoffNormalizerTripleIntegrand
          (x, (t, u)) := by
  rw [cutoffNormalizerFourierIntegrand,
    div_eq_mul_inv,
    ← integral_exp_cutoffNormalizerLaplaceExponent_Ioi,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change
      χ.cutoffWeightedFourier t *
            χ.cutoffWeightedFourier u *
          Complex.exp
            (cutoffNormalizerLaplaceExponent t u * x) =
        Complex.exp
              (cutoffNormalizerLaplaceExponent t u * x) *
            χ.cutoffWeightedFourier t *
          χ.cutoffWeightedFourier u
    ring

/-- Absolute integrability of the resulting two-variable Fourier
kernel.  This is a consequence of the stronger three-variable
absolute-convergence statement. -/
theorem cutoffNormalizerFourierIntegrand_integrable
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun z : ℝ × ℝ =>
        χ.cutoffNormalizerFourierIntegrand z.1 z.2)
      (volume.prod volume) := by
  have hinner :
      Integrable
        (fun z : ℝ × ℝ =>
          ∫ x : ℝ in Set.Ioi (0 : ℝ),
            χ.cutoffNormalizerTripleIntegrand
              (x, z))
        (volume.prod volume) :=
    χ.cutoffNormalizerTripleIntegrand_integrable.integral_prod_right
  exact hinner.congr
    (Filter.Eventually.of_forall fun z => by
      change
        (∫ x : ℝ in Set.Ioi (0 : ℝ),
            χ.cutoffNormalizerTripleIntegrand
              (x, z)) =
          χ.cutoffNormalizerFourierIntegrand z.1 z.2
      exact
        (χ.cutoffNormalizerFourierIntegrand_eq_integral
          z.1 z.2).symm)

/-- The abbreviated integrand is exactly the original expression with
two cutoff transforms and the one-pair kernel. -/
theorem cutoffFourierTransform_mul_cutoffNormalizerKernel
    (χ : SmoothSieveCutoff) (t u : ℝ) :
    χ.cutoffFourierTransform t *
        χ.cutoffFourierTransform u *
        cutoffNormalizerKernel t u =
      χ.cutoffNormalizerFourierIntegrand t u := by
  simp only [cutoffNormalizerKernel,
    cutoffNormalizerFourierIntegrand,
    cutoffWeightedFourier,
    div_eq_mul_inv]
  ring

/-- At fixed positive-half-line parameter, the two Fourier variables
factor into the square of one inverse transform. -/
theorem integral_cutoffNormalizerTripleIntegrand_pair
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerTripleIntegrand
          (x, z) ∂(volume.prod volume)) =
      (Real.exp (-2 * x) : ℂ) *
        (∫ t : ℝ,
          χ.cutoffWeightedFourier t *
            inverseFourierCharacter x t) ^ 2 := by
  calc
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerTripleIntegrand
          (x, z) ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ,
          (Real.exp (-2 * x) : ℂ) *
            ((χ.cutoffWeightedFourier z.1 *
                inverseFourierCharacter x z.1) *
              (χ.cutoffWeightedFourier z.2 *
                inverseFourierCharacter x z.2))
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change
          Complex.exp
                (cutoffNormalizerLaplaceExponent z.1 z.2 * x) *
              χ.cutoffWeightedFourier z.1 *
              χ.cutoffWeightedFourier z.2 =
            _
        rw [exp_cutoffNormalizerLaplaceExponent_mul_eq]
        ring
    _ =
        (Real.exp (-2 * x) : ℂ) *
          ∫ z : ℝ × ℝ,
            (χ.cutoffWeightedFourier z.1 *
              inverseFourierCharacter x z.1) *
            (χ.cutoffWeightedFourier z.2 *
              inverseFourierCharacter x z.2)
            ∂(volume.prod volume) := by
      exact integral_const_mul
        (Real.exp (-2 * x) : ℂ)
        (fun z : ℝ × ℝ =>
          (χ.cutoffWeightedFourier z.1 *
              inverseFourierCharacter x z.1) *
            (χ.cutoffWeightedFourier z.2 *
              inverseFourierCharacter x z.2))
    _ =
        (Real.exp (-2 * x) : ℂ) *
          (∫ t : ℝ,
            χ.cutoffWeightedFourier t *
              inverseFourierCharacter x t) ^ 2 := by
      rw [integral_prod_mul
        (fun t : ℝ =>
          χ.cutoffWeightedFourier t *
            inverseFourierCharacter x t)
        (fun u : ℝ =>
          χ.cutoffWeightedFourier u *
            inverseFourierCharacter x u)]
      ring

/-- Fourier inversion removes the exponential weights and leaves the
complexified derivative square. -/
theorem integral_cutoffNormalizerTripleIntegrand_pair_eq_deriv_sq
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerTripleIntegrand
          (x, z) ∂(volume.prod volume)) =
      (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ) := by
  rw [integral_cutoffNormalizerTripleIntegrand_pair,
    integral_cutoffWeightedFourier_mul_inverseFourierCharacter]
  have hexp :
      Real.exp (-2 * x) * (Real.exp x) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    simp
  simp only [neg_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul]
  congr 1
  calc
    Real.exp (-2 * x) *
          (Real.exp x * deriv χ.toFun x) ^ 2 =
        (Real.exp (-2 * x) * (Real.exp x) ^ 2) *
          (deriv χ.toFun x) ^ 2 := by
      ring
    _ = (deriv χ.toFun x) ^ 2 := by
      rw [hexp, one_mul]

/-- The positive-half-line integral of the complexified derivative
square is the real cutoff normalizer embedded in `ℂ`. -/
theorem integral_deriv_sq_complex_eq_normalizer
    (χ : SmoothSieveCutoff) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ)) =
      (χ.normalizer : ℂ) := by
  have hreal :
      (∫ x : ℝ in Set.Ioi (0 : ℝ),
          (deriv χ.toFun x) ^ 2) =
        χ.normalizer := by
    rw [normalizer]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change
        (deriv χ.toFun x) ^ 2 =
          |deriv χ.toFun x| ^ 2
      exact (sq_abs (deriv χ.toFun x)).symm
  calc
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ)) =
        ((show ℝ from
          ∫ x : ℝ in Set.Ioi (0 : ℝ),
            (deriv χ.toFun x) ^ 2) : ℂ) :=
      integral_ofReal
    _ = (χ.normalizer : ℂ) := by
      rw [hreal]

/-! ## The one-pair archimedean identity -/

/-- Product-measure form of the one-pair archimedean identity. -/
theorem integral_cutoffNormalizerFourierIntegrand_eq_normalizer
    (χ : SmoothSieveCutoff) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerFourierIntegrand
          z.1 z.2 ∂(volume.prod volume)) =
      (χ.normalizer : ℂ) := by
  calc
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerFourierIntegrand
          z.1 z.2 ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ,
          (∫ x : ℝ in Set.Ioi (0 : ℝ),
            χ.cutoffNormalizerTripleIntegrand
              (x, z))
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        χ.cutoffNormalizerFourierIntegrand_eq_integral
          z.1 z.2
    _ =
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (∫ z : ℝ × ℝ,
            χ.cutoffNormalizerTripleIntegrand
              (x, z) ∂(volume.prod volume)) := by
      have htriple :
          Integrable
            (Function.uncurry
              (fun x : ℝ => fun z : ℝ × ℝ =>
                χ.cutoffNormalizerTripleIntegrand
                  (x, z)))
            ((volume.restrict (Set.Ioi (0 : ℝ))).prod
              (volume.prod volume)) := by
        exact
          χ.cutoffNormalizerTripleIntegrand_integrable.congr
            (Filter.Eventually.of_forall fun z => by
              change
                χ.cutoffNormalizerTripleIntegrand z =
                  χ.cutoffNormalizerTripleIntegrand
                    (z.1, z.2)
              rw [Prod.eta])
      exact
        (integral_integral_swap
          htriple).symm
    _ =
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        χ.integral_cutoffNormalizerTripleIntegrand_pair_eq_deriv_sq x
    _ = (χ.normalizer : ℂ) :=
      χ.integral_deriv_sq_complex_eq_normalizer

/-- Absolute integrability of the original, unabbreviated one-pair
Fourier integrand. -/
theorem cutoffFourierKernelIntegrand_integrable
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun z : ℝ × ℝ =>
        χ.cutoffFourierTransform z.1 *
          χ.cutoffFourierTransform z.2 *
          cutoffNormalizerKernel z.1 z.2)
      (volume.prod volume) := by
  exact χ.cutoffNormalizerFourierIntegrand_integrable.congr
    (Filter.Eventually.of_forall fun z => by
      exact
        (χ.cutoffFourierTransform_mul_cutoffNormalizerKernel
          z.1 z.2).symm)

/-- **Exact one-pair archimedean identity.**  In Mathlib's `2π`
Fourier normalization, the double integral with kernel

`(1 - 2πit)(1 - 2πiu) / (2 - 2πi(t+u))`

is the derivative-square normalizer. -/
theorem integral_cutoffFourierTransform_pairKernel_eq_normalizer
    (χ : SmoothSieveCutoff) :
    (∫ t : ℝ, ∫ u : ℝ,
        χ.cutoffFourierTransform t *
          χ.cutoffFourierTransform u *
          cutoffNormalizerKernel t u) =
      (χ.normalizer : ℂ) := by
  calc
    (∫ t : ℝ, ∫ u : ℝ,
        χ.cutoffFourierTransform t *
          χ.cutoffFourierTransform u *
          cutoffNormalizerKernel t u) =
        ∫ t : ℝ, ∫ u : ℝ,
          χ.cutoffNormalizerFourierIntegrand t u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u =>
          χ.cutoffFourierTransform_mul_cutoffNormalizerKernel t u
    _ =
        ∫ z : ℝ × ℝ,
          χ.cutoffNormalizerFourierIntegrand
            z.1 z.2 ∂(volume.prod volume) := by
      exact
        integral_integral
          χ.cutoffNormalizerFourierIntegrand_integrable
    _ = (χ.normalizer : ℂ) :=
      χ.integral_cutoffNormalizerFourierIntegrand_eq_normalizer

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
