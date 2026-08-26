import ErdosProblems.Erdos1002.ContinuousCompoundPoisson
import ErdosProblems.Erdos1002.PoissonFactorialConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# First and second moments of a centered compound-Poisson law

This file supplies the moment calculation needed for quantitative deletion
of compact transition bands.  The proof starts from the literal convolution
mixture defining `continuousCompoundPoissonProbability`: it proves moment
identities for convolution powers and then justifies the countable Poisson
mixture by an explicit nonnegative `lintegral` computation.  Thus no
differentiation of a characteristic function, and no hidden uniform
integrability assertion, is used.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1002

noncomputable section

open ProbabilityTheory

theorem integrable_id_conv_of_integrable
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hν : Integrable (fun x : ℝ ↦ x) ν) :
    Integrable (fun x : ℝ ↦ x) (μ ∗ ν) := by
  unfold Measure.conv
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_apply] using!
    (hμ.comp_fst ν).add (hν.comp_snd μ)

theorem integrable_sq_conv_of_integrable
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hν : Integrable (fun x : ℝ ↦ x ^ 2) ν) :
    Integrable (fun x : ℝ ↦ x ^ 2) (μ ∗ ν) := by
  unfold Measure.conv
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have hbound : Integrable
      (fun z : ℝ × ℝ ↦ 2 * z.1 ^ 2 + 2 * z.2 ^ 2) (μ.prod ν) :=
    ((hμ.comp_fst ν).const_mul 2).add ((hν.comp_snd μ).const_mul 2)
  apply hbound.mono (by fun_prop)
  filter_upwards with z
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (z.1 - z.2)]

theorem integral_id_conv_eq_add
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hν : Integrable (fun x : ℝ ↦ x) ν) :
    (∫ x : ℝ, x ∂(μ ∗ ν)) =
      (∫ x : ℝ, x ∂μ) + ∫ x : ℝ, x ∂ν := by
  rw [integral_conv (integrable_id_conv_of_integrable μ ν hμ hν)]
  have hinner (x : ℝ) :
      (∫ y : ℝ, x + y ∂ν) = x + ∫ y : ℝ, y ∂ν := by
    rw [integral_add (integrable_const x) hν, integral_const]
    simp
  simp_rw [hinner]
  rw [integral_add hμ (integrable_const _), integral_const]
  simp

theorem integral_sq_conv_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν) :
    (∫ x : ℝ, x ^ 2 ∂(μ ∗ ν)) =
      (∫ x : ℝ, x ^ 2 ∂μ) +
        2 * (∫ x : ℝ, x ∂μ) * (∫ x : ℝ, x ∂ν) +
        ∫ x : ℝ, x ^ 2 ∂ν := by
  rw [integral_conv (integrable_sq_conv_of_integrable μ ν hμ2 hν2)]
  have hinner (x : ℝ) :
      (∫ y : ℝ, (x + y) ^ 2 ∂ν) =
        x ^ 2 + 2 * x * (∫ y : ℝ, y ∂ν) +
          ∫ y : ℝ, y ^ 2 ∂ν := by
    have hconst : Integrable (fun _y : ℝ ↦ x ^ 2) ν := integrable_const _
    have hlin : Integrable (fun y : ℝ ↦ 2 * x * y) ν := hν1.const_mul _
    calc
      (∫ y : ℝ, (x + y) ^ 2 ∂ν) =
          ∫ y : ℝ, (x ^ 2 + 2 * x * y) + y ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ = _ := by
        calc
          (∫ y : ℝ, x ^ 2 + 2 * x * y + y ^ 2 ∂ν) =
              (∫ y : ℝ, x ^ 2 ∂ν) +
                ∫ y : ℝ, 2 * x * y + y ^ 2 ∂ν := by
            simpa only [Pi.add_apply, add_assoc] using!
              integral_add hconst (hlin.add hν2)
          _ = (∫ y : ℝ, x ^ 2 ∂ν) +
                ((∫ y : ℝ, 2 * x * y ∂ν) +
                  ∫ y : ℝ, y ^ 2 ∂ν) := by
            rw [integral_add hlin hν2]
          _ = _ := by
            rw [integral_const, integral_const_mul]
            simp
            ring
  simp_rw [hinner]
  have hc1 : Integrable
      (fun _x : ℝ ↦ ∫ y : ℝ, y ^ 2 ∂ν) μ := integrable_const _
  have hcross : Integrable
      (fun x : ℝ ↦ 2 * x * (∫ y : ℝ, y ∂ν)) μ := by
    simpa only [mul_assoc] using!
      (hμ1.mul_const (∫ y : ℝ, y ∂ν)).const_mul 2
  have hcrossIntegral :
      (∫ x : ℝ, 2 * x * (∫ y : ℝ, y ∂ν) ∂μ) =
        2 * (∫ x : ℝ, x ∂μ) * (∫ y : ℝ, y ∂ν) := by
    calc
      (∫ x : ℝ, 2 * x * (∫ y : ℝ, y ∂ν) ∂μ) =
          ∫ x : ℝ, 2 * (x * (∫ y : ℝ, y ∂ν)) ∂μ := by
        congr 1
        funext x
        ring
      _ = 2 * (∫ x : ℝ, x * (∫ y : ℝ, y ∂ν) ∂μ) := by
        rw [integral_const_mul]
      _ = _ := by
        rw [integral_mul_const]
        ring
  calc
    (∫ x : ℝ,
        x ^ 2 + 2 * x * (∫ y : ℝ, y ∂ν) +
          ∫ y : ℝ, y ^ 2 ∂ν ∂μ) =
        (∫ x : ℝ, x ^ 2 ∂μ) +
          (∫ x : ℝ, 2 * x * (∫ y : ℝ, y ∂ν) ∂μ) +
          ∫ _x : ℝ, (∫ y : ℝ, y ^ 2 ∂ν) ∂μ := by
      simpa only [Pi.add_apply, add_assoc] using!
        (integral_add (hμ2.add hcross) hc1).trans
          (congrArg (fun q ↦ q + ∫ _x : ℝ,
              (∫ y : ℝ, y ^ 2 ∂ν) ∂μ)
            (integral_add hμ2 hcross))
    _ = _ := by
      rw [integral_const, hcrossIntegral]
      simp

theorem integrable_id_probabilityConvolutionPow
    (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) :
    ∀ n : ℕ, Integrable (fun x : ℝ ↦ x)
      (probabilityConvolutionPow μ n : Measure ℝ) := by
  intro n
  induction n with
  | zero => exact integrable_dirac (by simp)
  | succ n ih =>
      rw [probabilityConvolutionPow_succ]
      exact integrable_id_conv_of_integrable _ _ hμ ih

theorem integral_id_probabilityConvolutionPow_eq_zero
    (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hmean : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0) :
    ∀ n : ℕ, (∫ x : ℝ, x
      ∂(probabilityConvolutionPow μ n : Measure ℝ)) = 0 := by
  intro n
  induction n with
  | zero => simp [probabilityConvolutionPow]
  | succ n ih =>
      rw [probabilityConvolutionPow_succ,
        integral_id_conv_eq_add _ _ hμ
          (integrable_id_probabilityConvolutionPow μ hμ n),
        hmean, ih, add_zero]

theorem integrable_sq_probabilityConvolutionPow
    (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ 2)
      (probabilityConvolutionPow μ n : Measure ℝ) := by
  intro n
  induction n with
  | zero => exact integrable_dirac (by simp)
  | succ n ih =>
      rw [probabilityConvolutionPow_succ]
      exact integrable_sq_conv_of_integrable _ _ hμ ih

theorem integral_sq_probabilityConvolutionPow_eq
    (μ : ProbabilityMeasure ℝ)
    (hμ1 : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hmean : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    ∀ n : ℕ, (∫ x : ℝ, x ^ 2
      ∂(probabilityConvolutionPow μ n : Measure ℝ)) =
        (n : ℝ) * ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ) := by
  intro n
  induction n with
  | zero => simp [probabilityConvolutionPow]
  | succ n ih =>
      rw [probabilityConvolutionPow_succ,
        integral_sq_conv_eq _ _ hμ1
          (integrable_id_probabilityConvolutionPow μ hμ1 n) hμ2
          (integrable_sq_probabilityConvolutionPow μ hμ2 n),
        hmean,
        integral_id_probabilityConvolutionPow_eq_zero μ hμ1 hmean,
        ih]
      push_cast
      ring

private lemma poissonPMFReal_mul_nat_succ
    (r : NNReal) (m : ℕ) :
    poissonPMFReal r (m + 1) * (m + 1 : ℝ) =
      (r : ℝ) * poissonPMFReal r m := by
  unfold poissonPMFReal
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem hasSum_poissonPMFReal_mul_nat (r : NNReal) :
    HasSum (fun n : ℕ ↦ poissonPMFReal r n * (n : ℝ)) (r : ℝ) := by
  let f : ℕ → ℝ := fun n ↦ poissonPMFReal r n * (n : ℝ)
  have htail : HasSum (fun m : ℕ ↦ f (m + 1)) (r : ℝ) := by
    have hscaled : HasSum
        (fun m : ℕ ↦ (r : ℝ) * poissonPMFReal r m) (r : ℝ) := by
      simpa using! HasSum.mul_left (r : ℝ) (poissonPMFRealSum r)
    apply HasSum.congr_fun hscaled
    intro m
    simpa only [f, Nat.cast_add, Nat.cast_one] using!
      poissonPMFReal_mul_nat_succ r m
  have hfull : HasSum f ((r : ℝ) + ∑ i ∈ Finset.range 1, f i) :=
    (hasSum_nat_add_iff 1).mp htail
  simpa [f] using! hfull

/-- A centered square-integrable jump law gives a square-integrable
compound-Poisson law.  The proof explicitly sums the conditional second
moments against the Poisson weights. -/
theorem integrable_sq_continuousCompoundPoissonProbability_of_centered
    (r : NNReal) (μ : ProbabilityMeasure ℝ)
    (hμ1 : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hmean : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      (continuousCompoundPoissonProbability r μ : Measure ℝ) := by
  let s : ℝ := ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact integral_nonneg (fun x ↦ sq_nonneg x)
  have hpowInt (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ 2)
      (probabilityConvolutionPow μ n : Measure ℝ) :=
    integrable_sq_probabilityConvolutionPow μ hμ2 n
  have hpowMoment (n : ℕ) :
      (∫ x : ℝ, x ^ 2
        ∂(probabilityConvolutionPow μ n : Measure ℝ)) = (n : ℝ) * s := by
    simpa only [s] using!
      integral_sq_probabilityConvolutionPow_eq μ hμ1 hmean hμ2 n
  have hpowLIntegral (n : ℕ) :
      (∫⁻ x : ℝ, ‖x ^ 2‖ₑ
        ∂(probabilityConvolutionPow μ n : Measure ℝ)) =
        ENNReal.ofReal ((n : ℝ) * s) := by
    have hnonneg : ∀ᵐ x : ℝ
        ∂(probabilityConvolutionPow μ n : Measure ℝ), 0 ≤ x ^ 2 :=
      Eventually.of_forall fun x ↦ sq_nonneg x
    calc
      (∫⁻ x : ℝ, ‖x ^ 2‖ₑ
          ∂(probabilityConvolutionPow μ n : Measure ℝ)) =
          ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2)
            ∂(probabilityConvolutionPow μ n : Measure ℝ) := by
        apply lintegral_congr
        intro x
        exact Real.enorm_eq_ofReal (sq_nonneg x)
      _ = ENNReal.ofReal
          (∫ x : ℝ, x ^ 2
            ∂(probabilityConvolutionPow μ n : Measure ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal (hpowInt n) hnonneg).symm
      _ = _ := by rw [hpowMoment n]
  have hseries : HasSum
      (fun n : ℕ ↦ poissonPMFReal r n * ((n : ℝ) * s))
      ((r : ℝ) * s) := by
    simpa only [mul_assoc] using!
      (hasSum_poissonPMFReal_mul_nat r).mul_right s
  constructor
  · fun_prop
  · rw [continuousCompoundPoissonProbability_toMeasure,
      continuousCompoundPoissonMeasure]
    change (∫⁻ x : ℝ, ‖x ^ 2‖ₑ
      ∂Measure.sum (fun n : ℕ ↦
        (poissonPMF r n) •
          (probabilityConvolutionPow μ n : Measure ℝ))) < ⊤
    rw [lintegral_sum_measure]
    calc
      (∑' n : ℕ, ∫⁻ x : ℝ, ‖x ^ 2‖ₑ
          ∂(poissonPMF r n) •
            (probabilityConvolutionPow μ n : Measure ℝ)) =
          ∑' n : ℕ, ENNReal.ofReal
            (poissonPMFReal r n * ((n : ℝ) * s)) := by
        apply tsum_congr
        intro n
        rw [lintegral_smul_measure, hpowLIntegral n]
        change poissonPMF r n * ENNReal.ofReal ((n : ℝ) * s) = _
        rw [show poissonPMF r n =
          ENNReal.ofReal (poissonPMFReal r n) by rfl,
          ← ENNReal.ofReal_mul poissonPMFReal_nonneg]
      _ = ENNReal.ofReal (∑' n : ℕ,
          poissonPMFReal r n * ((n : ℝ) * s)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n ↦ mul_nonneg poissonPMFReal_nonneg
            (mul_nonneg (Nat.cast_nonneg n) hs0))
          hseries.summable).symm
      _ = ENNReal.ofReal ((r : ℝ) * s) := by rw [hseries.tsum_eq]
      _ < ⊤ := ENNReal.ofReal_lt_top

/-- Exact second moment of a centered compound-Poisson law:
`E[S²] = rate * E[J²]`. -/
theorem integral_sq_continuousCompoundPoissonProbability_of_centered
    (r : NNReal) (μ : ProbabilityMeasure ℝ)
    (hμ1 : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hmean : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 0)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    (∫ x : ℝ, x ^ 2
      ∂(continuousCompoundPoissonProbability r μ : Measure ℝ)) =
      (r : ℝ) * ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ) := by
  let s : ℝ := ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)
  have hseries : HasSum
      (fun n : ℕ ↦ poissonPMFReal r n * ((n : ℝ) * s))
      ((r : ℝ) * s) := by
    simpa only [mul_assoc] using!
      (hasSum_poissonPMFReal_mul_nat r).mul_right s
  have hInt := integrable_sq_continuousCompoundPoissonProbability_of_centered
    r μ hμ1 hmean hμ2
  rw [continuousCompoundPoissonProbability_toMeasure,
    continuousCompoundPoissonMeasure] at hInt ⊢
  rw [integral_sum_measure hInt]
  calc
    (∑' n : ℕ,
        ∫ x : ℝ, x ^ 2
          ∂(poissonPMF r n) •
            (probabilityConvolutionPow μ n : Measure ℝ)) =
      ∑' n : ℕ, poissonPMFReal r n * ((n : ℝ) * s) := by
      apply tsum_congr
      intro n
      rw [integral_smul_measure, poissonPMF_toReal,
        integral_sq_probabilityConvolutionPow_eq μ hμ1 hmean hμ2]
      simp only [smul_eq_mul, s]
    _ = (r : ℝ) * s := hseries.tsum_eq
    _ = _ := by rfl

end

end Erdos1002
