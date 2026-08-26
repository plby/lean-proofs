import ErdosProblems.Erdos1002.PoissonCompat
import ErdosProblems.Erdos1002.CompoundPoisson
import ErdosProblems.Erdos1002.ProbabilityFoundations
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Compound Poisson laws with an arbitrary real jump distribution

The finite-grid limits in the marked-resonance argument are compound Poisson
laws.  This file constructs the corresponding law for an arbitrary probability
distribution of one real jump.  The construction is an honest countable sum
of convolution powers with Poisson weights, and its characteristic function
is derived from that measure.  Thus later continuum-mark arguments need not
postulate the existence of a probability measure with a prescribed exponent.
-/

open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory

namespace Erdos1002

open ProbabilityTheory

noncomputable section

/-- The law of a sum of `n` independent jumps with common law `μ`. -/
def probabilityConvolutionPow (μ : ProbabilityMeasure ℝ) :
    ℕ → ProbabilityMeasure ℝ
  | 0 => ⟨Measure.dirac 0, inferInstance⟩
  | n + 1 =>
      ⟨(μ : Measure ℝ) ∗
        (probabilityConvolutionPow μ n : Measure ℝ), inferInstance⟩

@[simp]
theorem probabilityConvolutionPow_zero (μ : ProbabilityMeasure ℝ) :
    (probabilityConvolutionPow μ 0 : Measure ℝ) = Measure.dirac 0 :=
  rfl

@[simp]
theorem probabilityConvolutionPow_succ
    (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    (probabilityConvolutionPow μ (n + 1) : Measure ℝ) =
      (μ : Measure ℝ) ∗
        (probabilityConvolutionPow μ n : Measure ℝ) :=
  rfl

theorem charFun_probabilityConvolutionPow
    (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (probabilityConvolutionPow μ n : Measure ℝ) t =
      charFun (μ : Measure ℝ) t ^ n := by
  induction n with
  | zero =>
      simp [charFun_apply_real]
  | succ n ih =>
      rw [probabilityConvolutionPow_succ, charFun_conv, ih, pow_succ]
      exact mul_comm _ _

/-- The countable Poisson mixture of convolution powers. -/
def continuousCompoundPoissonMeasure
    (r : NNReal) (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ ↦
    (poissonPMF r n) • (probabilityConvolutionPow μ n : Measure ℝ)

instance continuousCompoundPoissonMeasure_isProbability
    (r : NNReal) (μ : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (continuousCompoundPoissonMeasure r μ) := by
  refine ⟨?_⟩
  rw [continuousCompoundPoissonMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using!
    (poissonPMF r).tsum_coe

/-- The compound Poisson law as a `ProbabilityMeasure`. -/
def continuousCompoundPoissonProbability
    (r : NNReal) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨continuousCompoundPoissonMeasure r μ, inferInstance⟩

@[simp]
theorem continuousCompoundPoissonProbability_toMeasure
    (r : NNReal) (μ : ProbabilityMeasure ℝ) :
    (continuousCompoundPoissonProbability r μ : Measure ℝ) =
      continuousCompoundPoissonMeasure r μ :=
  rfl

private theorem tsum_poissonPMFReal_mul_pow_eq_exp
    (r : NNReal) (z : ℂ) :
    (∑' n : ℕ, (poissonPMFReal r n : ℂ) * z ^ n) =
      Complex.exp ((r : ℂ) * (z - 1)) := by
  have h := integral_pow_poissonMeasure r z
  rw [poissonMeasure_eq_toMeasure,
    PMF.integral_eq_tsum _ _ (by
      simpa only [poissonMeasure_eq_toMeasure] using! integrable_pow_poissonMeasure r z)] at h
  simpa only [poissonPMF_toReal, smul_eq_mul] using! h

/-- Characteristic exponent of the compound Poisson law. -/
theorem charFun_continuousCompoundPoissonProbability
    (r : NNReal) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (continuousCompoundPoissonProbability r μ : Measure ℝ) t =
      Complex.exp ((r : ℂ) *
        (charFun (μ : Measure ℝ) t - 1)) := by
  rw [continuousCompoundPoissonProbability_toMeasure, charFun_apply_real]
  have hInt : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
      (continuousCompoundPoissonMeasure r μ) := by
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  rw [continuousCompoundPoissonMeasure, integral_sum_measure hInt]
  calc
    (∑' n : ℕ,
        ∫ x : ℝ, Complex.exp (t * x * Complex.I)
          ∂(poissonPMF r n) •
            (probabilityConvolutionPow μ n : Measure ℝ)) =
        ∑' n : ℕ, (poissonPMFReal r n : ℂ) *
          charFun (μ : Measure ℝ) t ^ n := by
      apply tsum_congr
      intro n
      rw [integral_smul_measure, poissonPMF_toReal,
        ← charFun_apply_real, charFun_probabilityConvolutionPow]
      rfl
    _ = Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) :=
      tsum_poissonPMFReal_mul_pow_eq_exp r
        (charFun (μ : Measure ℝ) t)

end

end Erdos1002
