import ErdosProblems.Erdos520.HarperCDFProduct
import Mathlib.Probability.Distributions.Gaussian.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Probability laws of scheduled centered blocks

This module packages the centered prime-block sum as an honest pushforward
probability measure.  Its characteristic function is exactly the finite
product already estimated in `HarperBlockGaussian`; the comparison Gaussian
has exactly the block variance computed in `HarperPrimeBlocks`.
-/

/-- The law of a centered linearized prime block under the tilted cube. -/
noncomputable def harperCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) : Measure ℝ :=
  Measure.map (harperCenteredLinearPrimeBlockSum y S t u)
    (harperTiltedCubeLaw y t)

instance harperCenteredLinearBlockLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    IsProbabilityMeasure (harperCenteredLinearBlockLaw y S t u) := by
  unfold harperCenteredLinearBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

/-- The nonnegative-real version of the exact block variance. -/
noncomputable def harperLinearBlockVarianceNNReal
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) : NNReal :=
  ⟨harperLinearBlockVariance y S t u,
    by
      unfold harperLinearBlockVariance
      exact Finset.sum_nonneg fun p hp ↦
        harperCenteredLinearPrimeVariance_nonneg p.1 t u⟩

@[simp] theorem coe_harperLinearBlockVarianceNNReal
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (harperLinearBlockVarianceNNReal y S t u : ℝ) =
      harperLinearBlockVariance y S t u := rfl

/-- The centered Gaussian law with the same exact variance as the block. -/
noncomputable def harperGaussianBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) : Measure ℝ :=
  gaussianReal 0 (harperLinearBlockVarianceNNReal y S t u)

instance harperGaussianBlockLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    IsProbabilityMeasure (harperGaussianBlockLaw y S t u) := by
  unfold harperGaussianBlockLaw
  infer_instance

/-- The pushforward law has exactly the characteristic function previously
computed from the tilted prime coordinates. -/
theorem charFun_harperCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u v : ℝ) :
    charFun (harperCenteredLinearBlockLaw y S t u) v =
      harperTiltedLinearPrimeBlockCharacteristic y S t u v := by
  rw [charFun_apply_real]
  unfold harperCenteredLinearBlockLaw
  rw [integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  unfold harperTiltedLinearPrimeBlockCharacteristic
    harperCharacteristicBlockExponent
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    push_cast
    rfl

/-- Characteristic function of the exact variance-matched Gaussian law. -/
theorem charFun_harperGaussianBlockLaw
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u v : ℝ) :
    charFun (harperGaussianBlockLaw y S t u) v =
      Complex.exp
        (-((v ^ 2 * harperLinearBlockVariance y S t u / 2 : ℝ) : ℂ)) := by
  unfold harperGaussianBlockLaw
  rw [charFun_gaussianReal]
  simp only [coe_harperLinearBlockVarianceNNReal,
    mul_zero, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  push_cast
  ring_nf

/-- Law-level form of the arbitrary-block characteristic comparison. -/
theorem norm_charFun_harperCenteredLinearBlockLaw_sub_gaussian_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1)
    (t u v : ℝ)
    (hsmall : ∀ p ∈ S,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ S,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    ‖charFun (harperCenteredLinearBlockLaw y S t u) v -
        charFun (harperGaussianBlockLaw y S t u) v‖ ≤
      (∑ p ∈ S,
        8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
      ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by
  rw [charFun_harperCenteredLinearBlockLaw,
    charFun_harperGaussianBlockLaw]
  exact norm_harperTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
    y S h4 t u v hsmall hquad

/-- Scheduled law-level cubic-plus-quartic characteristic estimate. -/
theorem norm_charFun_harperScheduledBlockLaw_sub_gaussian_le
    (y j : ℕ) (t u v : ℝ)
    (hsmall : ∀ p ∈ harperScheduledPrimeBlock y j,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ harperScheduledPrimeBlock y j,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    ‖charFun (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v -
        charFun (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v‖ ≤
      (16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
        harperBlockGaussianQuarticBudget y
          (harperScheduledPrimeBlock y j) t u * |v| ^ 4 := by
  rw [charFun_harperCenteredLinearBlockLaw,
    charFun_harperGaussianBlockLaw]
  exact norm_harperScheduledBlockCharacteristic_sub_gaussian_le_cubic_quartic
    y j t u v hsmall hquad

end Problem520
end Erdos
