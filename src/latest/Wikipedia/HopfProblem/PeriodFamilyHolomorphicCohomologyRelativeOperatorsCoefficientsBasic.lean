import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeCoefficient

/-!
# Haar coefficients of the genuine smooth-family operations

Linearity follows from the original normalized Haar integral. Vertical
differentiation uses the already proved differentiation-under-the-integral
identity for each actual torus slice. All frequencies, including zero, are
covered by these identities.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

theorem coefficientValue_add (f g : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (add f g).coefficientValue k (b : ℂ) =
      f.coefficientValue k (b : ℂ) + g.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply,
    SmoothFamily.coefficientValue_apply]
  change mFourierCoeff ((f.slice b).toContinuousMap + (g.slice b).toContinuousMap) k = _
  exact torusFourierCoeff_add (f.slice b).toContinuousMap (g.slice b).toContinuousMap k

theorem coefficientValue_sub (f g : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (f.sub g).coefficientValue k (b : ℂ) =
      f.coefficientValue k (b : ℂ) - g.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply,
    SmoothFamily.coefficientValue_apply]
  change mFourierCoeff ((f.slice b).toContinuousMap - (g.slice b).toContinuousMap) k = _
  exact torusFourierCoeff_sub (f.slice b).toContinuousMap (g.slice b).toContinuousMap k

theorem coefficientValue_constMul (a : ℂ) (f : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (constMul a f).coefficientValue k (b : ℂ) = a * f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply]
  exact torusFourierCoeff_const_mul (fun t => f (b, t)) a k

theorem coefficientValue_baseMultiply (g : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g U)
    (f : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (baseMultiply g hg f).coefficientValue k (b : ℂ) =
      g (b : ℂ) * f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply]
  exact torusFourierCoeff_const_mul (fun t => f (b, t)) (g (b : ℂ)) k

/-- The genuine vertical derivative has the exact directional Fourier multiplier. -/
theorem coefficientValue_verticalDerivative (f : SmoothFamily U d)
    (v : d → ℝ) (k : d → ℤ) (b : U) :
    (f.verticalDerivative v).coefficientValue k (b : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * (v j : ℂ)) *
        f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply]
  exact mFourierCoeff_torusDirectionalDerivative (f.slice b) v k

/-- Coordinate differentiation multiplies the original Haar coefficient by `2πI kⱼ`. -/
theorem coefficientValue_coordinateDerivative [DecidableEq d] (f : SmoothFamily U d)
    (j : d) (k : d → ℤ) (b : U) :
    (f.verticalDerivative (Pi.single j 1)).coefficientValue k (b : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply, SmoothFamily.coefficientValue_apply]
  exact mFourierCoeff_torusCoordinateDerivative (f.slice b) j k

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
