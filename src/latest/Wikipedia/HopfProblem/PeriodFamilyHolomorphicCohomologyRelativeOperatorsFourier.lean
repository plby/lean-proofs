import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsDifferential
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsCoefficientsBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearSymbol

/-!
# Exact Fourier formulas for the original relative differential operators

The two vertical multipliers are the already defined relative symbols of
the original period matrix. The base formula is actual differentiation
under the original Haar integral. There are no separate coefficient or
differential-equation assumptions.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The actual base antiholomorphic derivative commutes with the Haar coefficient. -/
theorem coefficientValue_d0 (f : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (d0 f).coefficientValue k (b : ℂ) =
      (fderiv ℝ (f.coefficientValue k) (b : ℂ) 1 +
        Complex.I * fderiv ℝ (f.coefficientValue k) (b : ℂ) Complex.I) / 2 := by
  rw [d0, coefficientValue_constMul, coefficientValue_add, coefficientValue_constMul,
    ← f.coefficientValue_fderiv_apply k (b : ℂ) b.property 1,
    ← f.coefficientValue_fderiv_apply k (b : ℂ) b.property Complex.I]
  ring

variable (P : HolomorphicPeriodMap ℂ U)

/-- The first actual operator has exactly the first original marked Fourier symbol. -/
theorem coefficientValue_d1 (f : SmoothFamily U (Fin 4)) (k : Fin 4 → ℤ) (b : U) :
    (d1 P f).coefficientValue k (b : ℂ) =
      MarkedLinear.relativeSymbol (P.point b) (integerFrequency k) 0 *
        f.coefficientValue k (b : ℂ) := by
  simp only [d1, coefficientValue_sub, coefficientValue_add, coefficientValue_baseMultiply,
    coefficientValue_coordinateDerivative, Smooth.muValue_apply, Smooth.betaValue_apply,
    MarkedLinear.relativeSymbol_zero, integerFrequency_apply, Complex.ofReal_intCast]
  ring

/-- The second actual operator has exactly the second original marked Fourier symbol. -/
theorem coefficientValue_d2 (f : SmoothFamily U (Fin 4)) (k : Fin 4 → ℤ) (b : U) :
    (d2 P f).coefficientValue k (b : ℂ) =
      MarkedLinear.relativeSymbol (P.point b) (integerFrequency k) 1 *
        f.coefficientValue k (b : ℂ) := by
  simp only [d2, coefficientValue_sub, coefficientValue_add, coefficientValue_baseMultiply,
    coefficientValue_coordinateDerivative, Smooth.tauValue_apply, Smooth.muValue_apply,
    MarkedLinear.relativeSymbol_one, integerFrequency_apply, Complex.ofReal_intCast]
  ring

/-- In particular, the genuine first vertical derivative has zero Haar mean. -/
@[simp] theorem coefficientValue_d1_zero (f : SmoothFamily U (Fin 4)) (b : U) :
    (d1 P f).coefficientValue 0 (b : ℂ) = 0 := by
  rw [coefficientValue_d1, integerFrequency_zero, map_zero, Pi.zero_apply, zero_mul]

/-- In particular, the genuine second vertical derivative has zero Haar mean. -/
@[simp] theorem coefficientValue_d2_zero (f : SmoothFamily U (Fin 4)) (b : U) :
    (d2 P f).coefficientValue 0 (b : ℂ) = 0 := by
  rw [coefficientValue_d2, integerFrequency_zero, map_zero, Pi.zero_apply, zero_mul]

/-- The first formula stated directly for the original normalized Haar integral. -/
theorem mFourierCoeff_d1 (f : SmoothFamily U (Fin 4)) (k : Fin 4 → ℤ) (b : U) :
    mFourierCoeff (fun t => d1 P f (b, t)) k =
      MarkedLinear.relativeSymbol (P.point b) (integerFrequency k) 0 *
        mFourierCoeff (fun t => f (b, t)) k := by
  simpa only [SmoothFamily.coefficientValue_apply] using coefficientValue_d1 P f k b

/-- The second formula stated directly for the original normalized Haar integral. -/
theorem mFourierCoeff_d2 (f : SmoothFamily U (Fin 4)) (k : Fin 4 → ℤ) (b : U) :
    mFourierCoeff (fun t => d2 P f (b, t)) k =
      MarkedLinear.relativeSymbol (P.point b) (integerFrequency k) 1 *
        mFourierCoeff (fun t => f (b, t)) k := by
  simpa only [SmoothFamily.coefficientValue_apply] using coefficientValue_d2 P f k b

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
