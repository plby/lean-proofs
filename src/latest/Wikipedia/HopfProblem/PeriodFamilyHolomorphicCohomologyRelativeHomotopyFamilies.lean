import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyFamilyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyClosed

/-!
# The selected potential of genuine smooth coefficient families

The input is a pair of actual smooth functions on the original family.
Their rapid estimates are derived from their original Haar coefficients,
then restricted to the proved inverse neighborhood. The resulting
potential is the actual smooth selected-inverse Fourier series.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis FourierParameter RelativeFourier RelativeOperators
  PeriodTorusLineBundleClassification

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain)
  (hVU : V ≤ U) (a : Fin 2 → SmoothFamily U (Fin 4))
  (hm : SmoothPolynomiallyBoundedCoefficients V (ambientInverse P p₀))

/-- The genuine potential for the original Haar coefficients, without an
extra coefficient-decay assumption on the smooth input functions. -/
def potentialOfFamilies : SmoothFamily V (Fin 4) :=
  potentialFamily P p₀ (fun j => (a j).coefficientValue) hm
    (fun j => (smoothRapidCoefficients_actual (a j)).mono hVU)

/-- The potential keeps the original selected coefficients and literal mode sum. -/
theorem potentialOfFamilies_apply (b : V) (t : UnitAddTorus (Fin 4)) :
    potentialOfFamilies P p₀ hVU a hm (b, t) =
      ∑' k, (ambientInverse P p₀ k (b : ℂ) *
        (a (centreCoordinate p₀ (integerFrequency k))).coefficientValue k (b : ℂ)) *
          mFourier k t := rfl

/-- These are the actual Haar coefficients of the genuine potential family. -/
theorem coefficientValue_potentialOfFamilies (b : V) (k : Frequency) :
    (potentialOfFamilies P p₀ hVU a hm).coefficientValue k (b : ℂ) =
      potentialCoefficients P p₀ (fun j => (a j).coefficientValue) k (b : ℂ) :=
  coefficientValue_potentialFamily P p₀ _ hm _ b k

/-- The true base derivative of the potential is computed from its original coefficients. -/
theorem coefficientValue_d0_potentialOfFamilies (b : V) (k : Frequency) :
    (d0 (potentialOfFamilies P p₀ hVU a hm)).coefficientValue k (b : ℂ) =
      baseDbarCoefficients (potentialCoefficients P p₀ (fun j => (a j).coefficientValue))
        k (b : ℂ) :=
  coefficientValue_d0_potentialFamily P p₀ _ hm _ b k

/-- The two original genuine vertical differential operators, indexed as a pair. -/
def verticalOperator {W : Opens ℂ} (Q : HolomorphicPeriodMap ℂ W)
    (j : Fin 2) (f : SmoothFamily W (Fin 4)) : SmoothFamily W (Fin 4) :=
  if j = 0 then d1 Q f else d2 Q f

theorem coefficientValue_verticalOperator {W : Opens ℂ} (Q : HolomorphicPeriodMap ℂ W)
    (j : Fin 2) (f : SmoothFamily W (Fin 4)) (b : W) (k : Frequency) :
    (verticalOperator Q j f).coefficientValue k (b : ℂ) =
      MarkedLinear.relativeSymbol (Q.point b) (integerFrequency k) j *
        f.coefficientValue k (b : ℂ) := by
  fin_cases j
  · simpa [verticalOperator] using coefficientValue_d1 Q f k b
  · simpa [verticalOperator] using coefficientValue_d2 Q f k b

/-- Removing the zero mode commutes with the literal restriction of the
original coefficient functions, only on the actual smaller open. -/
theorem removeZero_coefficientValue_restrictFamily (f : SmoothFamily U (Fin 4))
    (b : V) (k : Frequency) :
    removeZeroCoefficients (restrictFamily hVU f).coefficientValue k (b : ℂ) =
      removeZeroCoefficients f.coefficientValue k (b : ℂ) := by
  by_cases hk : k = 0
  · subst k
    rw [removeZeroCoefficients_zero, removeZeroCoefficients_zero]
  · rw [removeZeroCoefficients_of_ne_zero _ hk, removeZeroCoefficients_of_ne_zero _ hk,
      coefficientValue_restrictFamily]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
