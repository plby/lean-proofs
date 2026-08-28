import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyBase
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyRestriction
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisMean

/-!
# The actual smooth selected-inverse potential family

The original inverse and selected coefficients define their literal
smooth Fourier sum. Its Haar coefficients are the original potential
coefficients. The real derivative of those coefficients, including the
base antiholomorphic derivative, is unchanged by passing to the genuine
smooth family because their functions agree on the original open base.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis FourierParameter RelativeFourier PeriodTorusLineBundleClassification

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain)
  (a : Fin 2 → Coefficients)
  (hm : SmoothPolynomiallyBoundedCoefficients V (ambientInverse P p₀))
  (ha : ∀ j, SmoothRapidCoefficients V (a j))

/-- The genuine smooth family obtained from the original selected inverse. -/
def potentialFamily : SmoothFamily V (Fin 4) :=
  smoothFamily (potentialCoefficients_rapid P p₀ a hm ha)

/-- Its values are exactly the original selected-inverse Fourier sum. -/
theorem potentialFamily_apply (b : V) (t : UnitAddTorus (Fin 4)) :
    potentialFamily P p₀ a hm ha (b, t) =
      ∑' k, (ambientInverse P p₀ k (b : ℂ) * selectedCoefficients p₀ a k (b : ℂ)) *
        mFourier k t := rfl

/-- Haar integration recovers the original potential coefficient. -/
theorem coefficientValue_potentialFamily (b : V) (k : Frequency) :
    (potentialFamily P p₀ a hm ha).coefficientValue k (b : ℂ) =
      potentialCoefficients P p₀ a k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply]
  exact mFourierCoeff_synthesis (potentialCoefficients_rapid P p₀ a hm ha) b k

/-- The actual ambient coefficients agree near each original base point. -/
theorem coefficientValue_potentialFamily_eventuallyEq (b : V) (k : Frequency) :
    (potentialFamily P p₀ a hm ha).coefficientValue k =ᶠ[𝓝 (b : ℂ)]
      potentialCoefficients P p₀ a k :=
  Filter.Eventually.mono (V.isOpen.mem_nhds b.property) (fun z hz =>
    coefficientValue_potentialFamily P p₀ a hm ha ⟨z, hz⟩ k)

/-- The genuine base operator has the actual base derivative of the
original potential coefficients. -/
theorem coefficientValue_d0_potentialFamily (b : V) (k : Frequency) :
    (RelativeOperators.d0 (potentialFamily P p₀ a hm ha)).coefficientValue k (b : ℂ) =
      baseDbarCoefficients (potentialCoefficients P p₀ a) k (b : ℂ) := by
  rw [RelativeOperators.coefficientValue_d0,
    (coefficientValue_potentialFamily_eventuallyEq P p₀ a hm ha b k).fderiv_eq,
    baseDbarCoefficients_apply]

/-- The first actual relative derivative uses the unchanged original period symbol. -/
theorem coefficientValue_d1_potentialFamily (hVU : V ≤ U) (b : V) (k : Frequency) :
    (RelativeOperators.d1 (restrictPeriods P hVU) (potentialFamily P p₀ a hm ha)).coefficientValue
        k (b : ℂ) =
      MarkedLinear.relativeSymbol (P.point (Set.inclusion hVU b)) (integerFrequency k) 0 *
        potentialCoefficients P p₀ a k (b : ℂ) := by
  rw [RelativeOperators.coefficientValue_d1, restrictPeriods_point,
    coefficientValue_potentialFamily]

/-- The second actual relative derivative uses the unchanged original period symbol. -/
theorem coefficientValue_d2_potentialFamily (hVU : V ≤ U) (b : V) (k : Frequency) :
    (RelativeOperators.d2 (restrictPeriods P hVU) (potentialFamily P p₀ a hm ha)).coefficientValue
        k (b : ℂ) =
      MarkedLinear.relativeSymbol (P.point (Set.inclusion hVU b)) (integerFrequency k) 1 *
        potentialCoefficients P p₀ a k (b : ℂ) := by
  rw [RelativeOperators.coefficientValue_d2, restrictPeriods_point,
    coefficientValue_potentialFamily]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
