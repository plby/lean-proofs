import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyFamilies

/-!
# The genuine selected potential solves the relative equations modulo means

The actual Fourier coefficients of the genuine differentiated potential
equal those of the original input with its zero mode removed. Original
Fourier reconstruction therefore gives equality of the actual smooth
functions, in all three relative directions.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis FourierParameter RelativeFourier RelativeOperators
  PeriodTorusLineBundleClassification

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain)
  (hVU : V ≤ U) (a₀ : SmoothFamily U (Fin 4)) (a : Fin 2 → SmoothFamily U (Fin 4))
  (hm : SmoothPolynomiallyBoundedCoefficients V (ambientInverse P p₀))
  (hinverse : ∀ (b : V) (k : Frequency), k ≠ 0 →
    centreCoefficient p₀ (P.point (Set.inclusion hVU b)) (integerFrequency k) *
      ambientInverse P p₀ k (b : ℂ) = 1)
  (hhol : ∀ k : Frequency, DifferentiableOn ℂ (ambientInverse P p₀ k) V)
  (hclosed : IsClosedTriple P a₀ a)

include hinverse hclosed

/-- Both genuine vertical derivatives of the original selected potential
are the corresponding input family with its actual Haar mean removed. -/
theorem potentialOfFamilies_vertical_eq_meanRemoved (j : Fin 2) :
    (verticalOperator (restrictPeriods P hVU) j (potentialOfFamilies P p₀ hVU a hm) :
      V × UnitAddTorus (Fin 4) → ℂ) = meanRemovedFamily (restrictFamily hVU (a j)) := by
  apply smoothFamily_ext_coefficients
  intro b k
  rw [coefficientValue_verticalOperator, restrictPeriods_point,
    coefficientValue_potentialOfFamilies, coefficientValue_meanRemovedFamily,
    removeZero_coefficientValue_restrictFamily]
  exact potentialCoefficients_symbol_removeZero P p₀ (fun i => (a i).coefficientValue)
    (Set.inclusion hVU b) (hinverse b) (hclosed.vertical_coefficients (Set.inclusion hVU b)) j k

include hhol

/-- The genuine base antiholomorphic derivative of the same potential
removes exactly the actual base zero coefficient. -/
theorem potentialOfFamilies_d0_eq_meanRemoved :
    (d0 (potentialOfFamilies P p₀ hVU a hm) : V × UnitAddTorus (Fin 4) → ℂ) =
      meanRemovedFamily (restrictFamily hVU a₀) := by
  apply smoothFamily_ext_coefficients
  intro b k
  rw [coefficientValue_d0_potentialOfFamilies, coefficientValue_meanRemovedFamily,
    removeZero_coefficientValue_restrictFamily]
  exact potentialCoefficients_baseDbar_removeZero P p₀ (fun i => (a i).coefficientValue)
    a₀.coefficientValue (Set.inclusion hVU b) (hinverse b)
    (fun k => (hhol k).differentiableAt (V.isOpen.mem_nhds b.property))
    (fun j k => ((a j).coefficientValue_hasFDerivAt k (Set.inclusion hVU b)).differentiableAt)
    (hclosed.base_coefficients (Set.inclusion hVU b)) k

omit hhol

/-- Pointwise vertical equations retain the original input functions and their original means. -/
theorem potentialOfFamilies_vertical_apply (j : Fin 2) (b : V)
    (t : UnitAddTorus (Fin 4)) :
    verticalOperator (restrictPeriods P hVU) j (potentialOfFamilies P p₀ hVU a hm) (b, t) =
      a j (Set.inclusion hVU b, t) - (a j).coefficientValue 0 (b : ℂ) := by
  have heq := congrFun
    (potentialOfFamilies_vertical_eq_meanRemoved P p₀ hVU a₀ a hm hinverse hclosed j) (b, t)
  simpa only [meanRemovedFamily_apply, restrictFamily_apply, coefficientValue_restrictFamily]
    using heq

include hhol

/-- Pointwise base equations use the same actual potential and original base mean. -/
theorem potentialOfFamilies_d0_apply (b : V) (t : UnitAddTorus (Fin 4)) :
    d0 (potentialOfFamilies P p₀ hVU a hm) (b, t) =
      a₀ (Set.inclusion hVU b, t) - a₀.coefficientValue 0 (b : ℂ) := by
  have heq := congrFun
    (potentialOfFamilies_d0_eq_meanRemoved P p₀ hVU a₀ a hm hinverse hhol hclosed) (b, t)
  simpa only [meanRemovedFamily_apply, restrictFamily_apply, coefficientValue_restrictFamily]
    using heq

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
