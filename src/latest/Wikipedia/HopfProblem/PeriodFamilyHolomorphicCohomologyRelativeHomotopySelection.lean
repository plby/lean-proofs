import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProduct
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivativesBasic

/-!
# The original fixed-centre selection in the relative Fourier homotopy

Selecting one of two coefficient families according to the original
centre and frequency preserves the proved rapid estimates: the selector
does not depend on the varying base. Multiplication by the genuine
selected inverse then gives actual rapidly decreasing potential
coefficients on any open where the inverse estimates have been proved.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis RelativeFourier PeriodTorusLineBundleClassification

/-- Select the original coefficient using only the fixed centre and frequency. -/
def selectedCoefficients (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) : Coefficients :=
  fun k z => a (centreCoordinate p₀ (integerFrequency k)) k z

@[simp] theorem selectedCoefficients_apply (p₀ : PeriodDomain)
    (a : Fin 2 → Coefficients) (k : Frequency) (z : ℂ) :
    selectedCoefficients p₀ a k z = a (centreCoordinate p₀ (integerFrequency k)) k z := rfl

/-- The fixed-centre selection preserves every original weighted derivative bound. -/
theorem selectedCoefficients_rapid {U : Opens ℂ} (p₀ : PeriodDomain)
    (a : Fin 2 → Coefficients) (ha : ∀ j, SmoothRapidCoefficients U (a j)) :
    SmoothRapidCoefficients U (selectedCoefficients p₀ a) where
  smooth k := (ha (centreCoordinate p₀ (integerFrequency k))).smooth k
  majorant := by
    intro s K hK r
    choose u hnonneg hsum hbound using fun j => (ha j).majorant s K hK r
    refine ⟨fun k => ∑ j, u j k, ?_, ?_, ?_⟩
    · intro k
      exact Finset.sum_nonneg (fun j _ => hnonneg j k)
    · exact summable_sum (fun j _ => hsum j)
    · intro b hb k
      exact (hbound (centreCoordinate p₀ (integerFrequency k)) b hb k).trans
        (Finset.single_le_sum (fun j _ => hnonneg j k)
          (Finset.mem_univ (centreCoordinate p₀ (integerFrequency k))))

/-- The literal original inverse times the original selected coefficient. -/
def potentialCoefficients {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) : Coefficients :=
  fun k z => ambientInverse P p₀ k z * selectedCoefficients p₀ a k z

/-- The proved inverse bounds and original coefficient estimates imply
rapid decay of the actual potential coefficients. -/
theorem potentialCoefficients_rapid {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (p₀ : PeriodDomain) (a : Fin 2 → Coefficients)
    (hm : SmoothPolynomiallyBoundedCoefficients V (ambientInverse P p₀))
    (ha : ∀ j, SmoothRapidCoefficients V (a j)) :
    SmoothRapidCoefficients V (potentialCoefficients P p₀ a) :=
  hm.mul_rapid (selectedCoefficients_rapid p₀ a ha)

/-- The genuine zero Fourier mode of this potential vanishes. -/
@[simp] theorem potentialCoefficients_zero {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) (b : U) :
    potentialCoefficients P p₀ a 0 (b : ℂ) = 0 := by
  simp only [potentialCoefficients, ambientInverse_apply, integerFrequency_zero,
    denominatorInverse_zero, zero_mul]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
