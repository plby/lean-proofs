import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyBaseDerivative
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopySymbol

/-!
# The actual base equation for the selected relative homotopy

Because the original selector depends only on the centre and frequency,
base differentiation commutes with selection. The genuine holomorphic
inverse then commutes with the base antiholomorphic derivative. For the
coefficient equations of a closed relative form, this recovers the base
coefficient at each nonzero mode and leaves exactly its zero mode.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis RelativeFourier MarkedLinear PeriodTorusLineBundleClassification

/-- The fixed-centre selector commutes literally with the actual base derivative. -/
theorem selectedCoefficients_baseDbar (p₀ : PeriodDomain) (a : Fin 2 → Coefficients)
    (k : Frequency) (z : ℂ) :
    baseDbarCoefficients (selectedCoefficients p₀ a) k z =
      selectedCoefficients p₀ (fun j => baseDbarCoefficients (a j)) k z := rfl

/-- The actual potential derivative is the original holomorphic inverse
times the selected actual derivative, not a derivative defined by a rule. -/
theorem potentialCoefficients_baseDbar {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (p₀ : PeriodDomain) (a : Fin 2 → Coefficients) (b : U) (k : Frequency)
    (hm : DifferentiableAt ℂ (ambientInverse P p₀ k) (b : ℂ))
    (ha : ∀ j, DifferentiableAt ℝ (a j k) (b : ℂ)) :
    baseDbarCoefficients (potentialCoefficients P p₀ a) k (b : ℂ) =
      ambientInverse P p₀ k (b : ℂ) *
        selectedCoefficients p₀ (fun j => baseDbarCoefficients (a j)) k (b : ℂ) :=
  baseDbar_mul_of_holomorphicAt hm (ha (centreCoordinate p₀ (integerFrequency k)))

/-- The actual base equation for every frequency removes only the original zero mode. -/
theorem potentialCoefficients_baseDbar_removeZero {U : Opens ℂ}
    (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain)
    (a : Fin 2 → Coefficients) (a₀ : Coefficients) (b : U)
    (hinverse : ∀ k : Frequency, k ≠ 0 →
      centreCoefficient p₀ (P.point b) (integerFrequency k) *
        ambientInverse P p₀ k (b : ℂ) = 1)
    (hhol : ∀ k : Frequency, DifferentiableAt ℂ (ambientInverse P p₀ k) (b : ℂ))
    (hdiff : ∀ j k, DifferentiableAt ℝ (a j k) (b : ℂ))
    (hclosed : ∀ j k, baseDbarCoefficients (a j) k (b : ℂ) =
      relativeSymbol (P.point b) (integerFrequency k) j * a₀ k (b : ℂ))
    (k : Frequency) :
    baseDbarCoefficients (potentialCoefficients P p₀ a) k (b : ℂ) =
      removeZeroCoefficients a₀ k (b : ℂ) := by
  rw [potentialCoefficients_baseDbar P p₀ a b k (hhol k) (fun j => hdiff j k)]
  by_cases hk : k = 0
  · subst k
    rw [ambientInverse_apply, integerFrequency_zero, denominatorInverse_zero, zero_mul,
      removeZeroCoefficients_zero]
  · rw [removeZeroCoefficients_of_ne_zero _ hk, selectedCoefficients_apply, hclosed]
    calc
      ambientInverse P p₀ k (b : ℂ) *
          (relativeSymbol (P.point b) (integerFrequency k)
            (centreCoordinate p₀ (integerFrequency k)) * a₀ k (b : ℂ)) =
        (centreCoefficient p₀ (P.point b) (integerFrequency k) *
          ambientInverse P p₀ k (b : ℂ)) * a₀ k (b : ℂ) := by
            unfold centreCoefficient
            ring
      _ = a₀ k (b : ℂ) := by rw [hinverse k hk, one_mul]

/-- The same genuine closedness equations force the original vertical
zero coefficients to be antiholomorphically constant in the base. -/
theorem vertical_zeroMode_baseDbar_eq_zero {U : Opens ℂ}
    (P : HolomorphicPeriodMap ℂ U) (a : Fin 2 → Coefficients) (a₀ : Coefficients) (b : U)
    (hclosed : ∀ j k, baseDbarCoefficients (a j) k (b : ℂ) =
      relativeSymbol (P.point b) (integerFrequency k) j * a₀ k (b : ℂ)) (i : Fin 2) :
    baseDbarCoefficients (a i) 0 (b : ℂ) = 0 := by
  simpa only [integerFrequency_zero, map_zero, Pi.zero_apply, zero_mul] using hclosed i 0

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
