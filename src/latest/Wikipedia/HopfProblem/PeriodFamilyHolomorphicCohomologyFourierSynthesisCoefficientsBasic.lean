import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol

/-!
# Smooth rapidly decreasing parameterized Fourier coefficients

The coefficients are actual ambient functions of the original complex
base coordinate, required to be real smooth only on its given open set.
Every literal real directional-derivative word has compact-uniform
summable bounds after every polynomial frequency weight. The genuine
Haar Fourier coefficients of the original smooth family satisfy this
condition by the proved differentiation and elliptic estimates.

This file constructs coefficient data only. It makes no infinite-series
smoothness or relative cohomology assertion.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

/-- The original marked integer Fourier lattice. -/
abbrev Frequency := Fin 4 → ℤ

/-- Actual ambient coefficient functions, used only on the original open base. -/
abbrev Coefficients := Frequency → ℂ → ℂ

/-- Real smooth coefficient functions with compact-uniform summable
majorants for every polynomially weighted actual base derivative word. -/
structure SmoothRapidCoefficients (U : Opens ℂ) (c : Coefficients) : Prop where
  smooth : ∀ k, ContDiffOn ℝ ∞ (c k) U
  majorant : ∀ (s : List ℂ) (K : Set U), IsCompact K → ∀ r : ℕ,
    ∃ u : Frequency → ℝ, (∀ k, 0 ≤ u k) ∧ Summable u ∧
      ∀ b ∈ K, ∀ k,
        (1 + ‖integerFrequency k‖) ^ r *
            ‖FourierParameter.iteratedDirectionalDerivativeList s (c k) (b : ℂ)‖ ≤ u k

/-- Differentiate the original coefficient in one fixed real base direction. -/
def baseDiff (v : ℂ) (c : Coefficients) : Coefficients :=
  fun k z => fderiv ℝ (c k) z v

@[simp] theorem baseDiff_apply (v : ℂ) (c : Coefficients) (k : Frequency) (z : ℂ) :
    baseDiff v c k z = fderiv ℝ (c k) z v := rfl

/-- The exact original Fourier multiplier for one real torus-coordinate derivative. -/
def frequencyDiff (j : Fin 4) (c : Coefficients) : Coefficients :=
  fun k z => (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * c k z

@[simp] theorem frequencyDiff_apply (j : Fin 4) (c : Coefficients)
    (k : Frequency) (z : ℂ) :
    frequencyDiff j c k z = (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * c k z := rfl

/-- The actual coefficient obtained by differentiating a joint base/torus Fourier mode. -/
def jointDerivativeCoefficients (v : ℂ × (Fin 4 → ℝ)) (c : Coefficients) : Coefficients :=
  baseDiff v.1 c + ∑ j : Fin 4, fun k z => (v.2 j : ℂ) * frequencyDiff j c k z

@[simp] theorem jointDerivativeCoefficients_apply (v : ℂ × (Fin 4 → ℝ))
    (c : Coefficients) (k : Frequency) (z : ℂ) :
    jointDerivativeCoefficients v c k z =
      baseDiff v.1 c k z + ∑ j : Fin 4, (v.2 j : ℂ) * frequencyDiff j c k z := by
  simp only [jointDerivativeCoefficients, Pi.add_apply, Finset.sum_apply]

/-- The actual Haar coefficients satisfy the coefficient condition;
neither their regularity nor their weighted decay is assumed. -/
theorem smoothRapidCoefficients_actual {U : Opens ℂ}
    (f : FourierParameter.SmoothFamily U (Fin 4)) :
    SmoothRapidCoefficients U f.coefficientValue where
  smooth := f.coefficientValue_contDiffOn
  majorant := by
    intro s K hK r
    obtain ⟨C, hC, hsum, hbound⟩ :=
      f.iteratedCoefficientDerivative_polynomial_majorant_compact s K hK r
    refine ⟨fun k => C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹, ?_, hsum, ?_⟩
    · intro k
      exact mul_nonneg (mul_nonneg hC.le (pow_nonneg (by norm_num) r))
        (inv_nonneg.mpr (fourierEllipticWeight_pos k).le)
    · exact hbound

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
