import ErdosProblems.Erdos67.StationarySpectralEnergy

/-!
# The spectral quadratic identity with complex coefficients

This finite identity applies to the modulated averages used in the atom
arguments, including averages on a dilated set of coordinate indices.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67.StationaryModel

variable {ι : Type*} [Fintype ι]

noncomputable def coordinatePolynomial (n : ι → ℕ) (c : ι → ℂ) (ω : Configuration) : ℂ :=
  ∑ i, c i * (coordinate (n i : ℤ) ω : ℂ)

noncomputable def frequencyPolynomial (n : ι → ℕ) (c : ι → ℂ) (θ : FrequencyCircle) : ℂ :=
  ∑ i, c i * fourier (n i : ℤ) θ

theorem continuous_coordinatePolynomial (n : ι → ℕ) (c : ι → ℂ) :
    Continuous (coordinatePolynomial n c) :=
  continuous_finsetSum _ fun i _ ↦ continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_coordinate (n i : ℤ)))

theorem continuous_frequencyPolynomial (n : ι → ℕ) (c : ι → ℂ) :
    Continuous (frequencyPolynomial n c) :=
  continuous_finsetSum _ fun i _ ↦ continuous_const.mul (fourier (n i : ℤ)).continuous

theorem normSq_sum_expansion (v : ι → ℂ) :
    (Complex.normSq (∑ i, v i) : ℂ) = ∑ i, ∑ j, v i * conj (v j) := by
  rw [← Complex.mul_conj, map_sum, sum_mul_sum]

theorem coordinatePolynomial_normSq_expansion (n : ι → ℕ) (c : ι → ℂ) (ω : Configuration) :
    (Complex.normSq (coordinatePolynomial n c ω) : ℂ) =
      ∑ i, ∑ j, (c i * conj (c j)) *
        ((coordinate (n i : ℤ) ω * coordinate (n j : ℤ) ω : ℝ) : ℂ) := by
  rw [coordinatePolynomial, normSq_sum_expansion]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem frequencyPolynomial_normSq_expansion (n : ι → ℕ) (c : ι → ℂ) (θ : FrequencyCircle) :
    (Complex.normSq (frequencyPolynomial n c θ) : ℂ) =
      ∑ i, ∑ j, (c i * conj (c j)) * fourier ((n i : ℤ) - (n j : ℤ)) θ := by
  rw [frequencyPolynomial, normSq_sum_expansion]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp only [map_mul]
  ring

theorem integral_coordinatePolynomial_normSq (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (n : ι → ℕ) (c : ι → ℂ) :
    (∫ ω, (Complex.normSq (coordinatePolynomial n c ω) : ℂ) ∂(Q : Measure Configuration)) =
      ∑ i, ∑ j, (c i * conj (c j)) * (correlation Q ((n i : ℤ) - (n j : ℤ)) : ℂ) := by
  simp_rw [coordinatePolynomial_normSq_expansion]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_complex_ofReal, integral_coordinate_pair_nat Q hQ]
    · intro j _
      exact (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_coordinate _).mul (continuous_coordinate _)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro i _
    exact (continuous_finsetSum _ fun j _ ↦ continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_coordinate _).mul (continuous_coordinate _)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem integral_frequencyPolynomial_normSq (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (n : ι → ℕ) (c : ι → ℂ) :
    (∫ θ, (Complex.normSq (frequencyPolynomial n c θ) : ℂ) ∂(σ : Measure FrequencyCircle)) =
      ∑ i, ∑ j, (c i * conj (c j)) * (correlation Q ((n i : ℤ) - (n j : ℤ)) : ℂ) := by
  simp_rw [frequencyPolynomial_normSq_expansion]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      rw [integral_const_mul, hσ]
    · intro j _
      exact integrable_spectrum_continuous σ _ (continuous_const.mul (fourier _).continuous)
  · intro i _
    exact integrable_spectrum_continuous σ _
      (continuous_finsetSum _ fun j _ ↦ continuous_const.mul (fourier _).continuous)

theorem spectral_quadratic_identity (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (n : ι → ℕ) (c : ι → ℂ) :
    (∫ ω, Complex.normSq (coordinatePolynomial n c ω) ∂(Q : Measure Configuration)) =
      ∫ θ, Complex.normSq (frequencyPolynomial n c θ) ∂(σ : Measure FrequencyCircle) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal,
    integral_coordinatePolynomial_normSq Q hQ, integral_frequencyPolynomial_normSq Q σ hσ]

end Erdos67.StationaryModel
