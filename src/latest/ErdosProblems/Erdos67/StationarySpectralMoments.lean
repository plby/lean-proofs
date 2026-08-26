import ErdosProblems.Erdos67.StationarySpectrum

/-!
# Spectral identities for finite coordinate sums

The moment identities follow from the Fourier representation, with the
stationarity hypotheses discharged at each pair of coordinates.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem integrable_spectrum_continuous (σ : ProbabilityMeasure FrequencyCircle)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : FrequencyCircle → E) (hF : Continuous F) : Integrable F (σ : Measure FrequencyCircle) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem integral_signPolynomial_spectrum (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (N : ℕ) (a : Fin N → ℝ) :
    (∫ θ, Complex.normSq (signPolynomial N a θ) ∂(σ : Measure FrequencyCircle)) =
      ∑ i : Fin N, ∑ j : Fin N, a i * a j * correlation Q ((i.val : ℤ) - (j.val : ℤ)) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [signPolynomial_normSq_expansion]
  rw [integral_finsetSum]
  · simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply sum_congr rfl
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

theorem integral_coordinate_pair_nat (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (i j : ℕ) :
    (∫ ω, coordinate (i : ℤ) ω * coordinate (j : ℤ) ω ∂(Q : Measure Configuration)) =
      correlation Q ((i : ℤ) - (j : ℤ)) := by
  have hp := integral_coordinate_pair_shift Q hQ j ((i : ℤ) - (j : ℤ))
  rw [add_sub_cancel] at hp
  rw [← hp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

theorem integral_blockSum_sq_eq_pairs (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N : ℕ) :
    (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) =
      ∑ i : Fin N, ∑ j : Fin N, correlation Q ((i.val : ℤ) - (j.val : ℤ)) := by
  have he (ω : Configuration) : blockSum N ω = ∑ i : Fin N, coordinate (i.val : ℤ) ω := by
    exact (Fin.sum_univ_eq_sum_range (fun i ↦ coordinate (i : ℤ) ω) N).symm
  simp_rw [he, pow_two, sum_mul, mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      exact integral_coordinate_pair_nat Q hQ i.val j.val
    · intro j _
      exact integrable_configuration_continuous Q _
        ((continuous_coordinate _).mul (continuous_coordinate _))
  · intro i _
    exact integrable_configuration_continuous Q _ (continuous_finsetSum _ fun j _ ↦
      (continuous_coordinate _).mul (continuous_coordinate _))

noncomputable def geometricPolynomial (N : ℕ) (θ : FrequencyCircle) : ℂ :=
  signPolynomial N (fun _ ↦ 1) θ

theorem continuous_geometricPolynomial (N : ℕ) : Continuous (geometricPolynomial N) :=
  continuous_signPolynomial N _

theorem geometricPolynomial_zero (N : ℕ) : geometricPolynomial N 0 = (N : ℂ) := by
  simp [geometricPolynomial, signPolynomial]

theorem integral_geometricPolynomial_normSq (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (N : ℕ) :
    (∫ θ, Complex.normSq (geometricPolynomial N θ) ∂(σ : Measure FrequencyCircle)) =
      ∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration) := by
  rw [integral_blockSum_sq_eq_pairs Q hQ]
  simpa only [geometricPolynomial, one_mul] using
    integral_signPolynomial_spectrum Q σ hσ N (fun _ ↦ 1)

end Erdos67.StationaryModel
