import ErdosProblems.Erdos67.StationarySpectralMoments

/-!
# Exclusion of the zero-frequency atom

A zero-frequency atom would contribute its mass times `N²` to every block
second moment, contrary to their uniform bound.
-/

open scoped BigOperators
open MeasureTheory

namespace Erdos67.StationaryModel

theorem spectral_zero_atom_bound (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (N : ℕ) :
    (σ : Measure FrequencyCircle).real {0} * (N : ℝ) ^ 2 ≤
      ∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration) := by
  have hi := integral_mono_measure
    (Measure.restrict_le_self (μ := (σ : Measure FrequencyCircle)) (s := {0}))
    (Filter.Eventually.of_forall fun θ ↦ Complex.normSq_nonneg (geometricPolynomial N θ))
    (integrable_spectrum_continuous σ _
      (Complex.continuous_normSq.comp (continuous_geometricPolynomial N)))
  rw [integral_singleton, geometricPolynomial_zero,
    integral_geometricPolynomial_normSq Q hQ σ hσ] at hi
  simpa [Complex.normSq_eq_norm_sq] using hi

theorem correlation_spectrum_zero_atom (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B) :
    (σ : Measure FrequencyCircle) {0} = 0 := by
  have hz : (σ : Measure FrequencyCircle).real {0} = 0 := by
    by_contra hne
    have ha : 0 < (σ : Measure FrequencyCircle).real {0} :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (B / (σ : Measure FrequencyCircle).real {0}))
    have hN1 : 1 < (N : ℝ) := (le_max_left _ _).trans_lt hN
    have hNB : B / (σ : Measure FrequencyCircle).real {0} < (N : ℝ) :=
      (le_max_right _ _).trans_lt hN
    have hprod : B < (N : ℝ) * (σ : Measure FrequencyCircle).real {0} :=
      (div_lt_iff₀ ha).mp hNB
    have hbound := (spectral_zero_atom_bound Q hQ σ hσ N).trans (hB N)
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

end Erdos67.StationaryModel
