import ErdosProblems.Erdos67.StationarySpectralApproximation

/-!
# Existence of the correlation spectral measure

Compactness of probability measures on the circle and the checked finite
periodogram formula produce a measure with all the required Fourier moments.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem correlation_neg_nat (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (n : ℕ) : correlation Q (-(n : ℤ)) = correlation Q (n : ℤ) := by
  have hs := integral_coordinate_pair_shift Q hQ n (-(n : ℤ))
  rw [add_neg_cancel] at hs
  rw [← hs, correlation]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω ↦ mul_comm _ _

theorem tendsto_triangular_factor (h : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + 1 - h : ℕ) : ℂ) / (n + 1 : ℕ)) atTop (nhds 1) := by
  have ht : Tendsto (fun n : ℕ ↦ 1 - (h : ℂ) * (1 / ((n : ℂ) + 1))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop h] with n hn
  have hhn : h ≤ n + 1 := by omega
  rw [Nat.cast_sub hhn]
  push_cast
  have hz : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

theorem tendsto_fourier_spectralApproximation (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (h : ℕ) :
    Tendsto (fun n ↦ ∫ θ : FrequencyCircle, fourier (h : ℤ) θ
      ∂(spectralApproximation Q n : Measure FrequencyCircle)) atTop
        (nhds (correlation Q (h : ℤ) : ℂ)) := by
  have ht := (tendsto_triangular_factor h).mul_const (correlation Q (h : ℤ) : ℂ)
  simpa only [one_mul, spectralApproximation, integral_fourier_blockSignLaw_nat Q hQ] using ht

/-- A probability measure whose Fourier moments are the stationary correlations. -/
def IsCorrelationSpectrum (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) : Prop :=
  ∀ h : ℤ, (∫ θ : FrequencyCircle, fourier h θ ∂(σ : Measure FrequencyCircle)) =
    (correlation Q h : ℂ)

theorem exists_correlation_spectrum (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration)) :
    ∃ σ : ProbabilityMeasure FrequencyCircle, IsCorrelationSpectrum Q σ := by
  obtain ⟨σ, r, hr, hlim⟩ := CompactSpace.tendsto_subseq (spectralApproximation Q)
  have hnat (h : ℕ) :
      (∫ θ : FrequencyCircle, fourier (h : ℤ) θ ∂(σ : Measure FrequencyCircle)) =
        (correlation Q (h : ℤ) : ℂ) := by
    let F : BoundedContinuousFunction FrequencyCircle ℂ :=
      (ContinuousMap.equivBoundedOfCompact FrequencyCircle ℂ) (fourier (h : ℤ))
    have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hlim F
    exact tendsto_nhds_unique hw
      ((tendsto_fourier_spectralApproximation Q hQ h).comp hr.tendsto_atTop)
  refine ⟨σ, ?_⟩
  intro h
  cases h with
  | ofNat n => exact hnat n
  | negSucc n =>
    change (∫ θ : FrequencyCircle, fourier (-((n + 1 : ℕ) : ℤ)) θ
      ∂(σ : Measure FrequencyCircle)) = (correlation Q (-((n + 1 : ℕ) : ℤ)) : ℂ)
    simp_rw [fourier_neg]
    rw [integral_conj, hnat, Complex.conj_ofReal, correlation_neg_nat Q hQ]

end Erdos67.StationaryModel
