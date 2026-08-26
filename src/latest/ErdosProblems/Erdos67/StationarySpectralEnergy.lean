import ErdosProblems.Erdos67.StationaryGeometricEnergy

/-!
# The finite spectral energy bound

Fatou's lemma transfers the uniform block moment bound to the inverse-square
distance from zero frequency. The excluded zero atom is used explicitly.
-/

open scoped BigOperators Topology ENNReal
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem integral_averagedGeometricEnergy_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B)
    (N : ℕ) :
    (∫ θ, averagedGeometricEnergy N θ ∂(σ : Measure FrequencyCircle)) ≤ B := by
  unfold averagedGeometricEnergy
  rw [integral_div, integral_finsetSum]
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos N))).2
    calc
      _ ≤ ∑ m ∈ range (N + 1), B := by
        apply sum_le_sum
        intro m _
        rw [integral_geometricPolynomial_normSq Q hQ σ hσ]
        exact hB m
      _ = B * ((N + 1 : ℕ) : ℝ) := by simp [mul_comm]
  · intro m _
    exact integrable_spectrum_continuous σ _
      (Complex.continuous_normSq.comp (continuous_geometricPolynomial m))

theorem spectralEnergy_nonneg (θ : FrequencyCircle) : 0 ≤ spectralEnergy θ :=
  div_nonneg (by norm_num) (Complex.normSq_nonneg _)

theorem measurable_spectralEnergy : Measurable spectralEnergy :=
  measurable_const.div
    (Complex.continuous_normSq.comp ((fourier 1).continuous.sub continuous_const)).measurable

/-- The spectral energy is finite, with the original uniform second-moment bound. -/
theorem lintegral_spectralEnergy_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B) :
    (∫⁻ θ, ENNReal.ofReal (spectralEnergy θ) ∂(σ : Measure FrequencyCircle)) ≤
      ENNReal.ofReal B := by
  have hzero : ∀ᵐ θ ∂(σ : Measure FrequencyCircle), θ ≠ 0 := by
    rw [ae_iff]
    simpa using correlation_spectrum_zero_atom Q hQ σ hσ B hB
  have hlim : ∀ᵐ θ ∂(σ : Measure FrequencyCircle),
      ENNReal.ofReal (spectralEnergy θ) =
        liminf (fun N ↦ ENNReal.ofReal (averagedGeometricEnergy N θ)) atTop := by
    filter_upwards [hzero] with θ hθ
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_averagedGeometricEnergy hθ)).liminf_eq.symm
  have hupper (N : ℕ) :
      (∫⁻ θ, ENNReal.ofReal (averagedGeometricEnergy N θ) ∂(σ : Measure FrequencyCircle)) ≤
        ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_spectrum_continuous σ _ (continuous_averagedGeometricEnergy N))
      (Eventually.of_forall (averagedGeometricEnergy_nonneg N))]
    exact ENNReal.ofReal_le_ofReal (integral_averagedGeometricEnergy_le Q hQ σ hσ B hB N)
  calc
    _ = ∫⁻ θ, liminf (fun N ↦ ENNReal.ofReal (averagedGeometricEnergy N θ)) atTop
        ∂(σ : Measure FrequencyCircle) := lintegral_congr_ae hlim
    _ ≤ liminf (fun N ↦ ∫⁻ θ, ENNReal.ofReal (averagedGeometricEnergy N θ)
        ∂(σ : Measure FrequencyCircle)) atTop :=
      lintegral_liminf_le (fun N ↦ (continuous_averagedGeometricEnergy N).measurable.ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hupper))

theorem integrable_spectralEnergy (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B) :
    Integrable spectralEnergy (σ : Measure FrequencyCircle) := by
  refine ⟨measurable_spectralEnergy.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall spectralEnergy_nonneg)]
  exact (lintegral_spectralEnergy_le Q hQ σ hσ B hB).trans_lt ENNReal.ofReal_lt_top

end Erdos67.StationaryModel
