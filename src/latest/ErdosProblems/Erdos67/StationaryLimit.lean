import ErdosProblems.Erdos67.StationarySamplingLaw

/-!
# Stationarity of limits of the finite sampling laws

The translation estimate yields stationarity of every weak subsequential limit.
Bounds on the second moments of all sign-block sums also pass to the limit.
Conditional dilation is established separately.
-/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem samplingLaw_shift_error_tendsto_zero (f : ℕ → Bool) (F : C(Configuration, ℝ)) :
    Tendsto (fun t ↦ |(∫ ω, F (shift 1 ω) ∂(samplingLaw f t : Measure Configuration)) -
      ∫ ω, F ω ∂(samplingLaw f t : Measure Configuration)|) atTop (nhds 0) := by
  have hsucc : Tendsto (fun t : ℕ ↦ t + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  exact squeeze_zero (fun _ ↦ abs_nonneg _) (abs_integral_samplingLaw_shift_sub_le f · F)
    ((StationaryHarmonicAverage.tendsto_translation_error_bound ‖F‖).comp hsucc)

theorem samplingLaw_limit_integral_shift
    (f : ℕ → Bool) (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ)
    (hr : StrictMono r) (hQ : Tendsto (samplingLaw f ∘ r) atTop (nhds Q))
    (F : C(Configuration, ℝ)) :
    (∫ ω, F (shift 1 ω) ∂(Q : Measure Configuration)) =
      ∫ ω, F ω ∂(Q : Measure Configuration) := by
  have hshift := tendsto_integral_continuous_observable hQ
    (fun ω ↦ F (shift 1 ω)) (F.continuous.comp (continuous_shift 1))
  have hplain := tendsto_integral_continuous_observable hQ F F.continuous
  have hlim := (hshift.sub hplain).abs
  have hzero := (samplingLaw_shift_error_tendsto_zero f F).comp hr.tendsto_atTop
  have heq := tendsto_nhds_unique hlim hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp heq)

theorem samplingLaw_limit_shift_invariant
    (f : ℕ → Bool) (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ)
    (hr : StrictMono r) (hQ : Tendsto (samplingLaw f ∘ r) atTop (nhds Q)) :
    Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (continuous_shift 1).measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact samplingLaw_limit_integral_shift f Q r hr hQ F.toContinuousMap

/-- Every sign sequence admits a stationary subsequential sampling law. -/
theorem exists_stationary_sampling_limit (f : ℕ → Bool) :
    ∃ (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ),
      StrictMono r ∧ Tendsto (samplingLaw f ∘ r) atTop (nhds Q) ∧
        Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration) := by
  obtain ⟨Q, r, hr, hQ⟩ := configuration_probability_tendsto_subseq (samplingLaw f)
  exact ⟨Q, r, hr, hQ, samplingLaw_limit_shift_invariant f Q r hr hQ⟩

theorem integral_samplingLaw_blockSum_sq_le (f : ℕ → Bool) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C) (t M : ℕ) :
    (∫ ω, blockSum M ω ^ 2 ∂(samplingLaw f t : Measure Configuration)) ≤ 4 * C ^ 2 := by
  let F : C(Configuration, ℝ) := ⟨fun ω ↦ blockSum M ω ^ 2, (continuous_blockSum M).pow 2⟩
  change (∫ ω, F ω ∂(samplingLaw f t : Measure Configuration)) ≤ _
  rw [samplingLaw, integral_finitePushforward]
  calc
    (∑ z, samplingVector t z * F (sample f (StationaryDilationAverage.boxValue z.1)
        (z.2.val + 1))) ≤ ∑ z, samplingVector t z * (4 * C ^ 2) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (FiniteEntropy.prob_nonneg _ z)
      have hb := abs_blockSum_sample_le f C hbound (StationaryDilationAverage.boxValue z.1)
        (z.2.val + 1) M (StationaryDilationAverage.boxValue_pos z.1) (Nat.succ_pos _)
      change blockSum M (sample f (StationaryDilationAverage.boxValue z.1) (z.2.val + 1)) ^ 2 ≤ _
      have hsq := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * C) |>.mpr hb
      rw [sq_abs] at hsq
      nlinarith
    _ = 4 * C ^ 2 := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

theorem samplingLaw_limit_blockSum_sq_le
    (f : ℕ → Bool) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C)
    (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ)
    (hQ : Tendsto (samplingLaw f ∘ r) atTop (nhds Q)) (M : ℕ) :
    (∫ ω, blockSum M ω ^ 2 ∂(Q : Measure Configuration)) ≤ 4 * C ^ 2 := by
  have hlim := tendsto_integral_continuous_observable hQ
    (fun ω ↦ blockSum M ω ^ 2) ((continuous_blockSum M).pow 2)
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n ↦
    integral_samplingLaw_blockSum_sq_le f C hC hbound (r n) M

/-- The stationary model and all its block second-moment bounds come from the
original bounded-discrepancy hypothesis, without assuming multiplicativity. -/
theorem exists_stationary_sampling_limit_with_moments
    (f : ℕ → Bool) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C) :
    ∃ (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ),
      StrictMono r ∧ Tendsto (samplingLaw f ∘ r) atTop (nhds Q) ∧
        Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration) ∧
          ∀ M, (∫ ω, blockSum M ω ^ 2 ∂(Q : Measure Configuration)) ≤ 4 * C ^ 2 := by
  obtain ⟨Q, r, hr, hQ, hstationary⟩ := exists_stationary_sampling_limit f
  exact ⟨Q, r, hr, hQ, hstationary,
    samplingLaw_limit_blockSum_sq_le f C hC hbound Q r hQ⟩

end Erdos67.StationaryModel
