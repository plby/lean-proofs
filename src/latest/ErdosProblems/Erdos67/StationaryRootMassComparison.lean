import ErdosProblems.Erdos67.StationaryAtomDifference

/-!
# Comparing the mass of an atom with one of its roots

The reverse triangle inequality in `L²`, applied to finite continuous
averages, bounds the squared difference of the square-root atom masses by
the mass of the remaining dilation fiber.
-/

open scoped BigOperators ComplexConjugate Topology ENNReal
open Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem norm_toL2_sq (μ : Measure Configuration) [IsFiniteMeasure μ]
    (F : C(Configuration, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ F‖ ^ 2 = ∫ ω, Complex.normSq (F ω) ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with ω hω
  rw [hω, real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq]

theorem norm_toL2_eq_sqrt (μ : Measure Configuration) [IsFiniteMeasure μ]
    (F : C(Configuration, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ F‖ = Real.sqrt (∫ ω, Complex.normSq (F ω) ∂μ) := by
  rw [← norm_toL2_sq μ F, Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_integral_normSq_sub_sq_le (μ : Measure Configuration) [IsFiniteMeasure μ]
    (F G : C(Configuration, ℂ)) :
    (Real.sqrt (∫ ω, Complex.normSq (F ω) ∂μ) -
      Real.sqrt (∫ ω, Complex.normSq (G ω) ∂μ)) ^ 2 ≤
        ∫ ω, Complex.normSq (F ω - G ω) ∂μ := by
  rw [← norm_toL2_eq_sqrt μ F, ← norm_toL2_eq_sqrt μ G]
  have hn := abs_norm_sub_norm_le (ContinuousMap.toLp 2 μ ℂ F) (ContinuousMap.toLp 2 μ ℂ G)
  have hsq : (‖ContinuousMap.toLp 2 μ ℂ F‖ - ‖ContinuousMap.toLp 2 μ ℂ G‖) ^ 2 ≤
      ‖ContinuousMap.toLp 2 μ ℂ F - ContinuousMap.toLp 2 μ ℂ G‖ ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hn
    simpa only [← pow_two, sq_abs] using hh
  rw [← map_sub, norm_toL2_sq μ (F - G)] at hsq
  exact hsq

noncomputable def residueWeightedMeasure (Q : ProbabilityMeasure Configuration) (d : ℕ+) :
    Measure Configuration :=
  (d.val : ℝ≥0∞) • (Q : Measure Configuration).restrict {ω | ω.2 d = 0}

instance residueWeightedMeasure_finite (Q : ProbabilityMeasure Configuration) (d : ℕ+) :
    IsFiniteMeasure (residueWeightedMeasure Q d) := by
  unfold residueWeightedMeasure
  exact Measure.smul_finite _ (ENNReal.natCast_ne_top _)

theorem integral_residueWeightedMeasure (Q : ProbabilityMeasure Configuration) (d : ℕ+)
    (F : Configuration → ℝ) :
    (∫ ω, F ω ∂residueWeightedMeasure Q d) =
      (d.val : ℝ) * ∫ ω, residueZeroIndicator d ω * F ω ∂(Q : Measure Configuration) := by
  have hs : MeasurableSet {ω : Configuration | ω.2 d = 0} :=
    (isClosed_eq ((continuous_apply d).comp continuous_snd) continuous_const).measurableSet
  have he : Set.indicator {ω : Configuration | ω.2 d = 0} F =
      (fun ω ↦ residueZeroIndicator d ω * F ω) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq, residueZeroIndicator]
    split_ifs <;> simp
  rw [residueWeightedMeasure, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    ← integral_indicator hs, he]

theorem conditional_sqrt_difference_le (Q : ProbabilityMeasure Configuration)
    (d : ℕ+) (F G : C(Configuration, ℂ)) :
    (Real.sqrt ((d.val : ℝ) * ∫ ω, residueZeroIndicator d ω * Complex.normSq (F ω)
        ∂(Q : Measure Configuration)) -
      Real.sqrt ((d.val : ℝ) * ∫ ω, residueZeroIndicator d ω * Complex.normSq (G ω)
        ∂(Q : Measure Configuration))) ^ 2 ≤
        (d.val : ℝ) * ∫ ω, Complex.normSq (F ω - G ω) ∂(Q : Measure Configuration) := by
  have ht := sqrt_integral_normSq_sub_sq_le (residueWeightedMeasure Q d) F G
  rw [integral_residueWeightedMeasure, integral_residueWeightedMeasure,
    integral_residueWeightedMeasure] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply integral_mono
    (integrable_configuration_continuous Q _ ((continuous_residueZeroIndicator d).mul
      (Complex.continuous_normSq.comp (F.continuous.sub G.continuous))))
    (integrable_configuration_continuous Q _
      (Complex.continuous_normSq.comp (F.continuous.sub G.continuous)))
  intro ω
  dsimp only [Pi.mul_apply, Function.comp_apply]
  unfold residueZeroIndicator
  split_ifs
  · simp
  · simpa using Complex.normSq_nonneg (F ω - G ω)

theorem spectral_root_mass_comparison (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (d : ℕ+) (η ξ : FrequencyCircle) (hξ : d.val • ξ = η) :
    (Real.sqrt ((σ : Measure FrequencyCircle).real {η}) -
      Real.sqrt ((σ : Measure FrequencyCircle).real {ξ})) ^ 2 ≤
        (d.val : ℝ) * (σ : Measure FrequencyCircle).real {θ | d.val • θ = η ∧ θ ≠ ξ} := by
  have hleft := tendsto_modulatedAverage_second_moment Q hQ σ hσ 1 η
  have hright := tendsto_conditional_modulated_moment Q hQ σ hσ d ξ
  have hdiff := (tendsto_modulatedAverage_difference Q hQ σ hσ d.val η ξ hξ).const_mul (d.val : ℝ)
  have hlim := ((Real.continuous_sqrt.continuousAt.tendsto.comp hleft).sub
    (Real.continuous_sqrt.continuousAt.tendsto.comp hright)).pow 2
  have hineq : ∀ N,
      (Real.sqrt (∫ ω, Complex.normSq (modulatedAverage N 1 η ω) ∂(Q : Measure Configuration)) -
        Real.sqrt ((d.val : ℝ) * ∫ ω, residueZeroIndicator d ω *
          Complex.normSq (modulatedAverage N 1 ξ ω) ∂(Q : Measure Configuration))) ^ 2 ≤
          (d.val : ℝ) * ∫ ω, Complex.normSq (modulatedAverage N d.val η ω -
            modulatedAverage N 1 ξ ω) ∂(Q : Measure Configuration) := by
    intro N
    have ht := conditional_sqrt_difference_le Q d
      ⟨modulatedAverage N d.val η, continuous_modulatedAverage N d.val η⟩
      ⟨modulatedAverage N 1 ξ, continuous_modulatedAverage N 1 ξ⟩
    rw [modulatedAverage_conditional_dilation Q hCD N η d]
    exact ht
  have he := le_of_tendsto_of_tendsto hlim hdiff (Eventually.of_forall hineq)
  simpa only [one_nsmul, Set.ofPred_eq_eq_singleton, Function.comp_def] using he

end Erdos67.StationaryModel
