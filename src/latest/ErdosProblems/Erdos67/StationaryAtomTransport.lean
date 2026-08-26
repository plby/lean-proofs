import ErdosProblems.Erdos67.StationaryModulatedAverage

/-!
# Spectral atom transport under conditional dilation

Conditional dilation is applied to the squared norm of each finite modulated
average. Dropping its residue indicator and passing to the proved limits gives
the atom-transport inequality with the necessary factor `d`, not `d²`.
-/

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem modulatedAverage_second_moment_le_dilation (Q : ProbabilityMeasure Configuration)
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (N : ℕ) (η : FrequencyCircle) (d : ℕ+) :
    (∫ ω, Complex.normSq (modulatedAverage N 1 η ω) ∂(Q : Measure Configuration)) ≤
      (d.val : ℝ) * ∫ ω, Complex.normSq (modulatedAverage N d.val η ω)
        ∂(Q : Measure Configuration) := by
  rw [modulatedAverage_conditional_dilation Q hCD]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply integral_mono
    (integrable_configuration_continuous Q _ ((continuous_residueZeroIndicator d).mul
      (Complex.continuous_normSq.comp (continuous_modulatedAverage N d.val η))))
    (integrable_configuration_continuous Q _
      (Complex.continuous_normSq.comp (continuous_modulatedAverage N d.val η)))
  intro ω
  dsimp only [Pi.mul_apply, Function.comp_apply]
  unfold residueZeroIndicator
  split_ifs
  · simp
  · simpa using Complex.normSq_nonneg (modulatedAverage N d.val η ω)

theorem spectral_atom_transport (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (η : FrequencyCircle) (d : ℕ+) :
    (σ : Measure FrequencyCircle).real {η} ≤
      (d.val : ℝ) * (σ : Measure FrequencyCircle).real {θ | d.val • θ = η} := by
  have hl := tendsto_modulatedAverage_second_moment Q hQ σ hσ 1 η
  have hr := (tendsto_modulatedAverage_second_moment Q hQ σ hσ d.val η).const_mul (d.val : ℝ)
  have he := le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall fun N ↦ modulatedAverage_second_moment_le_dilation Q hCD N η d)
  simpa only [one_nsmul, Set.ofPred_eq_eq_singleton] using he

end Erdos67.StationaryModel
