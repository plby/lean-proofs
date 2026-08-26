import ErdosProblems.Erdos67.StationaryResidueBalance

/-!
# Recovering spectral atom mass after conditioning on residues

The squared modulated averages become translation invariant uniformly. The
residue-balancing estimate therefore makes every fixed residue class carry
the same limiting squared norm.
-/

open scoped Topology
open Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem abs_conditional_modulated_moment_sub_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (d : ℕ+) (η : FrequencyCircle) (N : ℕ) :
    |(d.val : ℝ) * (∫ ω, residueZeroIndicator d ω * Complex.normSq (modulatedAverage N 1 η ω)
        ∂(Q : Measure Configuration)) -
      ∫ ω, Complex.normSq (modulatedAverage N 1 η ω) ∂(Q : Measure Configuration)| ≤
        (d.val : ℝ) ^ 2 * (4 / ((N + 1 : ℕ) : ℝ)) := by
  exact abs_residue_normalized_weight_sub_le Q hQ d
    (fun ω ↦ Complex.normSq (modulatedAverage N 1 η ω))
    (Complex.continuous_normSq.comp (continuous_modulatedAverage N 1 η))
    (4 / ((N + 1 : ℕ) : ℝ)) (by positivity)
    (abs_modulatedAverage_normSq_shift_sub_le N η)

theorem tendsto_conditional_modulated_moment (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (d : ℕ+) (η : FrequencyCircle) :
    Tendsto (fun N ↦ (d.val : ℝ) *
      (∫ ω, residueZeroIndicator d ω * Complex.normSq (modulatedAverage N 1 η ω)
        ∂(Q : Measure Configuration))) atTop (nhds ((σ : Measure FrequencyCircle).real {η})) := by
  have he : Tendsto (fun N ↦
      (d.val : ℝ) * (∫ ω, residueZeroIndicator d ω * Complex.normSq (modulatedAverage N 1 η ω)
          ∂(Q : Measure Configuration)) -
        ∫ ω, Complex.normSq (modulatedAverage N 1 η ω) ∂(Q : Measure Configuration))
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ ↦ (d.val : ℝ) ^ 2 * (4 / ((N + 1 : ℕ) : ℝ)))
    · intro N
      simpa only [Real.norm_eq_abs] using abs_conditional_modulated_moment_sub_le Q hQ d η N
    · have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((d.val : ℝ) ^ 2 * 4)
      convert ht using 1 <;> simp [Nat.cast_add, div_eq_mul_inv, mul_assoc]
  have hu := tendsto_modulatedAverage_second_moment Q hQ σ hσ 1 η
  have ht := he.add hu
  simpa only [sub_add_cancel, zero_add, one_nsmul, Set.ofPred_eq_eq_singleton] using ht

end Erdos67.StationaryModel
