import ErdosProblems.Erdos67.StationaryPrimePairGrouping

/-!
# Cancellation of the prime correlation average

The existing unconditional prime-pair square-sum sieve bound combines with
the proved Wiener limit. A fourth-moment estimate yields cancellation on the
natural prime-counting scale, without a pointwise Fourier decay assumption.
-/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem tendsto_prime_correlation_normalized_fourth (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    Tendsto (fun P : ℕ ↦ ((∑ p ∈ Nat.primesLE (2 * P),
      correlation Q ((d.val * p : ℕ) : ℤ)) * Real.log (P : ℝ) / P) ^ 4)
      atTop (nhds 0) := by
  obtain ⟨K, hK, hpair⟩ := exists_forwardPrimeDifference_square_sum_bound
  have hw : Tendsto (fun P : ℕ ↦
      (∑ h ∈ range (2 * P + 1), correlation Q ((d.val * h : ℕ) : ℤ) ^ 2) /
        ((2 * P + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    (tendsto_correlation_square_average Q σ hσ d).comp
      (tendsto_atTop_mono (fun P : ℕ ↦ by omega : ∀ P : ℕ, P ≤ 2 * P) tendsto_id)
  apply squeeze_zero' (Eventually.of_forall fun P ↦ by positivity)
    (g := fun P ↦ (12 * K) *
      ((∑ h ∈ range (2 * P + 1), correlation Q ((d.val * h : ℕ) : ℤ) ^ 2) /
        ((2 * P + 1 : ℕ) : ℝ)))
  · filter_upwards [hpair, eventually_ge_atTop 2] with P hpair hP
    have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr (by omega)
    have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
    let S := ∑ h ∈ range (2 * P + 1), correlation Q ((d.val * h : ℕ) : ℤ) ^ 2
    have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ sq_nonneg _
    have he := prime_correlation_fourth_power_le Q hQ P d.val
    have he' : (∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d.val * p : ℕ) : ℤ)) ^ 4 ≤
        4 * (K * (P : ℝ) ^ 3 / Real.log (P : ℝ) ^ 4) * S := by
      exact he.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpair (by norm_num)) hS)
    have hh := mul_le_mul_of_nonneg_right he' (show 0 ≤ (Real.log (P : ℝ) / P) ^ 4 by positivity)
    have hscaled : ((∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d.val * p : ℕ) : ℤ)) *
        Real.log (P : ℝ) / P) ^ 4 ≤ 4 * K * S / P := by
      calc
        _ = (∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d.val * p : ℕ) : ℤ)) ^ 4 *
            (Real.log (P : ℝ) / P) ^ 4 := by ring
        _ ≤ _ := hh
        _ = _ := by field_simp [hPR.ne', hlog.ne']
    apply hscaled.trans
    change 4 * K * S / P ≤ (12 * K) * (S / ((2 * P + 1 : ℕ) : ℝ))
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hPR (Nat.cast_pos.mpr (Nat.succ_pos _))).mpr
    push_cast
    have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
    nlinarith [mul_nonneg (mul_nonneg hK.le hS) (sub_nonneg.mpr hp1)]
  · simpa only [mul_zero] using hw.const_mul (12 * K)

theorem tendsto_zero_of_fourth_power {ι : Type*} {l : Filter ι} {F : ι → ℝ}
    (hF : Tendsto (fun i ↦ F i ^ 4) l (nhds 0)) : Tendsto F l (nhds 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hF)
  have he (x : ℝ) : Real.sqrt (Real.sqrt (x ^ 4)) = ‖x‖ := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg x),
      Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  have ht : Tendsto (fun i ↦ ‖F i‖) l (nhds 0) := by
    simpa only [Function.comp_def, he, Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ht

theorem tendsto_prime_correlation_normalized (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    Tendsto (fun P : ℕ ↦ (∑ p ∈ Nat.primesLE (2 * P),
      correlation Q ((d.val * p : ℕ) : ℤ)) * Real.log (P : ℝ) / P)
      atTop (nhds 0) :=
  tendsto_zero_of_fourth_power (tendsto_prime_correlation_normalized_fourth Q hQ σ hσ d)

end Erdos67.StationaryModel
