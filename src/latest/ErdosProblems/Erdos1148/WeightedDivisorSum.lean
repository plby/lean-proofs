import ErdosProblems.Erdos1148.ConvolutionDivisorBound
import ErdosProblems.Erdos1148.HyperbolaBoundaryEstimates

/-! # A subpower bound for the weighted coefficient sums in a four-factor hyperbola -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma realPowerPartialSum_three_eighths_le {N : ℕ} (hN : 0 < N) :
    realPowerPartialSum (3 / 8) N ≤ 4 * (N : ℝ) ^ (5 / 8 : ℝ) := by
  have h := realPowerPartialSum_sub_regularized_norm_le
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (3 / 8 : ℝ) < 1) hN
  have hz := realZetaRegularized_neg
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (3 / 8 : ℝ) < 1)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ (-(3 / 8) : ℝ) ≤ (N : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  rw [Real.norm_eq_abs] at h
  have hle := (le_abs_self _).trans h
  norm_num only [show (1 : ℝ) - 3 / 8 = 5 / 8 by norm_num] at hle
  have hpos : 0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) := by positivity
  linarith

theorem exists_weighted_divisor_sum_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ArithmeticFunction ℝ),
      (∀ n, ‖f n‖ ≤ (n.divisors.card : ℝ)) → ∀ (N : ℕ), 0 < N →
        (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-(1 / 2) : ℝ) * ‖f n‖) ≤
          D * (N : ℝ) ^ (5 / 8 : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := exists_card_divisors_le_rpow (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨4 * C, by positivity, ?_⟩
  intro f hf N hN
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, C * (n : ℝ) ^ (-(3 / 8) : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := (mem_Ioc.mp hn).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      calc
        _ ≤ (n : ℝ) ^ (-(1 / 2) : ℝ) * (C * (n : ℝ) ^ (1 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((hf n).trans (hdiv n (Nat.ne_zero_of_lt hn0))) (by positivity)
        _ = _ := by
          rw [mul_left_comm, ← Real.rpow_add hnR]
          norm_num
    _ = C * realPowerPartialSum (3 / 8) N := by
      rw [realPowerPartialSum_eq_sum_Ioc, mul_sum]
    _ ≤ C * (4 * (N : ℝ) ^ (5 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (realPowerPartialSum_three_eighths_le hN) hC.le
    _ = _ := by ring

end Erdos1148.DukeArithmetic
