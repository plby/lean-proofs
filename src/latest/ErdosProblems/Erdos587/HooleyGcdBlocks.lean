import ErdosProblems.Erdos587.HooleyGcdMean
import ErdosProblems.Erdos587.ArithmeticBlocks

/-! # The gcd/dyadic cover costs only one log-log factor -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_gcd_dyadic_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u M X : ℕ, 0 < u → u ≤ X →
      (∑ d ∈ u.divisors, ∑ j ∈ dyadicBlockIndices (M / d), (2 : ℝ) ^ j) ≤
        C * M * max 1 (Real.log (Real.log (X : ℝ))) := by
  obtain ⟨C, hC, hratio⟩ := exists_delta_totient_ratio_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro u M X hu huX
  have hsum := (delta_sum_divisor_reciprocal_le_totient hu).trans (hratio X u hu huX)
  calc
    _ ≤ ∑ d ∈ u.divisors, 2 * ((M / d : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun d hd => sum_dyadic_block_lengths_real_le (M / d))
    _ ≤ ∑ d ∈ u.divisors, 2 * (M : ℝ) * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hdiv : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / d := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast Nat.div_mul_le_self M d
      calc
        _ ≤ 2 * ((M : ℝ) / d) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = _ := by ring
    _ = 2 * (M : ℝ) * ∑ d ∈ u.divisors, 1 / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * (M : ℝ) * (C * max 1 (Real.log (Real.log (X : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma delta_rpow_seventh_half_mul_self {F : ℝ} (hF : 0 < F) :
    F ^ (7 / 2 : ℝ) * F = F ^ (9 / 2 : ℝ) := by
  calc
    _ = F ^ (7 / 2 : ℝ) * F ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = F ^ ((7 / 2 : ℝ) + 1) := (Real.rpow_add hF _ _).symm
    _ = _ := by norm_num

end Erdos587
