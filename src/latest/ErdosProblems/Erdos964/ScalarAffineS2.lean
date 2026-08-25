import ErdosProblems.Erdos964.AffineSemiprimeDecomposition
import ErdosProblems.Erdos964.ScalarAffineS1

/-!
# Expanding the actual scalar second sum

The second sum is the square weight restricted to a prescribed set of
distinguished affine values. Its expansion uses the actual divisor counts.
-/

namespace Erdos964

open scoped BigOperators

noncomputable def scalarAffineSecondSum (A B : Fin 3 → ℕ) (j : Fin 3)
    (N P : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ico N (2 * N)).filter (fun n => A j * n + B j ∈ S),
    scalarAffineWeight A B P w n

theorem scalarAffineSecondSum_eq_pair_count (A B : Fin 3 → ℕ) (j : Fin 3)
    (N P : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) :
    scalarAffineSecondSum A B j N P w S =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (affineDivisorValueCount A B j N (Nat.lcm d e) S : ℝ) * (w d * w e) := by
  unfold scalarAffineSecondSum
  simp_rw [scalarAffineWeight_eq_pair_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  unfold affineDivisorValueCount affineDivisorParameters
  congr 1
  ext n
  simp only [Finset.mem_filter]
  tauto

theorem scalarAffineSecondSum_error_le (A B : Fin 3 → ℕ) (j : Fin 3)
    (N P : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) (M E : ℕ → ℝ)
    (hE : ∀ d ∈ P.divisors, ∀ e ∈ P.divisors,
      w d * w e ≠ 0 →
      |(affineDivisorValueCount A B j N (Nat.lcm d e) S : ℝ) - M (Nat.lcm d e)| ≤
        E (Nat.lcm d e)) :
    |scalarAffineSecondSum A B j N P w S -
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, M (Nat.lcm d e) * (w d * w e)| ≤
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, E (Nat.lcm d e) * |w d * w e| := by
  rw [scalarAffineSecondSum_eq_pair_count, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  by_cases hzero : w d * w e = 0
  · simp only [hzero, mul_zero, abs_zero, le_refl]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hE d hd e he hzero) (abs_nonneg _)

end Erdos964
