import ErdosProblems.Erdos964.ScalarWeightedMoments
import ErdosProblems.Erdos964.ScalarAffineModel

/-!
# The concrete first polynomial moment

The exact strict endpoint is retained as `R-1`.
-/

namespace Erdos964

noncomputable def scalarFirstMomentPolynomial (q : ℝ) : ℝ :=
  49 / 6 * q ^ 3 - 21 / 2 * q ^ 4 + 18 / 5 * q ^ 5

theorem scalarFirstMomentPolynomial_one : scalarFirstMomentPolynomial 1 = 19 / 15 := by
  norm_num [scalarFirstMomentPolynomial]

theorem scalarCandidateFirstMain_eq_log_moments (M R : ℕ) (hR : 1 ≤ R) :
    scalarCandidateFirstMain M R = 49 * scalarLogMoment M 3 R (R - 1) 0 -
      84 * scalarLogMoment M 3 R (R - 1) 1 + 36 * scalarLogMoment M 3 R (R - 1) 2 := by
  classical
  have hinterval : Finset.Icc 0 (R - 1) = insert 0 (Finset.Ico 1 R) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hzero (j : ℕ) : scalarLogMoment M 3 R (R - 1) j =
      ∑ n ∈ Finset.Ico 1 R, normalizedLogMonomial (Real.log R) j n * scalarMomentAF M 3 n := by
    unfold scalarLogMoment
    rw [hinterval, Finset.sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
  rw [hzero 0, hzero 1, hzero 2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, scalarCandidateFirstMain, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Ico.mp hn).1
  have hnR := (Finset.mem_Ico.mp hn).2
  rw [scalarMomentAF_three]
  by_cases h : Squarefree n ∧ n.Coprime M
  · have hcut : 1 ≤ n ∧ n < R := ⟨hn1, hnR⟩
    simp only [if_pos h, scalarLinearY, if_pos hcut, linearSieveWeight,
      normalizedLogMonomial_eq, pow_zero, pow_one]
    ring
  · simp only [if_neg h, mul_zero, sub_self, zero_add]

end Erdos964
