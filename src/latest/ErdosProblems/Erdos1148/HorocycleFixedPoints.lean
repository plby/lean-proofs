import ErdosProblems.Erdos1148.HorocycleContraction
import ErdosProblems.Erdos1148.MautnerContraction

/-! # A vector fixed by the diagonal time-one map is fixed by both horocycles -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem diagonal_nat_smul_fixed {X : Type*} [MulAction SL(2, ℝ) X] {x : X}
    (hx : diagonalFlow 1 • x = x) (n : ℕ) : diagonalFlow (n : ℝ) • x = x := by
  induction n with
  | zero => simp only [Nat.cast_zero, diagonalFlow_zero, one_smul]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, diagonalFlow_add, mul_smul, hx, ih]

theorem horocycles_fixed_of_diagonal_fixed {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X]
    {x : X} (hx : diagonalFlow 1 • x = x) :
    (∀ r : ℝ, stableHorocycle r • x = x) ∧ (∀ r : ℝ, unstableHorocycle r • x = x) := by
  constructor
  · intro r
    exact fixed_of_conjugates_tendsto_one (diagonal_nat_smul_fixed hx)
      (stableHorocycle_conjugates_tendsto_one r)
  · intro r
    apply fixed_of_conjugates_tendsto_one (g := fun n : ℕ => diagonalFlow (-(n : ℝ)))
      (hconj := unstableHorocycle_conjugates_tendsto_one r)
    intro n
    rw [diagonalFlow_neg]
    calc
      (diagonalFlow (n : ℝ))⁻¹ • x = (diagonalFlow (n : ℝ))⁻¹ • (diagonalFlow (n : ℝ) • x) := by
        rw [diagonal_nat_smul_fixed hx n]
      _ = x := inv_smul_smul _ _

end Erdos1148.DukeArithmetic
