import ErdosProblems.Erdos1148.BufferedCuspVector
import ErdosProblems.Erdos1148.ExcursionEnergyBounds

/-! # A returning excursion vector is uniformly nonzero at the buffered endpoints -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma buffered_energy_lower {H X Y : ℝ} (hH : 0 < H) (hY : 0 ≤ Y)
    (hX : (H ^ 2)⁻¹ * cuspEndpointLengthSqLower ≤ X) :
    cuspEndpointLengthSqLower ≤
      Real.exp (2 * Real.log H) * X + Real.exp (-(2 * Real.log H)) * Y := by
  calc
    cuspEndpointLengthSqLower =
        Real.exp (2 * Real.log H) * ((H ^ 2)⁻¹ * cuspEndpointLengthSqLower) := by
      rw [← mul_assoc, exp_two_log_mul_inv_sq hH, one_mul]
    _ ≤ Real.exp (2 * Real.log H) * X :=
      mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
    _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le hY)

theorem buffered_initial_vector_lengthSq_lower (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 0 < H) (hL : 1 ≤ L) (u v : ℤ)
    (hprev : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow (-1)) u v)
    (hnext : modularVectorLengthSq (g * diagonalFlow L) u v ≤ (H ^ 2)⁻¹) :
    cuspEndpointLengthSqLower ≤
      modularVectorLengthSq (g * diagonalFlow (-(2 * Real.log H))) u v := by
  rw [modularVectorLengthSq_flow, neg_neg] at hprev
  rw [modularVectorLengthSq_flow] at hnext
  have hX := exponential_energy_initial_coefficient_lower
    (sq_nonneg (modularVector g u v).1) (sq_nonneg (modularVector g u v).2) hL hprev hnext
  rw [modularVectorLengthSq_flow, neg_neg]
  exact buffered_energy_lower hH (sq_nonneg _) hX

theorem buffered_terminal_vector_lengthSq_lower (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 0 < H) (hL : 1 ≤ L) (u v : ℤ)
    (hprev : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow 1) u v)
    (hnext : modularVectorLengthSq (g * diagonalFlow (-L)) u v ≤ (H ^ 2)⁻¹) :
    cuspEndpointLengthSqLower ≤
      modularVectorLengthSq (g * diagonalFlow (2 * Real.log H)) u v := by
  rw [modularVectorLengthSq_flow] at hprev
  rw [modularVectorLengthSq_flow, neg_neg] at hnext
  have hY := exponential_energy_initial_coefficient_lower
    (sq_nonneg (modularVector g u v).2) (sq_nonneg (modularVector g u v).1) hL
    (by simpa only [add_comm] using hprev) (by simpa only [add_comm] using hnext)
  rw [modularVectorLengthSq_flow, add_comm]
  exact buffered_energy_lower hH (sq_nonneg _) hY

end Erdos1148.DukeArithmetic
