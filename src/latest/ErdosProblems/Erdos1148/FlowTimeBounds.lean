import ErdosProblems.Erdos1148.FlowVectorLengths

/-! # Comparing lattice-vector lengths at two arbitrary flow times -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma flow_frame_time_change (g : SL(2, ℝ)) (s t : ℝ) :
    (g * diagonalFlow s) * diagonalFlow (t - s) = g * diagonalFlow t := by
  rw [mul_assoc, ← diagonalFlow_add, add_sub_cancel]

theorem modularVectorLengthSq_flow_time_le (g : SL(2, ℝ)) (s t : ℝ) (u v : ℤ) :
    modularVectorLengthSq (g * diagonalFlow t) u v ≤
      Real.exp |t - s| * modularVectorLengthSq (g * diagonalFlow s) u v := by
  simpa only [flow_frame_time_change] using
    modularVectorLengthSq_flow_le (g * diagonalFlow s) (t - s) u v

theorem modularVectorLengthSq_of_short_time (g : SL(2, ℝ)) (s t H C : ℝ)
    (u v : ℤ) (hshort : modularVectorLengthSq (g * diagonalFlow s) u v < (H ^ 2)⁻¹)
    (hscale : Real.exp |t - s| * (H ^ 2)⁻¹ ≤ C ^ 2) :
    modularVectorLengthSq (g * diagonalFlow t) u v < C ^ 2 :=
  (modularVectorLengthSq_flow_time_le g s t u v).trans_lt
    ((mul_lt_mul_of_pos_left hshort (Real.exp_pos _)).trans_le hscale)

end Erdos1148.DukeArithmetic
