import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductCoordinates
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace and a scalar bound for the symmetric cross-product map

Its trace is determined by the sum of the squared complex coordinates.
On the unit sphere that sum lies in the closed unit disk.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def squareSum (z : Vector) : ℂ := ∑ r, z r ^ 2

theorem matrix_trace (z : Vector) : (matrix z).trace = squareSum z := by
  simp only [Matrix.trace, Matrix.diag, matrix_diagonal, squareSum]

theorem symmetric_matrix_trace (z : Vector) :
    (matrix z * (matrix z).transpose).trace = squareSum z ^ 2 + 2 * star (squareSum z) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    matrix, outer, crossMatrix, squareSum, Matrix.cons_val_two]
  ring

theorem symmetricMap_trace (z : UnitSphere) :
    (symmetricMap z).val.val.trace = squareSum z.val ^ 2 + 2 * star (squareSum z.val) := by
  rw [symmetricMap_val, symmetric_matrix_trace]

theorem norm_squareSum_le_one (z : UnitSphere) : ‖squareSum z.val‖ ≤ 1 := by
  have hn : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  calc
    ‖squareSum z.val‖ ≤ ∑ r, ‖z.val r ^ 2‖ := norm_sum_le _ _
    _ = ∑ r, ‖z.val r‖ ^ 2 := by simp only [norm_pow]
    _ = ‖z.val‖ ^ 2 := (EuclideanSpace.norm_sq_eq z.val).symm
    _ = 1 := by rw [hn, one_pow]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
