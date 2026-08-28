import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldFibresAlgebra
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Actual ranks of the small-resolution matrices

The two native chart matrices are literal outer products. Their ranks are
at most one, and are exactly one away from the zero normal vector. The
explicit chart representation of every determinant-zero matrix gives the
same rank bounds for the unchanged complex matrix space.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ConifoldStandardBoundary

/-- The lower chart matrix is the literal outer product of its line and row vectors. -/
theorem lowerMatrix_eq_vecMulVec (a : ℂ) (p : ℂ × ℂ) :
    lowerMatrix a p = Matrix.vecMulVec ![1, a] ![p.1, p.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerMatrix, Matrix.vecMulVec]

/-- The upper chart matrix is the literal outer product of its line and row vectors. -/
theorem upperMatrix_eq_vecMulVec (b : ℂ) (p : ℂ × ℂ) :
    upperMatrix b p = Matrix.vecMulVec ![b, 1] ![p.1, p.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix, Matrix.vecMulVec]

/-- The actual lower-chart matrix has rank at most one. -/
theorem lowerMatrix_rank_le_one (a : ℂ) (p : ℂ × ℂ) :
    (lowerMatrix a p).rank ≤ 1 := by
  rw [lowerMatrix_eq_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- The actual upper-chart matrix has rank at most one. -/
theorem upperMatrix_rank_le_one (b : ℂ) (p : ℂ × ℂ) :
    (upperMatrix b p).rank ≤ 1 := by
  rw [upperMatrix_eq_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- The two literal chart forms prove the rank bound for every determinant-zero matrix. -/
theorem matrix_rank_le_one_of_det_zero (M : MatrixSpace) (hdet : M.det = 0) :
    M.rank ≤ 1 := by
  obtain ⟨a, p, rfl⟩ | ⟨b, p, rfl⟩ := exists_matrix_chart_of_det_zero M hdet
  · exact lowerMatrix_rank_le_one a p
  · exact upperMatrix_rank_le_one b p

/-- In the original finite-dimensional complex matrix space, rank zero means matrix zero. -/
theorem matrix_rank_eq_zero_iff (M : MatrixSpace) : M.rank = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hcols : Submodule.span ℂ (Set.range M.col) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rwa [← Matrix.rank_eq_finrank_span_cols]
    ext i j
    have hcol : M.col j ∈ (⊥ : Submodule ℂ (Fin 2 → ℂ)) := by
      rw [← hcols]
      exact Submodule.subset_span (mem_range_self j)
    exact congrFun ((Submodule.mem_bot ℂ).mp hcol) i
  · rintro rfl
    exact Matrix.rank_zero

/-- Every nonzero determinant-zero matrix in the actual target has rank exactly one. -/
theorem matrix_rank_eq_one_of_det_zero (M : MatrixSpace) (hdet : M.det = 0)
    (hM : M ≠ 0) : M.rank = 1 := by
  apply le_antisymm (matrix_rank_le_one_of_det_zero M hdet)
  exact Nat.one_le_iff_ne_zero.mpr (fun h => hM ((matrix_rank_eq_zero_iff M).mp h))

/-- A nonzero lower-chart normal vector gives an actual rank-one matrix. -/
theorem lowerMatrix_rank_eq_one (a : ℂ) (p : ℂ × ℂ) (hp : p ≠ 0) :
    (lowerMatrix a p).rank = 1 :=
  matrix_rank_eq_one_of_det_zero _ (lowerMatrix_det a p)
    (fun h => hp ((lowerMatrix_eq_zero_iff a p).mp h))

/-- A nonzero upper-chart normal vector gives an actual rank-one matrix. -/
theorem upperMatrix_rank_eq_one (b : ℂ) (p : ℂ × ℂ) (hp : p ≠ 0) :
    (upperMatrix b p).rank = 1 :=
  matrix_rank_eq_one_of_det_zero _ (upperMatrix_det b p)
    (fun h => hp ((upperMatrix_eq_zero_iff b p).mp h))

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
