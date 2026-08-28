import Wikipedia.HopfProblem.ConifoldPolarDefs
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Recovering the explicit Hermitian factor from its three coordinates

For two-by-two Hermitian matrices, determinant one and positive trace recover
the positive scalar part by a square root.  The proof uses the original
matrix entries; no spectral theorem or abstract polar decomposition is used.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- Half the real trace of a two-by-two matrix. -/
def scalarPart (M : MatrixSpace) : ℝ := ((M 0 0).re + (M 1 1).re) / 2

theorem hermitian_diagonal_im_zero {M : MatrixSpace} (hM : M.IsHermitian)
    (i : Fin 2) : (M i i).im = 0 := by
  have h := hM.apply i i
  change conj (M i i) = M i i at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem hermitian_lowerLeft {M : MatrixSpace} (hM : M.IsHermitian) :
    M 1 0 = conj (M 0 1) := (hM.apply 1 0).symm

theorem hermitian_coordinate_reconstruction {M : MatrixSpace} (hM : M.IsHermitian) :
    M = (scalarPart M : ℂ) • (1 : MatrixSpace) + tracelessMatrix (baseCoordinates M) := by
  have h00 := hermitian_diagonal_im_zero hM 0
  have h11 := hermitian_diagonal_im_zero hM 1
  have h10 := hermitian_lowerLeft hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [scalarPart, tracelessMatrix, baseCoordinates, h00, h11, h10] <;> ring

theorem scalarPart_sq_sub_baseCoordinates_norm_sq {M : MatrixSpace}
    (hM : M.IsHermitian) :
    scalarPart M ^ 2 - ‖baseCoordinates M‖ ^ 2 = M.det.re := by
  have h00 := hermitian_diagonal_im_zero hM 0
  have h11 := hermitian_diagonal_im_zero hM 1
  have h10 := hermitian_lowerLeft hM
  simp [scalarPart, EuclideanSpace.real_norm_sq_eq, baseCoordinates,
    Fin.sum_univ_succ, Matrix.det_fin_two, h00, h11, h10]
  ring

theorem scalarPart_pos_of_trace {M : MatrixSpace} (htrace : 0 < M.trace.re) :
    0 < scalarPart M := by
  simp only [Matrix.trace_fin_two, Complex.add_re] at htrace
  unfold scalarPart
  linarith

theorem hyperbolicScale_baseCoordinates {M : MatrixSpace}
    (hM : M.IsHermitian) (hdet : M.det = 1) (htrace : 0 < M.trace.re) :
    hyperbolicScale (baseCoordinates M) = scalarPart M := by
  have hs := scalarPart_sq_sub_baseCoordinates_norm_sq hM
  rw [hdet, Complex.one_re] at hs
  have hs' : 1 + ‖baseCoordinates M‖ ^ 2 = scalarPart M ^ 2 := by linarith
  rw [hyperbolicScale, hs', Real.sqrt_sq_eq_abs,
    abs_of_pos (scalarPart_pos_of_trace htrace)]

/-- The positive-trace determinant-one Hermitian matrix is recovered from its native coordinates. -/
theorem positiveMatrix_baseCoordinates {M : MatrixSpace}
    (hM : M.IsHermitian) (hdet : M.det = 1) (htrace : 0 < M.trace.re) :
    positiveMatrix (baseCoordinates M) = M := by
  rw [positiveMatrix, hyperbolicScale_baseCoordinates hM hdet htrace]
  exact (hermitian_coordinate_reconstruction hM).symm

end Wikipedia.HopfProblem.ConifoldPolar
