import Wikipedia.HopfProblem.EllipticHigherHomologyData

/-!
# Ordered exterior-square minors of a rank-three integral matrix

The row and column order is `(0,1), (0,2), (1,2)`, exactly the order of
`fibrePair`. The two literal elliptic square matrices are specializations
of this formula for arbitrary integral matrices.
-/

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The ordered matrix of two-by-two minors, with rows and columns indexed by `fibrePair`. -/
def torusSquareMatrix (A : FibreMatrix) : FibreMatrix := fun i j =>
  A (fibrePair i 0) (fibrePair j 0) * A (fibrePair i 1) (fibrePair j 1) -
    A (fibrePair i 0) (fibrePair j 1) * A (fibrePair i 1) (fibrePair j 0)

@[simp] theorem torusSquareMatrix_apply (A : FibreMatrix) (i j : Fin 3) :
    torusSquareMatrix A i j =
      A (fibrePair i 0) (fibrePair j 0) * A (fibrePair i 1) (fibrePair j 1) -
        A (fibrePair i 0) (fibrePair j 1) * A (fibrePair i 1) (fibrePair j 0) := rfl

/-- Each coefficient is the determinant of the corresponding actual submatrix. -/
theorem torusSquareMatrix_eq_det_submatrix (A : FibreMatrix) (i j : Fin 3) :
    torusSquareMatrix A i j = (A.submatrix (fibrePair i) (fibrePair j)).det := by
  rw [Matrix.det_fin_two]
  rfl

/-- The source's two explicit exterior-square matrices have this same ordered-minor convention. -/
@[simp] theorem torusSquareMatrix_fibreMatrix (j : Kind) :
    torusSquareMatrix (fibreMatrix j) = fibreSquareMatrix j := by
  ext i k
  exact (fibreSquareMatrix_minor j i k).symm

end Wikipedia.HopfProblem.Elliptic.HigherHomology
