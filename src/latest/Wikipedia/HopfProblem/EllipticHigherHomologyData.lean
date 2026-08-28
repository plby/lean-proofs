import Wikipedia.HopfProblem.EllipticData
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The actual three-dimensional elliptic fibre matrices

The primitive special twist splits the integral four-dimensional lattice
into its twist direction and the kernel of the first coordinate.  The
matrices here are the restrictions of the source's actual `A₁` and `A₂`
to that kernel.  Their exterior-square matrices use the ordered pairs
`(0,1)`, `(0,2)`, `(1,2)`.
-/

noncomputable section

open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

abbrev FibreLattice := Fin 3 → ℤ
abbrev FibreMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- The restriction of the actual integral elliptic action to `ker γ`. -/
def fibreMatrix : Kind → FibreMatrix
  | .three => !![0, 1, 0; -1, -1, 0; 1, 0, 1]
  | .four => !![0, -1, 0; 1, 0, 0; 0, 1, 1]

theorem fibreMatrix_eq_submatrix (j : Kind) :
    fibreMatrix j = j.matrix.submatrix Fin.succ Fin.succ := by
  cases j <;> decide

theorem fibreMatrix_det (j : Kind) : (fibreMatrix j).det = 1 := by
  cases j <;> decide

theorem fibreMatrix_pow_order (j : Kind) : (fibreMatrix j) ^ j.order = 1 := by
  cases j <;> decide

/-- The actual restricted determinant-one lattice automorphism. -/
def fibreSL (j : Kind) : SL(3, ℤ) := ⟨fibreMatrix j, fibreMatrix_det j⟩

@[simp] theorem fibreSL_val (j : Kind) : (fibreSL j : FibreMatrix) = fibreMatrix j := rfl

/-- The increasing pairs in their usual exterior-square order. -/
def fibrePair : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![0, 2], ![1, 2]]

/-- The exterior square of the restricted actual elliptic action. -/
def fibreSquareMatrix : Kind → FibreMatrix
  | .three => !![1, 0, 0; -1, 0, 1; 1, -1, -1]
  | .four => !![1, 0, 0; 0, 0, -1; 1, 1, 0]

theorem fibreSquareMatrix_minor (j : Kind) (i k : Fin 3) :
    fibreSquareMatrix j i k =
      fibreMatrix j (fibrePair i 0) (fibrePair k 0) *
        fibreMatrix j (fibrePair i 1) (fibrePair k 1) -
      fibreMatrix j (fibrePair i 0) (fibrePair k 1) *
        fibreMatrix j (fibrePair i 1) (fibrePair k 0) := by
  cases j <;> fin_cases i <;> fin_cases k <;> decide

theorem fibreSquareMatrix_det (j : Kind) : (fibreSquareMatrix j).det = 1 := by
  cases j <;> decide

theorem fibreSquareMatrix_pow_order (j : Kind) :
    (fibreSquareMatrix j) ^ j.order = 1 := by
  cases j <;> decide

end Wikipedia.HopfProblem.Elliptic.HigherHomology
