import Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder

/-! # Diagonal matrices under a scalar coordinate inclusion -/

namespace Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder

theorem border_diagonal {R : Type*} [Semiring R] {n : ℕ} (a : R) (d : Fin n → R) :
    border a (Matrix.diagonal d) = Matrix.diagonal (Fin.cons a d) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [border, Matrix.diagonal_apply, eq_comm]

end Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder
