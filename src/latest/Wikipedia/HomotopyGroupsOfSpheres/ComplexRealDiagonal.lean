import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

/-! # The exact realification of a real diagonal complex matrix -/

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

theorem matrix_ofReal_diagonal {N : Type*} [DecidableEq N] (d : N → ℝ) :
    matrix (Matrix.diagonal (fun i ↦ (d i : ℂ))) = Matrix.diagonal (Sum.elim d d) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals by_cases h : i = j <;> simp [matrix, h]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
