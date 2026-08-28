import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCornerHomotopy

/-! # The zero-corner homotopy preserves real entries -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

theorem atAngle_real (θ : ℝ) (U : Domain N M)
    (hU : ∀ i j, star (U.val.val i j) = U.val.val i j) (i j : N ⊕ M) :
    star ((atAngle θ U).val i j) = (atAngle θ U).val i j := by
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp [atAngle, deformation, Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.mul_apply, Matrix.one_apply, apply_ite, hU,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
  all_goals split_ifs <;> simp_all

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCorner
