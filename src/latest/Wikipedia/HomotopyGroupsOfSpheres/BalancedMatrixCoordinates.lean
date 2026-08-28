import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameAction

/-! # Exact coordinate entries of the real orthogonal matrix representation -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

theorem projectionRepresentation_basis (n : ℕ) (A : Matrix (Index n) (Index n) ℝ)
    (i j : Fin (n + n)) :
    projectionRepresentation n A (EuclideanSpace.basisFun (Fin (n + n)) ℝ j) i =
      A ((finSumFinEquiv : Index n ≃ Fin (n + n)).symm i) (finSumFinEquiv.symm j) := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv A)
      (EuclideanSpace.basisFun (Fin (n + n)) ℝ j)).ofLp i = _
  rw [EuclideanSpace.basisFun_apply]
  change ((Matrix.reindex finSumFinEquiv finSumFinEquiv A) *ᵥ Pi.single j (1 : ℝ)) i = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem matrixOrthogonal_basis {n : ℕ} (U : unitary (Matrix (Index n) (Index n) ℝ))
    (i j : Fin (n + n)) :
    (matrixOrthogonal U).val.val (EuclideanSpace.basisFun (Fin (n + n)) ℝ j) i =
      U.val ((finSumFinEquiv : Index n ≃ Fin (n + n)).symm i) (finSumFinEquiv.symm j) :=
  projectionRepresentation_basis n U.val i j

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
