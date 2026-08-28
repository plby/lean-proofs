import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameProjection
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealConjugation
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-! # Matrix conjugation is the actual orthogonal action on balanced frames -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

theorem projectionRepresentation_norm (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    ∀ x, ‖projectionRepresentation n U.val x‖ = ‖x‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
  change star (projectionRepresentation n U.val) * projectionRepresentation n U.val = 1
  rw [← projectionRepresentation_star, ← map_mul, U.property.1, map_one]

def matrixOrthogonal :
    unitary (Matrix (Index n) (Index n) ℝ) →* OrthogonalOperators (n + n) where
  toFun U := ⟨⟨projectionRepresentation n U.val,
    OrthogonalCompactness.normPreserving_isInvertible _ (projectionRepresentation_norm U)⟩,
    projectionRepresentation_norm U⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (projectionRepresentation n)))
  map_mul' U V := Subtype.ext (Subtype.ext ((projectionRepresentation n).map_mul U.val V.val))

theorem matrixOrthogonal_operator (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    (matrixOrthogonal U).val.val = projectionRepresentation n U.val := rfl

theorem continuous_matrixOrthogonal :
    Continuous (matrixOrthogonal (n := n)) :=
  (((continuous_projectionRepresentation n).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem positiveMatrix_conjugate (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) :
    positiveMatrix (conjugate U J) = U.val * positiveMatrix J * U.val.transpose := by
  have hU : U.val * U.val.transpose = 1 := by
    simpa only [RealUnitaryMatrices.star_eq_transpose] using U.property.2
  change (1 / 2 : ℝ) • (1 + U.val * J.val * U.val.transpose) =
    U.val * ((1 / 2 : ℝ) • (1 + J.val)) * U.val.transpose
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, hU]

theorem positiveProjection_conjugate (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) :
    positiveProjection (conjugate U J) =
      (matrixOrthogonal U).val.val * positiveProjection J * star (matrixOrthogonal U).val.val := by
  change projectionRepresentation n (positiveMatrix (conjugate U J)) =
    projectionRepresentation n U.val * projectionRepresentation n (positiveMatrix J) *
      star (projectionRepresentation n U.val)
  rw [positiveMatrix_conjugate, map_mul, map_mul, ← projectionRepresentation_star,
    RealUnitaryMatrices.star_eq_transpose]

namespace FrameProjection

theorem operator_action (U : unitary (Matrix (Index n) (Index n) ℝ))
    (A : Stiefel.Space (n + n) n) :
    operator (Stiefel.action (matrixOrthogonal U) A) =
      (matrixOrthogonal U).val.val * operator A * star (matrixOrthogonal U).val.val := by
  change ((matrixOrthogonal U).val.val.comp A.val).comp
    ((matrixOrthogonal U).val.val.comp A.val).adjoint =
      ((matrixOrthogonal U).val.val.comp (A.val.comp A.val.adjoint)).comp
        (matrixOrthogonal U).val.val.adjoint
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

theorem toBalanced_action (U : unitary (Matrix (Index n) (Index n) ℝ))
    (A : Stiefel.Space (n + n) n) :
    toBalanced (Stiefel.action (matrixOrthogonal U) A) = conjugate U (toBalanced A) := by
  apply positiveProjection_injective n
  rw [positiveProjection_toBalanced, operator_action, positiveProjection_conjugate,
    positiveProjection_toBalanced]

end FrameProjection

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
