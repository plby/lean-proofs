import Wikipedia.HomotopyGroupsOfSpheres.BalancedPositiveProjection

/-!
# The balanced real orbit is homeomorphic to rank-n orthogonal projections

The inverse sends an orthogonal projection to twice its matrix minus the
identity. Rank determines the trace, and the proved intrinsic classification
places this symmetric involution in the original balanced orbit.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open NoExoticSixSphere.GLOrthonormalization

abbrev ProjectionSpace (n : ℕ) :=
  {P : Vector (n + n) →L[ℝ] Vector (n + n) //
    IsIdempotentElem P ∧ IsSelfAdjoint P ∧ Module.finrank ℝ P.range = n}

def toProjection {n : ℕ} (J : Space n) : ProjectionSpace n :=
  ⟨positiveProjection J, positiveProjection_idempotent J,
    positiveProjection_selfAdjoint J, positiveProjection_rank J⟩

theorem continuous_toProjection (n : ℕ) : Continuous (toProjection (n := n)) :=
  (continuous_positiveProjection n).subtype_mk _

def projectionMatrix {n : ℕ} (P : ProjectionSpace n) : Matrix (Index n) (Index n) ℝ :=
  (projectionRepresentation n).symm P.val

theorem projectionMatrix_idempotent {n : ℕ} (P : ProjectionSpace n) :
    IsIdempotentElem (projectionMatrix P) := by
  change (projectionRepresentation n).symm P.val * (projectionRepresentation n).symm P.val =
    (projectionRepresentation n).symm P.val
  rw [← map_mul, P.property.1]

theorem projectionMatrix_transpose {n : ℕ} (P : ProjectionSpace n) :
    (projectionMatrix P).transpose = projectionMatrix P := by
  rw [← RealUnitaryMatrices.star_eq_transpose]
  apply (projectionRepresentation n).injective
  change projectionRepresentation n (star ((projectionRepresentation n).symm P.val)) =
    projectionRepresentation n ((projectionRepresentation n).symm P.val)
  rw [projectionRepresentation_star, AlgEquiv.apply_symm_apply]
  exact P.property.2.1

theorem projectionMatrix_trace {n : ℕ} (P : ProjectionSpace n) :
    (projectionMatrix P).trace = (n : ℝ) := by
  have hi : IsIdempotentElem P.val.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap P.property.1
  have ht := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hi).trace
  have he := projectionRepresentation_trace n (projectionMatrix P)
  change LinearMap.trace ℝ (Vector (n + n))
    (projectionRepresentation n ((projectionRepresentation n).symm P.val)).toLinearMap = _ at he
  rw [AlgEquiv.apply_symm_apply, ht, P.property.2.2] at he
  exact he.symm

def involutionMatrix {n : ℕ} (P : ProjectionSpace n) : Matrix (Index n) (Index n) ℝ :=
  (2 : ℝ) • projectionMatrix P - 1

theorem involutionMatrix_transpose {n : ℕ} (P : ProjectionSpace n) :
    (involutionMatrix P).transpose = involutionMatrix P := by
  rw [involutionMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    projectionMatrix_transpose, Matrix.transpose_one]

theorem involutionMatrix_square {n : ℕ} (P : ProjectionSpace n) :
    involutionMatrix P * involutionMatrix P = 1 := by
  have hP : projectionMatrix P * projectionMatrix P = projectionMatrix P :=
    projectionMatrix_idempotent P
  simp only [involutionMatrix, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hP]
  module

theorem involutionMatrix_trace {n : ℕ} (P : ProjectionSpace n) :
    (involutionMatrix P).trace = 0 := by
  rw [involutionMatrix, Matrix.trace_sub, Matrix.trace_smul, projectionMatrix_trace,
    Matrix.trace_one]
  simp only [Index, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, smul_eq_mul]
  ring

def ofProjection {n : ℕ} (P : ProjectionSpace n) : Space n :=
  ofRelations n (involutionMatrix P) (involutionMatrix_transpose P)
    (involutionMatrix_square P) (involutionMatrix_trace P)

theorem continuous_ofProjection (n : ℕ) : Continuous (ofProjection (n := n)) := by
  have hc : Continuous (projectionMatrix (n := n)) :=
    (finiteLinearMap_contDiff (projectionRepresentation n).symm.toLinearMap).continuous.comp
      continuous_subtype_val
  exact ((hc.const_smul (2 : ℝ)).sub continuous_const).subtype_mk _

theorem ofProjection_toProjection {n : ℕ} (J : Space n) :
    ofProjection (toProjection J) = J := by
  apply Subtype.ext
  change (2 : ℝ) • (projectionRepresentation n).symm
    (projectionRepresentation n (positiveMatrix J)) - 1 = J.val
  rw [AlgEquiv.symm_apply_apply, positiveMatrix]
  module

theorem toProjection_ofProjection {n : ℕ} (P : ProjectionSpace n) :
    toProjection (ofProjection P) = P := by
  apply Subtype.ext
  change projectionRepresentation n
    ((1 / 2 : ℝ) • (1 + ((2 : ℝ) • (projectionRepresentation n).symm P.val - 1))) = P.val
  have he : (1 / 2 : ℝ) • (1 + ((2 : ℝ) • (projectionRepresentation n).symm P.val - 1)) =
      (projectionRepresentation n).symm P.val := by module
  rw [he, AlgEquiv.apply_symm_apply]

def projectionHomeomorph (n : ℕ) : Space n ≃ₜ ProjectionSpace n where
  toFun := toProjection
  invFun := ofProjection
  left_inv := ofProjection_toProjection
  right_inv := toProjection_ofProjection
  continuous_toFun := continuous_toProjection n
  continuous_invFun := continuous_ofProjection n

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
