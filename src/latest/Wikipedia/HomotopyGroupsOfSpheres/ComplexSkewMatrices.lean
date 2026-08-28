import Wikipedia.HomotopyGroupsOfSpheres.UnitaryMatrixLogarithmRelations
import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealExponential
import Wikipedia.HomotopyGroupsOfSpheres.FiniteSubmoduleProjection

/-! # Complex skew-Hermitian matrices and their actual real orthogonal action -/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices

open NoExoticSixSphere.CayleyTransform

variable {N : Type*} [Fintype N] [DecidableEq N]

abbrev Space (N : Type*) [Fintype N] :=
  ↥(skewAdjoint.submodule ℝ (Matrix N N ℂ))

def toOrthogonalSkew : Space N →ₗ[ℝ] SkewOperators (2 * Fintype.card N) :=
  ((ComplexMatrixRealRepresentation.representation (N := N)).toLinearMap.comp
    (skewAdjoint.submodule ℝ (Matrix N N ℂ)).subtype).codRestrict
      (skewAdjoint.submodule ℝ (ComplexMatrixRealRepresentation.RealSpace N →L[ℝ]
        ComplexMatrixRealRepresentation.RealSpace N)) (by
    intro K
    change (ComplexMatrixRealRepresentation.action K.val).adjoint =
      -ComplexMatrixRealRepresentation.action K.val
    rw [← ComplexMatrixRealRepresentation.action_star, K.property]
    exact ComplexMatrixRealRepresentation.representation.map_neg K.val)

theorem continuous_toOrthogonalSkew : Continuous (toOrthogonalSkew (N := N)) :=
  (finiteLinearMap_contDiff (toOrthogonalSkew (N := N))).continuous

def projection : Matrix N N ℂ →L[ℝ] Space N :=
  finiteSubmoduleProjection (skewAdjoint.submodule ℝ (Matrix N N ℂ))

omit [DecidableEq N] in
theorem projection_coe (K : Space N) : projection K.val = K :=
  finiteSubmoduleProjection_apply _ K

def logarithm (U : unitary (Matrix N N ℂ)) : Space N :=
  projection (ComplexMatrixLocalLogarithm.logarithm U.val)

theorem logarithm_val (U : unitary (Matrix N N ℂ))
    (hU : U.val ∈ ComplexMatrixLocalLogarithm.domain N) :
    (logarithm U).val = ComplexMatrixLocalLogarithm.logarithm U.val := by
  let K : Space N := ⟨_, ComplexMatrixLocalLogarithm.logarithm_star U.val hU U.property⟩
  exact congrArg Subtype.val (projection_coe K)

theorem logarithm_one : logarithm (1 : unitary (Matrix N N ℂ)) = 0 := by
  change projection (ComplexMatrixLocalLogarithm.logarithm (1 : Matrix N N ℂ)) = 0
  rw [ComplexMatrixLocalLogarithm.logarithm_one, map_zero]

theorem continuousOn_logarithm : ContinuousOn (logarithm (N := N))
    {U | U.val ∈ ComplexMatrixLocalLogarithm.domain N} := by
  have hc : ContinuousOn (ComplexMatrixLocalLogarithm.logarithm (N := N))
      (ComplexMatrixLocalLogarithm.domain N) :=
    (ComplexMatrixLocalLogarithm.contDiffOn_logarithm (N := N)).continuousOn.mono (fun _ h ↦ h.1)
  exact projection.continuous.comp_continuousOn
    (hc.comp continuous_subtype_val.continuousOn (fun _ h ↦ h))

theorem exp_unitary (K : Space N) : NormedSpace.exp K.val ∈ unitary (Matrix N N ℂ) := by
  apply (Matrix.isUnit_exp K.val).mem_unitary_of_star_mul_self
  change (NormedSpace.exp K.val).conjTranspose * NormedSpace.exp K.val = 1
  rw [← Matrix.exp_conjTranspose]
  change NormedSpace.exp (star K.val) * NormedSpace.exp K.val = 1
  rw [K.property, ← Matrix.exp_add_of_commute _ _ (Commute.refl K.val).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

def exponential (K : Space N) : unitary (Matrix N N ℂ) := ⟨NormedSpace.exp K.val, exp_unitary K⟩

theorem exponential_zero : exponential (0 : Space N) = 1 :=
  Subtype.ext NormedSpace.exp_zero

theorem exponential_add_smul (K : Space N) (s t : ℝ) :
    exponential ((s + t) • K) = exponential (s • K) * exponential (t • K) := by
  apply Subtype.ext
  change NormedSpace.exp ((s + t) • K.val) =
    NormedSpace.exp (s • K.val) * NormedSpace.exp (t • K.val)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl K.val).smul_left s).smul_right t)

theorem continuous_exponential : Continuous (exponential (N := N)) :=
  (NormedSpace.exp_continuous.comp continuous_subtype_val).subtype_mk _

theorem exponential_logarithm (U : unitary (Matrix N N ℂ))
    (hU : U.val ∈ ComplexMatrixLocalLogarithm.domain N) : exponential (logarithm U) = U := by
  apply Subtype.ext
  change NormedSpace.exp (logarithm U).val = U.val
  rw [logarithm_val U hU]
  exact ComplexMatrixLocalLogarithm.exp_logarithm U.val hU.1

theorem orthogonal_exponential (K : Space N) :
    ComplexMatrixRealRepresentation.orthogonal (exponential K) =
      NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew K) := by
  apply Subtype.ext
  apply Subtype.ext
  exact ComplexMatrixRealRepresentation.action_exp K.val

theorem logarithm_inverse (U : unitary (Matrix N N ℂ))
    (hU : U.val ∈ ComplexMatrixLocalLogarithm.domain N) :
    logarithm U⁻¹ = -logarithm U := by
  apply Subtype.ext
  rw [logarithm_val U⁻¹ (ComplexMatrixLocalLogarithm.logarithm_inverse U hU).1]
  change ComplexMatrixLocalLogarithm.logarithm (U⁻¹).val = -(logarithm U).val
  rw [logarithm_val U hU]
  exact (ComplexMatrixLocalLogarithm.logarithm_inverse U hU).2

end Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices
