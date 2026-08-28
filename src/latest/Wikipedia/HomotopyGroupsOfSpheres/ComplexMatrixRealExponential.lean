import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixHilbertSchmidt
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryEndpointVariation
import Wikipedia.NoExoticSixSphere.OrthogonalExponential

/-! # The complex real action preserves the actual exponentials and constrained variations -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform
open ImaginarySymmetricMatrices RealSymmetricMixing QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

open scoped Matrix.Norms.Operator in
theorem action_exp (A : Matrix N N ℂ) :
    action (NormedSpace.exp A) = NormedSpace.exp (action A) := by
  simpa only [] using! NormedSpace.map_exp (representation (N := N)) continuous_action A

def skewMap : DirectionSpace N →ₗ[ℝ] SkewOperators (2 * Fintype.card N) :=
  ((representation (N := N)).toLinearMap.comp directionMap).codRestrict
    (skewAdjoint.submodule ℝ (RealSpace N →L[ℝ] RealSpace N)) (by
      intro A
      change (action (imaginary A.val)).adjoint = -action (imaginary A.val)
      rw [← action_star, (imaginary_relations A).2.1]
      exact representation.map_neg (imaginary A.val))

theorem skewMap_coe (A : DirectionSpace N) :
    (skewMap A).val = action (imaginary A.val) := rfl

theorem skewMap_injective : Function.Injective (skewMap (N := N)) := by
  intro A B h
  exact directionMap_injective (action_injective (congrArg Subtype.val h))

def specialOrthogonal (B : SpecialSpace N) : OrthogonalOperators (2 * Fintype.card N) :=
  orthogonal B.val.val

theorem specialOrthogonal_exponential (A : DirectionSpace N) :
    specialOrthogonal (exponential A) =
      NoExoticSixSphere.OrthogonalExponential.exp (skewMap A) := by
  apply Subtype.ext
  apply Subtype.ext
  exact action_exp (imaginary A.val)

theorem specialOrthogonal_curve (A : DirectionSpace N) (t : ℝ) :
    specialOrthogonal (exponentialCurve A t) =
      NoExoticSixSphere.OrthogonalExponential.exp (t • skewMap A) := by
  rw [exponentialCurve, specialOrthogonal_exponential, map_smul]

theorem specialOrthogonal_sandwich (A : DirectionSpace N) (B : SpecialSpace N) :
    specialOrthogonal (sandwich A B) =
      NoExoticSixSphere.OrthogonalExponential.exp ((1 / 2 : ℝ) • skewMap A) *
        specialOrthogonal B *
        NoExoticSixSphere.OrthogonalExponential.exp ((1 / 2 : ℝ) • skewMap A) := by
  rw [← map_smul, ← specialOrthogonal_exponential]
  apply Subtype.ext
  apply Subtype.ext
  change action (sandwich A B).val.val.val =
    action (exponential ((1 / 2 : ℝ) • A)).val.val.val * action B.val.val.val *
      action (exponential ((1 / 2 : ℝ) • A)).val.val.val
  rw [sandwich_matrix, (exponential ((1 / 2 : ℝ) • A)).val.property, action_mul, action_mul]

theorem specialOrthogonal_endpointVariation (A C : DirectionSpace N) (s t : ℝ) :
    specialOrthogonal (endpointVariation A C s t) =
      NoExoticSixSphere.OrthogonalExponential.exp ((1 / 2 : ℝ) • (t • skewMap A)) *
        NoExoticSixSphere.OrthogonalExponential.exp ((s * Real.sin (Real.pi * t)) • skewMap C) *
        NoExoticSixSphere.OrthogonalExponential.exp ((1 / 2 : ℝ) • (t • skewMap A)) := by
  rw [endpointVariation, specialOrthogonal_sandwich, specialOrthogonal_exponential,
    map_smul, map_smul]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
