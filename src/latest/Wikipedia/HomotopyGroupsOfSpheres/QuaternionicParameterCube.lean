import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeLowGenerators
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableCandidate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# A genuine generating five-cube for the explicit complex-sphere parameter

An actual orthogonal reflection adjusts the quotient sphere's base point to
the original complex coordinate axis. The resulting native cube is proved
to generate the parameter sphere's fifth homotopy group. Its stable symmetric
and determinant-one images are then defined without assuming they generate.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open SphereCubeGenerator QuaternionicSymmetricMatrices

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

def parameterBasepointIsometry : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ ((sphereFiveHomeomorph (point 5)).val - axis.val))ᗮ.reflection

theorem parameterBasepointIsometry_apply :
    parameterBasepointIsometry (sphereFiveHomeomorph (point 5)).val = axis.val := by
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp (sphereFiveHomeomorph (point 5)).property,
    mem_sphere_zero_iff_norm.mp axis.property]

def basedSphereFiveHomeomorph : Sphere 5 ≃ₜ UnitSphere :=
  sphereFiveHomeomorph.trans (SphereCenteredCoordinates.sphereIsometry parameterBasepointIsometry)

theorem basedSphereFiveHomeomorph_point : basedSphereFiveHomeomorph (point 5) = axis :=
  Subtype.ext parameterBasepointIsometry_apply

def parameterCube : GenLoop (Fin 5) UnitSphere axis :=
  pointedMapGenLoop (basedSphereFiveHomeomorph : C(_, _)) (point 5) axis
    basedSphereFiveHomeomorph_point (quotientCube 5)

def parameterCubeClass : π_ 5 UnitSphere axis := ⟦parameterCube⟧

def parameterSpherePiFiveMulEquiv : π_ 5 (Sphere 5) (point 5) ≃* π_ 5 UnitSphere axis :=
  pointedHomeomorphMulEquiv basedSphereFiveHomeomorph (point 5) axis
    basedSphereFiveHomeomorph_point

theorem parameterSpherePiFiveMulEquiv_quotient :
    parameterSpherePiFiveMulEquiv (quotientClass 5) = parameterCubeClass :=
  pointedHomeomorphMulEquiv_mk basedSphereFiveHomeomorph (point 5) axis
    basedSphereFiveHomeomorph_point (quotientCube 5)

theorem parameterCubeClass_generates :
    Function.Surjective (fun k : ℤ ↦ parameterCubeClass ^ k) := by
  intro a
  obtain ⟨k, hk⟩ := quotientClass_five_generates (parameterSpherePiFiveMulEquiv.symm a)
  refine ⟨k, ?_⟩
  change parameterCubeClass ^ k = a
  change quotientClass 5 ^ k = parameterSpherePiFiveMulEquiv.symm a at hk
  rw [← parameterSpherePiFiveMulEquiv_quotient, ← map_zpow, hk, MulEquiv.apply_symm_apply]

def stableInputCube (r : ℕ) : GenLoop (Fin 5) (Space (Fin (3 + r))) identity :=
  pointedMapGenLoop (stableSymmetricInput r) axis identity
    (stableSymmetricInput_axis r) parameterCube

def stableInputClass (r : ℕ) : π_ 5 (Space (Fin (3 + r))) identity := ⟦stableInputCube r⟧

theorem stableInputClass_eq_pointed (r : ℕ) :
    stableInputClass r = pointedMap (stableSymmetricInput r) axis identity
      (stableSymmetricInput_axis r) parameterCubeClass :=
  (pointedMap_mk (stableSymmetricInput r) axis identity (stableSymmetricInput_axis r)
    parameterCube).symm

def stableSpecialInputClass (r : ℕ) : π_ 5 (SpecialSpace (Fin (3 + r))) specialIdentity :=
  pointedMap (stableSpecialInput r) axis specialIdentity
    (stableSpecialInput_axis r) parameterCubeClass

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
