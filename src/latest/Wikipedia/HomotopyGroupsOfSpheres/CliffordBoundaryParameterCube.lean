import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryComplexStructure
import Wikipedia.HomotopyGroupsOfSpheres.SphereTwo
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # A generating two-cube at the explicit complex-structure parameter pole -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube SphereCubeGenerator

def parameterBasepointIsometry : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ℝ ∙ ((point 2).val - structurePole.val))ᗮ.reflection

theorem parameterBasepointIsometry_apply :
    parameterBasepointIsometry (point 2).val = structurePole.val := by
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp (point 2).property,
    mem_sphere_zero_iff_norm.mp structurePole.property]

def parameterHomeomorph : Sphere 2 ≃ₜ Sphere 2 :=
  SphereCenteredCoordinates.sphereIsometry parameterBasepointIsometry

theorem parameterHomeomorph_point : parameterHomeomorph (point 2) = structurePole :=
  Subtype.ext parameterBasepointIsometry_apply

def parameterCube : GenLoop (Fin 2) (Sphere 2) structurePole :=
  pointedMapGenLoop (parameterHomeomorph : C(Sphere 2, Sphere 2)) (point 2) structurePole
    parameterHomeomorph_point (quotientCube 2)

def parameterClass : π_ 2 (Sphere 2) structurePole := ⟦parameterCube⟧

theorem parameterCube_apply (t : Fin 2 → I) :
    parameterCube t = parameterHomeomorph (quotient 2 t) := rfl

theorem parameterClass_generates :
    Function.Surjective (fun k : ℤ ↦ parameterClass ^ k) :=
  PointedCubeGenerators.homeomorph_cube_generates parameterHomeomorph (point 2) structurePole
    parameterHomeomorph_point (quotientCube 2)
    (quotientClass_generates (pi2_sphere_two_mulEquiv (point 2)))

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
