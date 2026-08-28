import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfBlock
import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # An actual generating three-cube based at the Clifford equatorial pole -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open SphereCubeGenerator

local notation "Ambient" => EuclideanSpace ℝ (Fin 4)

def parameterThreeBasepointIsometry : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ ((point 3).val - equatorPole.val))ᗮ.reflection

theorem parameterThreeBasepointIsometry_apply :
    parameterThreeBasepointIsometry (point 3).val = equatorPole.val := by
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp (point 3).property,
    mem_sphere_zero_iff_norm.mp equatorPole.property]

def basedSphereThreeHomeomorph : Sphere 3 ≃ₜ EquatorSphere :=
  SphereCenteredCoordinates.sphereIsometry parameterThreeBasepointIsometry

theorem basedSphereThreeHomeomorph_point : basedSphereThreeHomeomorph (point 3) = equatorPole :=
  Subtype.ext parameterThreeBasepointIsometry_apply

def parameterThreeCube : GenLoop (Fin 3) EquatorSphere equatorPole :=
  pointedMapGenLoop (basedSphereThreeHomeomorph : C(Sphere 3, EquatorSphere)) (point 3) equatorPole
    basedSphereThreeHomeomorph_point (quotientCube 3)

def parameterThreeClass : π_ 3 EquatorSphere equatorPole := ⟦parameterThreeCube⟧

theorem parameterThreeCube_apply (t : Fin 3 → I) :
    parameterThreeCube t = basedSphereThreeHomeomorph (quotient 3 t) := rfl

theorem parameterThreeClass_generates :
    Function.Surjective (fun k : ℤ ↦ parameterThreeClass ^ k) :=
  PointedCubeGenerators.homeomorph_cube_generates basedSphereThreeHomeomorph (point 3) equatorPole
    basedSphereThreeHomeomorph_point (quotientCube 3)
    (quotientClass_generates (pi3_sphere_three_mulEquiv (point 3)))

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
