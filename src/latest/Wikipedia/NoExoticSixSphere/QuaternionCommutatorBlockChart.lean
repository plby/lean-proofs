import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeFiber
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The actual three-cube coordinates and centered quaternion charts

The transition is a genuine open partial homeomorphism from the open
three-cube to the imaginary quaternion tangent space, with full target.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionCommutatorBlockChart

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres
open SphereCenteredCoordinates QuaternionCommutatorSourceChart
open QuaternionCommutatorNativeSphere GLOrthonormalization

local notation "ℍ" => Quaternion ℝ

def coordinateIsometry : UnitSphere ℍ ≃ₜ Sphere 3 :=
  sphereIsometry Quaternion.linearIsometryEquivTuple

def centeredChart : OpenPartialHomeomorph (Sphere 3) Imaginary :=
  coordinateIsometry.symm.transOpenPartialHomeomorph (chart center)

theorem centeredChart_symm (v : Imaginary) :
    centeredChart.symm v = sphereHomeomorph (quaternionChart v) := rfl

theorem centeredChart_target : centeredChart.target = Set.univ := rfl

theorem centeredChart_source : centeredChart.source = {spherePole 3}ᶜ := by
  ext x
  change coordinateIsometry.symm x ≠ ⟨-center.val, _⟩ ↔ x ≠ spherePole 3
  have hp : coordinateIsometry (⟨-center.val, by simp [center]⟩ : UnitSphere ℍ) =
      spherePole 3 := by
    apply Subtype.ext
    change Quaternion.linearIsometryEquivTuple (-(-1 : ℍ)) = (spherePole 3).val
    rw [neg_neg]
    exact congrArg Subtype.val sphereHomeomorph_one
  constructor
  · intro h hx
    apply h
    apply coordinateIsometry.injective
    exact (coordinateIsometry.apply_symm_apply x).trans (hx.trans hp.symm)
  · intro h hx
    apply h
    exact (coordinateIsometry.apply_symm_apply x).symm.trans
      ((congrArg coordinateIsometry hx).trans hp)

def sphereInverse : OpenPartialHomeomorph (Vector 3) (Sphere 3) :=
  (SmoothCube.sphereChart 3).toOpenPartialHomeomorph.symm

theorem sphereInverse_target : sphereInverse.target = centeredChart.source := by
  rw [centeredChart_source]
  rfl

def blockChart : OpenPartialHomeomorph (Vector 3) Imaginary :=
  sphereInverse.trans' centeredChart sphereInverse_target

theorem blockChart_source : blockChart.source = SmoothCube.openCube 3 := rfl

theorem blockChart_target : blockChart.target = Set.univ := rfl

theorem blockChart_apply (x : Vector 3) :
    blockChart x = centeredChart ((SmoothCube.sphereChart 3).symm x) := rfl

theorem blockChart_symm (v : Imaginary) :
    blockChart.symm v = SmoothCube.sphereChart 3 (sphereHomeomorph (quaternionChart v)) := rfl

theorem quaternionCube_chart (u : Fin 3 → I) (hu : u ∉ Cube.boundary (Fin 3)) :
    quaternionChart (blockChart (SmoothCube.vectorOfCube 3 u)) = quaternionCube u := by
  have hx : SmoothCube.vectorOfCube 3 u ∈ sphereInverse.source :=
    (SmoothCube.vectorOfCube_mem_openCube 3 u).mpr hu
  have hs : sphereInverse (SmoothCube.vectorOfCube 3 u) ∈ centeredChart.source :=
    sphereInverse_target ▸ sphereInverse.map_source hx
  apply sphereHomeomorph.injective
  change centeredChart.symm (centeredChart (sphereInverse (SmoothCube.vectorOfCube 3 u))) =
    sphereHomeomorph (sphereHomeomorph.symm (SmoothCube.quotient 3 u))
  rw [Homeomorph.apply_symm_apply, centeredChart.left_inv hs]
  exact (SmoothCube.quotient_interior 3 ⟨u, hu⟩).symm

theorem quaternionChart_injective : Function.Injective quaternionChart := by
  intro v w h
  apply inverse_injective center
  apply Subtype.ext
  exact congrArg (fun q : UnitQuaternions ↦ q.val) h

theorem antipodalCube_not_boundary : antipodalCube ∉ Cube.boundary (Fin 3) := by
  intro h
  exact minusOne_ne_one (antipodalCube_value.symm.trans (quaternionCube.property _ h))

theorem blockChart_antipodalCube : blockChart (SmoothCube.vectorOfCube 3 antipodalCube) = 0 := by
  apply quaternionChart_injective
  exact (quaternionCube_chart antipodalCube antipodalCube_not_boundary).trans
    (antipodalCube_value.trans (Subtype.ext quaternionChart_zero).symm)

end NoExoticSixSphere.QuaternionCommutatorBlockChart
