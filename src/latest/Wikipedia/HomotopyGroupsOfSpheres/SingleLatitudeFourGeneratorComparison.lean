import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapseHomology
import Wikipedia.HomotopyGroupsOfSpheres.SphereFourHomologyGenerators

/-! # The fourth-degree single-latitude generator comparison -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X : Type} [TopologicalSpace X] {x : X}
variable (F : SingleFamily 3 X x) (hp : ∀ t, F.map (t, point 3) = x)

theorem nativeFourCube_generates_iff :
    Function.Surjective (fun k : ℤ ↦
      (pointedMap F.toSphereMap (latitudeBasepoint 3) x F.toSphereMap_latitudeBasepoint
        (sphereFourGenerator (latitudeBasepoint 3))) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let d := pointedMap (N := Fin 4) (SphereCubeGenerator.descend (by decide) (nativeCube F hp))
    (point 4) x (SphereCubeGenerator.descend_point _ _)
  let c := pointedMap (N := Fin 4) (SingleLatitudeCollapse.collapse 3 (by decide))
    (latitudeBasepoint 3) (point 4) (collapse_latitudeBasepoint (by decide))
  let g := sphereFourGenerator (latitudeBasepoint 3)
  have hc : Function.Surjective (fun k : ℤ ↦ (c g) ^ k) :=
    sphereFourMap_generator_generates_of_homology _ _ _ _
      (SingleLatitudeCollapse.collapse_homology_bijective 3 (by decide) 2)
  have hq : d (SphereCubeGenerator.quotientClass 4) = nativeClass F hp :=
    SphereCubeGenerator.descend_native_class (nativeCube F hp)
  have hf : pointedMap F.toSphereMap (latitudeBasepoint 3) x F.toSphereMap_latitudeBasepoint g =
      d (c g) :=
    congrArg (fun h : π_ 4 (Sphere 4) (latitudeBasepoint 3) →* π_ 4 X x ↦ h g)
      (nativeCube_pointed_factorization F hp (by decide))
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 3) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
  rw [hf, ← hq]
  exact (CyclicGenerators.map_generates_iff d (c g) hc).trans
    (CyclicGenerators.map_generates_iff d (SphereCubeGenerator.quotientClass 4)
      (SphereCubeGenerator.quotientClass_generates (pi4_sphere_four_mulEquiv (point 4)))).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
