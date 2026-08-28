import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapseHomology
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeHomologyGenerators

/-! # The third-degree single-latitude generator comparison -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X : Type} [TopologicalSpace X] {x : X}
variable (F : SingleFamily 2 X x) (hp : ∀ t, F.map (t, point 2) = x)

theorem nativeThreeCube_generates_iff :
    Function.Surjective (fun k : ℤ ↦
      (pointedMap F.toSphereMap (latitudeBasepoint 2) x F.toSphereMap_latitudeBasepoint
        (sphereThreeGenerator (latitudeBasepoint 2))) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let d := pointedMap (N := Fin 3) (SphereCubeGenerator.descend (by decide) (nativeCube F hp))
    (point 3) x (SphereCubeGenerator.descend_point _ _)
  let c := pointedMap (N := Fin 3) (SingleLatitudeCollapse.collapse 2 (by decide))
    (latitudeBasepoint 2) (point 3) (collapse_latitudeBasepoint (by decide))
  let g := sphereThreeGenerator (latitudeBasepoint 2)
  have hc : Function.Surjective (fun k : ℤ ↦ (c g) ^ k) :=
    sphereThreeMap_generator_generates_of_homology _ _ _ _
      (SingleLatitudeCollapse.collapse_homology_bijective 2 (by decide) 1)
  have hq : d (SphereCubeGenerator.quotientClass 3) = nativeClass F hp :=
    SphereCubeGenerator.descend_native_class (nativeCube F hp)
  have hf : pointedMap F.toSphereMap (latitudeBasepoint 2) x F.toSphereMap_latitudeBasepoint g =
      d (c g) :=
    congrArg (fun h : π_ 3 (Sphere 3) (latitudeBasepoint 2) →* π_ 3 X x ↦ h g)
      (nativeCube_pointed_factorization F hp (by decide))
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 2) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
  rw [hf, ← hq]
  exact (CyclicGenerators.map_generates_iff d (c g) hc).trans
    (CyclicGenerators.map_generates_iff d (SphereCubeGenerator.quotientClass 3)
      (SphereCubeGenerator.quotientClass_generates (pi3_sphere_three_mulEquiv (point 3)))).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
