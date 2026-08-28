import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapseHomology
import Wikipedia.HomotopyGroupsOfSpheres.SphereFiveHomologyGenerators
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeLowGenerators

/-!
# Generation by a single-latitude sphere family and its native cube
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X : Type} [TopologicalSpace X] {x : X}
variable (F : SingleFamily 4 X x) (hp : ∀ t, F.map (t, point 4) = x)

theorem nativeCube_generates_iff :
    Function.Surjective (fun k : ℤ ↦
      (pointedMap F.toSphereMap (latitudeBasepoint 4) x F.toSphereMap_latitudeBasepoint
        (sphereFiveGenerator (latitudeBasepoint 4))) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let d := pointedMap (N := Fin 5) (SphereCubeGenerator.descend (by decide) (nativeCube F hp))
    (point 5) x (SphereCubeGenerator.descend_point _ _)
  let c := pointedMap (N := Fin 5) (SingleLatitudeCollapse.collapse 4 (by decide))
    (latitudeBasepoint 4) (point 5) (collapse_latitudeBasepoint (by decide))
  let g := sphereFiveGenerator (latitudeBasepoint 4)
  have hc : Function.Surjective (fun k : ℤ ↦ (c g) ^ k) :=
    sphereFiveMap_generator_generates_of_homology _ _ _ _
      (SingleLatitudeCollapse.collapse_homology_bijective 4 (by decide) 3)
  have hq : d (SphereCubeGenerator.quotientClass 5) = nativeClass F hp :=
    SphereCubeGenerator.descend_native_class (nativeCube F hp)
  have hf : pointedMap F.toSphereMap (latitudeBasepoint 4) x F.toSphereMap_latitudeBasepoint g =
      d (c g) :=
    congrArg (fun h : π_ 5 (Sphere 5) (latitudeBasepoint 4) →* π_ 5 X x ↦ h g)
      (nativeCube_pointed_factorization F hp (by decide))
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 4) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
  rw [hf, ← hq]
  exact (CyclicGenerators.map_generates_iff d (c g) hc).trans
    (CyclicGenerators.map_generates_iff d (SphereCubeGenerator.quotientClass 5)
      SphereCubeGenerator.quotientClass_five_generates).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
