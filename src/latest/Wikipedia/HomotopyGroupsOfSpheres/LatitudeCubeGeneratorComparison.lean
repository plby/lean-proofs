import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeFactorization
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapseHomology
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeLowGenerators
import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenMapGenerators

/-!
# The global double-latitude class generates exactly when its native cube does

This uses the proved degree of the actual comparison map, not an assumed
agreement between the two different boundary quotients.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X : Type} [TopologicalSpace X] {x : X}
variable (F : DoubleFamily 5 X x) (hp : ∀ s t, F.map (s, (t, point 5)) = x)

theorem nativeCube_generates_iff :
    Function.Surjective (fun k : ℤ ↦
      (pointedMap F.toSphereMap (latitudeBasepoint 5) x F.toSphereMap_latitudeBasepoint
        (sphereSevenGenerator (latitudeBasepoint 5))) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let d := pointedMap (N := Fin 7) (SphereCubeGenerator.descend (by decide) (nativeCube F hp))
    (point 7) x (SphereCubeGenerator.descend_point _ _)
  let c := pointedMap (N := Fin 7) (LatitudeCubeCollapse.collapse 5 (by decide))
    (latitudeBasepoint 5) (point 7) (collapse_latitudeBasepoint (by decide))
  let g := sphereSevenGenerator (latitudeBasepoint 5)
  have hc : Function.Surjective (fun k : ℤ ↦ (c g) ^ k) :=
    sphereSevenMap_generator_generates _ _ _ _ LatitudeCubeCollapse.collapse_five_degree_natAbs
  have hq : d (SphereCubeGenerator.quotientClass 7) = nativeClass F hp :=
    SphereCubeGenerator.descend_native_class (nativeCube F hp)
  have hf : pointedMap F.toSphereMap (latitudeBasepoint 5) x F.toSphereMap_latitudeBasepoint g =
      d (c g) :=
    congrArg (fun h : π_ 7 (Sphere 7) (latitudeBasepoint 5) →* π_ 7 X x ↦ h g)
      (nativeCube_pointed_factorization F hp (by decide))
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 5) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
  rw [hf, ← hq]
  exact (CyclicGenerators.map_generates_iff d (c g) hc).trans
    (CyclicGenerators.map_generates_iff d (SphereCubeGenerator.quotientClass 7)
      SphereCubeGenerator.quotientClass_seven_generates).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily
