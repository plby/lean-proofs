import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeThreeGeneratorComparison

/-! # Third-degree generation after an actual based change of sphere coordinates -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

theorem nativeThreeCube_generates_iff_of_homeomorph
    (F : SingleFamily 2 X x) (hp : ∀ t, F.map (t, point 2) = x)
    (e : Sphere 3 ≃ₜ Y) (y : Y) (he : e (latitudeBasepoint 2) = y)
    (f : C(Y, X)) (hf : f y = x)
    (hF : F.toSphereMap = f.comp (e : C(Sphere 3, Y)))
    (a : π_ 3 Y y) (ha : Function.Surjective (fun k : ℤ ↦ a ^ k)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f y x hf a) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let g := sphereThreeGenerator (latitudeBasepoint 2)
  let E := pointedHomeomorphMulEquiv (N := Fin 3) e (latitudeBasepoint 2) y he
  let m := pointedMap (N := Fin 3) f y x hf
  have hE : Function.Surjective (fun k : ℤ ↦ (E g) ^ k) :=
    (CyclicGenerators.equiv_generates_iff E g).mpr
      (sphereThreeGenerator_generates (latitudeBasepoint 2))
  have hmap : pointedMap (N := Fin 3) F.toSphereMap (latitudeBasepoint 2) x
      F.toSphereMap_latitudeBasepoint = m.comp E.toMonoidHom := by
    change pointedMap F.toSphereMap (latitudeBasepoint 2) x _ =
      (pointedMap f y x hf).comp (pointedMap (e : C(Sphere 3, Y)) (latitudeBasepoint 2) y he)
    rw [← pointedMap_comp]
    congr 1
  have hvalue : pointedMap F.toSphereMap (latitudeBasepoint 2) x
      F.toSphereMap_latitudeBasepoint g = m (E g) :=
    congrArg (fun h : π_ 3 (Sphere 3) (latitudeBasepoint 2) →* π_ 3 X x ↦ h g) hmap
  have hn := nativeThreeCube_generates_iff F hp
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 2) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
      at hn
  rw [hvalue] at hn
  exact (CyclicGenerators.map_generates_iff m a ha).trans
    ((CyclicGenerators.map_generates_iff m (E g) hE).symm.trans hn)

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
