import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFourGeneratorComparison

/-! # Fourth-degree generation after an actual based change of sphere coordinates -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

theorem nativeFourCube_generates_iff_of_homeomorph
    (F : SingleFamily 3 X x) (hp : ∀ t, F.map (t, point 3) = x)
    (e : Sphere 4 ≃ₜ Y) (y : Y) (he : e (latitudeBasepoint 3) = y)
    (f : C(Y, X)) (hf : f y = x)
    (hF : F.toSphereMap = f.comp (e : C(Sphere 4, Y)))
    (a : π_ 4 Y y) (ha : Function.Surjective (fun k : ℤ ↦ a ^ k)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f y x hf a) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let g := sphereFourGenerator (latitudeBasepoint 3)
  let E := pointedHomeomorphMulEquiv (N := Fin 4) e (latitudeBasepoint 3) y he
  let m := pointedMap (N := Fin 4) f y x hf
  have hE : Function.Surjective (fun k : ℤ ↦ (E g) ^ k) :=
    (CyclicGenerators.equiv_generates_iff E g).mpr
      (sphereFourGenerator_generates (latitudeBasepoint 3))
  have hmap : pointedMap (N := Fin 4) F.toSphereMap (latitudeBasepoint 3) x
      F.toSphereMap_latitudeBasepoint = m.comp E.toMonoidHom := by
    change pointedMap F.toSphereMap (latitudeBasepoint 3) x _ =
      (pointedMap f y x hf).comp (pointedMap (e : C(Sphere 4, Y)) (latitudeBasepoint 3) y he)
    rw [← pointedMap_comp]
    congr 1
  have hvalue : pointedMap F.toSphereMap (latitudeBasepoint 3) x
      F.toSphereMap_latitudeBasepoint g = m (E g) :=
    congrArg (fun h : π_ 4 (Sphere 4) (latitudeBasepoint 3) →* π_ 4 X x ↦ h g) hmap
  have hn := nativeFourCube_generates_iff F hp
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 3) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
      at hn
  rw [hvalue] at hn
  exact (CyclicGenerators.map_generates_iff m a ha).trans
    ((CyclicGenerators.map_generates_iff m (E g) hE).symm.trans hn)

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
