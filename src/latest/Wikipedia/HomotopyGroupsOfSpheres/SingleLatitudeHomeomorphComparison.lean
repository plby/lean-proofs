import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeGeneratorComparison

/-! # Generation comparison after an actual based change of sphere coordinates -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

theorem nativeCube_generates_iff_of_homeomorph
    (F : SingleFamily 4 X x) (hp : ∀ t, F.map (t, point 4) = x)
    (e : Sphere 5 ≃ₜ Y) (y : Y) (he : e (latitudeBasepoint 4) = y)
    (f : C(Y, X)) (hf : f y = x)
    (hF : F.toSphereMap = f.comp (e : C(Sphere 5, Y)))
    (a : π_ 5 Y y) (ha : Function.Surjective (fun k : ℤ ↦ a ^ k)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f y x hf a) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ nativeClass F hp ^ k) := by
  let g := sphereFiveGenerator (latitudeBasepoint 4)
  let E := pointedHomeomorphMulEquiv (N := Fin 5) e (latitudeBasepoint 4) y he
  let m := pointedMap (N := Fin 5) f y x hf
  have hE : Function.Surjective (fun k : ℤ ↦ (E g) ^ k) :=
    (CyclicGenerators.equiv_generates_iff E g).mpr
      (sphereFiveGenerator_generates (latitudeBasepoint 4))
  have hmap : pointedMap (N := Fin 5) F.toSphereMap (latitudeBasepoint 4) x
      F.toSphereMap_latitudeBasepoint = m.comp E.toMonoidHom := by
    change pointedMap F.toSphereMap (latitudeBasepoint 4) x _ =
      (pointedMap f y x hf).comp (pointedMap (e : C(Sphere 5, Y)) (latitudeBasepoint 4) y he)
    rw [← pointedMap_comp]
    congr 1
  have hvalue : pointedMap F.toSphereMap (latitudeBasepoint 4) x
      F.toSphereMap_latitudeBasepoint g = m (E g) :=
    congrArg (fun h : π_ 5 (Sphere 5) (latitudeBasepoint 4) →* π_ 5 X x ↦ h g) hmap
  have hn := nativeCube_generates_iff F hp
  change Function.Surjective (fun k : ℤ ↦
    (pointedMap F.toSphereMap (latitudeBasepoint 4) x F.toSphereMap_latitudeBasepoint g) ^ k) ↔ _
      at hn
  rw [hvalue] at hn
  exact (CyclicGenerators.map_generates_iff m a ha).trans
    ((CyclicGenerators.map_generates_iff m (E g) hE).symm.trans hn)

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
