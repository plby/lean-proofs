import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies

/-! # Exact factorization of a single-latitude family through its native cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
variable (F : SingleFamily n X x) (hp : ∀ t, F.map (t, point n) = x)

def nativeCube : GenLoop (Fin (n + 1)) X x where
  val := F.map.comp ⟨fun u ↦ (u 0, quotient n (Fin.tail u)), by
    apply Continuous.prodMk (continuous_apply 0)
    exact (quotient n).continuous.comp
      (continuous_pi (fun i ↦ continuous_apply i.succ))⟩
  property u hu := by
    rcases hu with ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rintro (h | h)
      · change F.map (u 0, quotient n (Fin.tail u)) = x
        rw [h, F.zero]
      · change F.map (u 0, quotient n (Fin.tail u)) = x
        rw [h, F.one]
    · intro h
      change F.map (u 0, quotient n (Fin.tail u)) = x
      rw [quotient_boundary n _ ⟨j, h⟩]
      exact hp (u 0)

theorem nativeCube_join (t : I) (u : Fin n → I) :
    nativeCube F hp (SingleLatitudeCollapse.join n t u) = F.map (t, quotient n u) := rfl

def nativeClass : π_ (n + 1) X x := ⟦nativeCube F hp⟧

theorem nativeCube_factorization (hn : 0 < n) :
    (SphereCubeGenerator.descend (Nat.zero_lt_succ n) (nativeCube F hp)).comp
      (SingleLatitudeCollapse.collapse n hn) = F.toSphereMap := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n w
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  change SphereCubeGenerator.descend (Nat.zero_lt_succ n) (nativeCube F hp)
    (SingleLatitudeCollapse.collapse n hn (Latitude.point n t (quotient n u))) = _
  rw [SingleLatitudeCollapse.collapse_point, SphereCubeGenerator.descend_quotient,
    nativeCube_join, toSphereMap_point]

def latitudeBasepoint (n : ℕ) : Sphere (n + 1) := Latitude.point n 0 (point n)

theorem collapse_latitudeBasepoint (hn : 0 < n) :
    SingleLatitudeCollapse.collapse n hn (latitudeBasepoint n) = point (n + 1) :=
  SingleLatitudeCollapse.collapse_parameter_point n hn 0

theorem toSphereMap_latitudeBasepoint : F.toSphereMap (latitudeBasepoint n) = x := by
  rw [latitudeBasepoint, toSphereMap_point, F.zero]

theorem nativeCube_pointed_factorization (hn : 0 < n) :
    pointedMap (N := Fin (n + 1)) F.toSphereMap (latitudeBasepoint n) x
      F.toSphereMap_latitudeBasepoint =
      (pointedMap (SphereCubeGenerator.descend (Nat.zero_lt_succ n) (nativeCube F hp))
        (point (n + 1)) x (SphereCubeGenerator.descend_point _ _)).comp
          (pointedMap (SingleLatitudeCollapse.collapse n hn) (latitudeBasepoint n)
            (point (n + 1)) (collapse_latitudeBasepoint hn)) := by
  rw [← pointedMap_comp]
  congr 1
  exact (nativeCube_factorization F hp hn).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.SingleFamily
