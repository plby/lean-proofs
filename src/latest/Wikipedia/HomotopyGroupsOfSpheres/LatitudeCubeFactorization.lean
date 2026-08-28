import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies

/-!
# Exact factorization of based double-latitude families through native cubes

The descended native cube composed with the actual latitude collapse is the
original sphere map. Thus the remaining comparison is the generator action
of a concrete sphere self-map, independent of the target family.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
variable (F : DoubleFamily n X x) (hp : ∀ s t, F.map (s, (t, point n)) = x)

def nativeCube : GenLoop (Fin (n + 2)) X x where
  val := F.map.comp ⟨fun u ↦ (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))), by
    apply Continuous.prodMk (continuous_apply 0)
    apply Continuous.prodMk (continuous_apply 1)
    exact (quotient n).continuous.comp
      (continuous_pi (fun i ↦ continuous_apply i.succ.succ))⟩
  property u hu := by
    rcases hu with ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rintro (h | h)
      · change F.map (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))) = x
        rw [h, F.outer_zero]
      · change F.map (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))) = x
        rw [h, F.outer_one]
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · rintro (h | h)
        · change F.map (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))) = x
          rw [show u 1 = 0 from h, F.inner_zero]
        · change F.map (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))) = x
          rw [show u 1 = 1 from h, F.inner_one]
      · intro h
        change F.map (u 0, (u 1, quotient n (Fin.tail (Fin.tail u)))) = x
        rw [quotient_boundary n _ ⟨k, h⟩]
        exact hp (u 0) (u 1)

theorem nativeCube_join (s t : I) (u : Fin n → I) :
    nativeCube F hp (LatitudeCubeCollapse.join n s t u) = F.map (s, (t, quotient n u)) := rfl

def nativeClass : π_ (n + 2) X x := ⟦nativeCube F hp⟧

theorem nativeCube_factorization (hn : 0 < n) :
    (SphereCubeGenerator.descend (Nat.zero_lt_succ (n + 1)) (nativeCube F hp)).comp
      (LatitudeCubeCollapse.collapse n hn) = F.toSphereMap := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n v
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  change SphereCubeGenerator.descend (Nat.zero_lt_succ (n + 1)) (nativeCube F hp)
    (LatitudeCubeCollapse.collapse n hn
      (Latitude.point (n + 1) s (Latitude.point n t (quotient n u)))) = _
  rw [LatitudeCubeCollapse.collapse_point, SphereCubeGenerator.descend_quotient,
    nativeCube_join, toSphereMap_point]

def latitudeBasepoint (n : ℕ) : Sphere (n + 2) :=
  Latitude.point (n + 1) 0 (Latitude.point n 0 (point n))

theorem collapse_latitudeBasepoint (hn : 0 < n) :
    LatitudeCubeCollapse.collapse n hn (latitudeBasepoint n) = point (n + 2) :=
  LatitudeCubeCollapse.collapse_parameter_point n hn 0 0

theorem toSphereMap_latitudeBasepoint : F.toSphereMap (latitudeBasepoint n) = x := by
  rw [latitudeBasepoint, toSphereMap_point, F.outer_zero]

theorem nativeCube_pointed_factorization (hn : 0 < n) :
    pointedMap (N := Fin (n + 2)) F.toSphereMap (latitudeBasepoint n) x
      F.toSphereMap_latitudeBasepoint =
      (pointedMap (SphereCubeGenerator.descend (Nat.zero_lt_succ (n + 1)) (nativeCube F hp))
        (point (n + 2)) x (SphereCubeGenerator.descend_point _ _)).comp
          (pointedMap (LatitudeCubeCollapse.collapse n hn) (latitudeBasepoint n)
            (point (n + 2)) (collapse_latitudeBasepoint hn)) := by
  rw [← pointedMap_comp]
  congr 1
  exact (nativeCube_factorization F hp hn).symm

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent.DoubleFamily
