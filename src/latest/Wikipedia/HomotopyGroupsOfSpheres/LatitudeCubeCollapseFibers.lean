import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse

/-! # The latitude comparison has single-point fibers away from the collapsed value -/

noncomputable section

open scoped unitInterval
open Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable (n : ℕ) (hn : 0 < n)

theorem collapse_injective_off_point (w v : Sphere (n + 2))
    (hw : collapse n hn w ≠ point (n + 2)) (h : collapse n hn w = collapse n hn v) : w = v := by
  obtain ⟨⟨s, a⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
  obtain ⟨⟨t, b⟩, rfl⟩ := Latitude.point_surjective n a
  obtain ⟨u, rfl⟩ := quotient_surjective hn b
  obtain ⟨⟨s', a'⟩, rfl⟩ := Latitude.point_surjective (n + 1) v
  obtain ⟨⟨t', b'⟩, rfl⟩ := Latitude.point_surjective n a'
  obtain ⟨u', rfl⟩ := quotient_surjective hn b'
  rw [collapse_point, collapse_point] at h
  rw [collapse_point] at hw
  rcases (quotient_eq_iff (n + 2) _ _).mp h with h | ⟨hu, _⟩
  · have hs : s = s' := congrFun h 0
    have ht : t = t' := congrFun h 1
    have hu : u = u' := funext (fun i ↦ congrFun h i.succ.succ)
    subst s'
    subst t'
    subst u'
    rfl
  · exact (hw (quotient_boundary (n + 2) _ hu)).elim

theorem collapse_isQuotientMap : IsQuotientMap (collapse n hn) :=
  .of_surjective_continuous (collapse_surjective n hn) (collapse n hn).continuous

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse
