import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFamily
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator

/-! # The actual single-latitude comparison with the cube-boundary quotient -/

noncomputable section

open scoped Topology unitInterval
open Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable (n : ℕ)

def join (t : I) (u : Fin n → I) : Fin (n + 1) → I := Fin.cons t u

theorem join_tail (u : Fin (n + 1) → I) : join n (u 0) (Fin.tail u) = u :=
  Fin.cons_self_tail u

theorem join_boundary (t : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
    join n t u ∈ Cube.boundary (Fin (n + 1)) := by
  rcases hu with ⟨i, hi⟩
  exact ⟨i.succ, hi⟩

def parameterQuotient : C(I × (Fin n → I), I × Sphere n) :=
  (ContinuousMap.id I).prodMap (quotient n)

theorem parameterQuotient_surjective (hn : 0 < n) :
    Function.Surjective (parameterQuotient n) := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, u), rfl⟩

theorem parameterQuotient_isQuotientMap (hn : 0 < n) :
    IsQuotientMap (parameterQuotient n) :=
  .of_surjective_continuous (parameterQuotient_surjective n hn)
    (parameterQuotient n).continuous

def cubeOutput : C(I × (Fin n → I), Sphere (n + 1)) :=
  (quotient (n + 1)).comp ⟨fun p ↦ join n p.1 p.2, by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd⟩

theorem cubeOutput_constant_on_fibers (p q : I × (Fin n → I))
    (h : parameterQuotient n p = parameterQuotient n q) : cubeOutput n p = cubeOutput n q := by
  rcases p with ⟨t, u⟩
  rcases q with ⟨s, v⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have hu : quotient n u = quotient n v := congrArg Prod.snd h
  rcases (quotient_eq_iff n u v).mp hu with rfl | ⟨hu, hv⟩
  · rfl
  · exact (quotient_boundary (n + 1) _ (join_boundary n _ _ hu)).trans
      (quotient_boundary (n + 1) _ (join_boundary n _ _ hv)).symm

def parameterLift (hn : 0 < n) : C(I × Sphere n, Sphere (n + 1)) :=
  (parameterQuotient_isQuotientMap n hn).lift (cubeOutput n)
    (cubeOutput_constant_on_fibers n)

theorem parameterLift_quotient (hn : 0 < n) (t : I) (u : Fin n → I) :
    parameterLift n hn (t, quotient n u) = quotient (n + 1) (join n t u) :=
  ContinuousMap.congr_fun ((parameterQuotient_isQuotientMap n hn).lift_comp (cubeOutput n)
    (cubeOutput_constant_on_fibers n)) (t, u)

def family (hn : 0 < n) :
    LatitudeDescent.SingleFamily n (Sphere (n + 1)) (point (n + 1)) where
  map := parameterLift n hn
  zero z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn 0 u).trans
      (quotient_boundary (n + 1) _ ⟨0, Or.inl rfl⟩)
  one z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn 1 u).trans
      (quotient_boundary (n + 1) _ ⟨0, Or.inr rfl⟩)

def collapse (hn : 0 < n) : C(Sphere (n + 1), Sphere (n + 1)) :=
  (family n hn).toSphereMap

theorem collapse_point (hn : 0 < n) (t : I) (u : Fin n → I) :
    collapse n hn (Latitude.point n t (quotient n u)) = quotient (n + 1) (join n t u) := by
  rw [collapse, LatitudeDescent.SingleFamily.toSphereMap_point]
  exact parameterLift_quotient n hn t u

theorem collapse_parameter_point (hn : 0 < n) (t : I) :
    collapse n hn (Latitude.point n t (point n)) = point (n + 1) := by
  rw [← quotient_boundary n 0 (zero_boundary hn), collapse_point]
  exact quotient_boundary (n + 1) _ (join_boundary n t 0 (zero_boundary hn))

theorem collapse_surjective (hn : 0 < n) : Function.Surjective (collapse n hn) := by
  intro z
  obtain ⟨u, rfl⟩ := quotient_surjective (Nat.zero_lt_succ n) z
  refine ⟨Latitude.point n (u 0) (quotient n (Fin.tail u)), ?_⟩
  rw [collapse_point]
  congr 1
  exact join_tail n u

theorem collapse_injective_off_point (hn : 0 < n) (w v : Sphere (n + 1))
    (hw : collapse n hn w ≠ point (n + 1)) (h : collapse n hn w = collapse n hn v) : w = v := by
  obtain ⟨⟨t, a⟩, rfl⟩ := Latitude.point_surjective n w
  obtain ⟨u, rfl⟩ := quotient_surjective hn a
  obtain ⟨⟨t', a'⟩, rfl⟩ := Latitude.point_surjective n v
  obtain ⟨u', rfl⟩ := quotient_surjective hn a'
  rw [collapse_point, collapse_point] at h
  rw [collapse_point] at hw
  rcases (quotient_eq_iff (n + 1) _ _).mp h with h | ⟨hu, _⟩
  · have ht : t = t' := congrFun h 0
    have hu : u = u' := funext (fun i ↦ congrFun h i.succ)
    subst t'
    subst u'
    rfl
  · exact (hw (quotient_boundary (n + 1) _ hu)).elim

theorem collapse_isQuotientMap (hn : 0 < n) : IsQuotientMap (collapse n hn) :=
  .of_surjective_continuous (collapse_surjective n hn) (collapse n hn).continuous

end Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse
