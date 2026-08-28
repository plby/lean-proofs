import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator

/-!
# The actual comparison from double latitude to the cube-boundary quotient

The map collapses the latitude ends and the double latitude of the parameter
base point. Its formula is the original quotient of the full cube. No degree
or generator property is assumed for this comparison.
-/

noncomputable section

open scoped Topology unitInterval
open Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable (n : ℕ)

def join (s t : I) (u : Fin n → I) : Fin (n + 2) → I :=
  Fin.cons s (Fin.cons t u)

theorem join_tail (u : Fin (n + 2) → I) :
    join n (u 0) (u 1) (Fin.tail (Fin.tail u)) = u := by
  change Fin.cons (u 0) (Fin.cons ((Fin.tail u) 0) (Fin.tail (Fin.tail u))) = u
  rw [Fin.cons_self_tail, Fin.cons_self_tail]

theorem join_boundary (s t : I) (u : Fin n → I)
    (hu : u ∈ Cube.boundary (Fin n)) : join n s t u ∈ Cube.boundary (Fin (n + 2)) := by
  rcases hu with ⟨i, hi⟩
  exact ⟨i.succ.succ, hi⟩

def parameterQuotient : C((I × I) × (Fin n → I), (I × I) × Sphere n) :=
  (ContinuousMap.id (I × I)).prodMap (quotient n)

theorem parameterQuotient_surjective (hn : 0 < n) :
    Function.Surjective (parameterQuotient n) := by
  rintro ⟨p, z⟩
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  exact ⟨(p, u), rfl⟩

theorem parameterQuotient_isQuotientMap (hn : 0 < n) :
    IsQuotientMap (parameterQuotient n) :=
  .of_surjective_continuous (parameterQuotient_surjective n hn)
    (parameterQuotient n).continuous

def cubeOutput : C((I × I) × (Fin n → I), Sphere (n + 2)) :=
  (quotient (n + 2)).comp ⟨fun p ↦ join n p.1.1 p.1.2 p.2, by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_fst.fst
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · exact continuous_fst.snd
      · exact (continuous_apply k).comp continuous_snd⟩

theorem cubeOutput_constant_on_fibers
    (p q : (I × I) × (Fin n → I)) (h : parameterQuotient n p = parameterQuotient n q) :
    cubeOutput n p = cubeOutput n q := by
  rcases p with ⟨p, u⟩
  rcases q with ⟨q, v⟩
  have hp : p = q := congrArg Prod.fst h
  subst q
  have hu : quotient n u = quotient n v := congrArg Prod.snd h
  rcases (quotient_eq_iff n u v).mp hu with rfl | ⟨hu, hv⟩
  · rfl
  · exact (quotient_boundary (n + 2) _ (join_boundary n _ _ _ hu)).trans
      (quotient_boundary (n + 2) _ (join_boundary n _ _ _ hv)).symm

def parameterLift (hn : 0 < n) : C((I × I) × Sphere n, Sphere (n + 2)) :=
  (parameterQuotient_isQuotientMap n hn).lift (cubeOutput n)
    (cubeOutput_constant_on_fibers n)

theorem parameterLift_quotient (hn : 0 < n) (s t : I) (u : Fin n → I) :
    parameterLift n hn ((s, t), quotient n u) = quotient (n + 2) (join n s t u) :=
  ContinuousMap.congr_fun ((parameterQuotient_isQuotientMap n hn).lift_comp (cubeOutput n)
    (cubeOutput_constant_on_fibers n)) ((s, t), u)

def family (hn : 0 < n) : LatitudeDescent.DoubleFamily n (Sphere (n + 2)) (point (n + 2)) where
  map := (parameterLift n hn).comp
    ⟨fun p : I × (I × Sphere n) ↦ ((p.1, p.2.1), p.2.2), by fun_prop⟩
  outer_zero t z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn 0 t u).trans
      (quotient_boundary (n + 2) _ ⟨0, Or.inl rfl⟩)
  outer_one t z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn 1 t u).trans
      (quotient_boundary (n + 2) _ ⟨0, Or.inr rfl⟩)
  inner_zero s z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn s 0 u).trans
      (quotient_boundary (n + 2) _ ⟨1, Or.inl rfl⟩)
  inner_one s z := by
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (parameterLift_quotient n hn s 1 u).trans
      (quotient_boundary (n + 2) _ ⟨1, Or.inr rfl⟩)

def collapse (hn : 0 < n) : C(Sphere (n + 2), Sphere (n + 2)) :=
  (family n hn).toSphereMap

theorem collapse_point (hn : 0 < n) (s t : I) (u : Fin n → I) :
    collapse n hn (Latitude.point (n + 1) s (Latitude.point n t (quotient n u))) =
      quotient (n + 2) (join n s t u) := by
  rw [collapse, LatitudeDescent.DoubleFamily.toSphereMap_point]
  exact parameterLift_quotient n hn s t u

theorem collapse_parameter_point (hn : 0 < n) (s t : I) :
    collapse n hn (Latitude.point (n + 1) s (Latitude.point n t (point n))) = point (n + 2) := by
  rw [← quotient_boundary n 0 (zero_boundary hn), collapse_point]
  exact quotient_boundary (n + 2) _ (join_boundary n s t 0 (zero_boundary hn))

theorem collapse_surjective (hn : 0 < n) : Function.Surjective (collapse n hn) := by
  intro z
  obtain ⟨u, rfl⟩ := quotient_surjective (Nat.zero_lt_succ (n + 1)) z
  refine ⟨Latitude.point (n + 1) (u 0) (Latitude.point n (u 1)
    (quotient n (Fin.tail (Fin.tail u)))), ?_⟩
  rw [collapse_point]
  congr 1
  exact join_tail n u

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapse
