import Wikipedia.HopfProblem.SphereHomologySuspension

/-! # Continuous descent from latitude cylinders to the actual Euclidean spheres -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.CuspCentralHomology

variable {X : Type*} [TopologicalSpace X]

def suspensionLift (n : ℕ) (f : C(I × UnitSphere n, X))
    (h0 : ∀ x y, f (0, x) = f (0, y)) (h1 : ∀ x y, f (1, x) = f (1, y)) :
    C(Suspension (UnitSphere n), X) where
  toFun := Quotient.lift f (by
    rintro ⟨s, x⟩ ⟨t, y⟩ h
    change s = t ∧ (s = 0 ∨ s = 1 ∨ x = y) at h
    rcases h with ⟨rfl, h | h | h⟩
    · subst s
      exact h0 x y
    · subst s
      exact h1 x y
    · subst y
      rfl)
  continuous_toFun := Suspension.isQuotientMap_mk.continuous_iff.mpr f.continuous

def sphereLift (n : ℕ) (f : C(I × UnitSphere n, X))
    (h0 : ∀ x y, f (0, x) = f (0, y)) (h1 : ∀ x y, f (1, x) = f (1, y)) :
    C(UnitSphere (n + 1), X) :=
  (suspensionLift n f h0 h1).comp ((suspensionSphereHomeomorph n).symm : C(_, _))

theorem sphereLift_point (n : ℕ) (f : C(I × UnitSphere n, X))
    (h0 : ∀ x y, f (0, x) = f (0, y)) (h1 : ∀ x y, f (1, x) = f (1, y))
    (t : I) (z : UnitSphere n) :
    sphereLift n f h0 h1 (Latitude.point n t z) = f (t, z) := by
  change suspensionLift n f h0 h1 ((suspensionSphereHomeomorph n).symm
    (Latitude.point n t z)) = _
  rw [← suspensionSphereHomeomorph_mk, Homeomorph.symm_apply_apply]
  rfl

/-- A continuous two-parameter family whose four outside faces have the same value. -/
structure DoubleFamily (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  map : C(I × (I × UnitSphere n), X)
  outer_zero : ∀ t z, map (0, (t, z)) = x
  outer_one : ∀ t z, map (1, (t, z)) = x
  inner_zero : ∀ s z, map (s, (0, z)) = x
  inner_one : ∀ s z, map (s, (1, z)) = x

namespace DoubleFamily

variable {n : ℕ} {x : X} (F : DoubleFamily n X x)

def innerFunction : C(I × UnitSphere n, C(I, X)) :=
  (F.map.comp ⟨fun p : (I × UnitSphere n) × I ↦ (p.2, p.1),
    continuous_snd.prodMk continuous_fst⟩).curry

theorem innerFunction_zero (z w : UnitSphere n) :
    F.innerFunction (0, z) = F.innerFunction (0, w) := by
  apply ContinuousMap.ext
  intro s
  exact (F.inner_zero s z).trans (F.inner_zero s w).symm

theorem innerFunction_one (z w : UnitSphere n) :
    F.innerFunction (1, z) = F.innerFunction (1, w) := by
  apply ContinuousMap.ext
  intro s
  exact (F.inner_one s z).trans (F.inner_one s w).symm

def outerFamily : C(I × UnitSphere (n + 1), X) :=
  (sphereLift n F.innerFunction F.innerFunction_zero F.innerFunction_one).uncurry.comp
    ⟨fun p : I × UnitSphere (n + 1) ↦ (p.2, p.1), continuous_snd.prodMk continuous_fst⟩

theorem outerFamily_point (s t : I) (z : UnitSphere n) :
    F.outerFamily (s, Latitude.point n t z) = F.map (s, (t, z)) := by
  change sphereLift n F.innerFunction F.innerFunction_zero F.innerFunction_one
    (Latitude.point n t z) s = _
  rw [sphereLift_point]
  rfl

theorem outerFamily_zero (z : UnitSphere (n + 1)) : F.outerFamily (0, z) = x := by
  obtain ⟨⟨t, w⟩, rfl⟩ := Latitude.point_surjective n z
  rw [F.outerFamily_point, F.outer_zero]

theorem outerFamily_one (z : UnitSphere (n + 1)) : F.outerFamily (1, z) = x := by
  obtain ⟨⟨t, w⟩, rfl⟩ := Latitude.point_surjective n z
  rw [F.outerFamily_point, F.outer_one]

def toSphereMap : C(UnitSphere (n + 2), X) :=
  sphereLift (n + 1) F.outerFamily
    (fun z w ↦ (F.outerFamily_zero z).trans (F.outerFamily_zero w).symm)
    (fun z w ↦ (F.outerFamily_one z).trans (F.outerFamily_one w).symm)

theorem toSphereMap_point (s t : I) (z : UnitSphere n) :
    F.toSphereMap (Latitude.point (n + 1) s (Latitude.point n t z)) = F.map (s, (t, z)) := by
  rw [toSphereMap, sphereLift_point, F.outerFamily_point]

end DoubleFamily

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
