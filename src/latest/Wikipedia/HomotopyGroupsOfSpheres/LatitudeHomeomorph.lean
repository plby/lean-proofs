import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

/-! # Actual latitude homeomorphisms induced by parameter homeomorphisms -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

open Wikipedia.HopfProblem.SphereHomology

def latitudeMap (n : ℕ) (f : C(UnitSphere n, UnitSphere n)) :
    C(UnitSphere (n + 1), UnitSphere (n + 1)) :=
  sphereLift n ⟨fun p ↦ Latitude.point n p.1 (f p.2), by fun_prop⟩
    (fun x y ↦ Latitude.point_zero_eq n (f x) (f y))
    (fun x y ↦ Latitude.point_one_eq n (f x) (f y))

theorem latitudeMap_point (n : ℕ) (f : C(UnitSphere n, UnitSphere n)) (s : I) (z : UnitSphere n) :
    latitudeMap n f (Latitude.point n s z) = Latitude.point n s (f z) :=
  sphereLift_point n _ _ _ s z

def latitudeHomeomorph (n : ℕ) (e : UnitSphere n ≃ₜ UnitSphere n) :
    UnitSphere (n + 1) ≃ₜ UnitSphere (n + 1) where
  toFun := latitudeMap n (e : C(_, _))
  invFun := latitudeMap n (e.symm : C(_, _))
  left_inv w := by
    obtain ⟨⟨s, z⟩, rfl⟩ := Latitude.point_surjective n w
    rw [latitudeMap_point, latitudeMap_point]
    change Latitude.point n s (e.symm (e z)) = Latitude.point n s z
    rw [e.symm_apply_apply]
  right_inv w := by
    obtain ⟨⟨s, z⟩, rfl⟩ := Latitude.point_surjective n w
    rw [latitudeMap_point, latitudeMap_point]
    change Latitude.point n s (e (e.symm z)) = Latitude.point n s z
    rw [e.apply_symm_apply]
  continuous_toFun := (latitudeMap n _).continuous
  continuous_invFun := (latitudeMap n _).continuous

theorem latitudeHomeomorph_point (n : ℕ) (e : UnitSphere n ≃ₜ UnitSphere n)
    (s : I) (z : UnitSphere n) :
    latitudeHomeomorph n e (Latitude.point n s z) = Latitude.point n s (e z) :=
  latitudeMap_point n _ s z

def doubleHomeomorph (n : ℕ) (e : UnitSphere n ≃ₜ UnitSphere n) :
    UnitSphere (n + 2) ≃ₜ UnitSphere (n + 2) :=
  latitudeHomeomorph (n + 1) (latitudeHomeomorph n e)

theorem doubleHomeomorph_point (n : ℕ) (e : UnitSphere n ≃ₜ UnitSphere n)
    (s t : I) (z : UnitSphere n) :
    doubleHomeomorph n e (Latitude.point (n + 1) s (Latitude.point n t z)) =
      Latitude.point (n + 1) s (Latitude.point n t (e z)) := by
  rw [doubleHomeomorph, latitudeHomeomorph_point, latitudeHomeomorph_point]

namespace DoubleFamily

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

def postcompose {Y : Type*} [TopologicalSpace Y] {y : Y}
    (F : DoubleFamily n X x) (g : C(X, Y)) (hg : g x = y) : DoubleFamily n Y y where
  map := g.comp F.map
  outer_zero t z := (congrArg g (F.outer_zero t z)).trans hg
  outer_one t z := (congrArg g (F.outer_one t z)).trans hg
  inner_zero s z := (congrArg g (F.inner_zero s z)).trans hg
  inner_one s z := (congrArg g (F.inner_one s z)).trans hg

theorem postcompose_toSphereMap {Y : Type*} [TopologicalSpace Y] {y : Y}
    (F : DoubleFamily n X x) (g : C(X, Y)) (hg : g x = y) :
    (postcompose F g hg).toSphereMap = g.comp F.toSphereMap := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n v
  change (postcompose F g hg).toSphereMap (Latitude.point (n + 1) s (Latitude.point n t z)) =
    g (F.toSphereMap (Latitude.point (n + 1) s (Latitude.point n t z)))
  rw [toSphereMap_point, toSphereMap_point]
  rfl

def reparametrize (F : DoubleFamily n X x) (e : UnitSphere n ≃ₜ UnitSphere n) :
    DoubleFamily n X x where
  map := F.map.comp ⟨fun p ↦ (p.1, (p.2.1, e p.2.2)), by fun_prop⟩
  outer_zero t z := F.outer_zero t (e z)
  outer_one t z := F.outer_one t (e z)
  inner_zero s z := F.inner_zero s (e z)
  inner_one s z := F.inner_one s (e z)

theorem reparametrize_toSphereMap (F : DoubleFamily n X x) (e : UnitSphere n ≃ₜ UnitSphere n) :
    (reparametrize F e).toSphereMap = F.toSphereMap.comp (doubleHomeomorph n e : C(_, _)) := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective (n + 1) w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective n v
  change (reparametrize F e).toSphereMap (Latitude.point (n + 1) s (Latitude.point n t z)) =
    F.toSphereMap (doubleHomeomorph n e (Latitude.point (n + 1) s (Latitude.point n t z)))
  rw [doubleHomeomorph_point, toSphereMap_point, toSphereMap_point]
  rfl

end DoubleFamily

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
