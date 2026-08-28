import Wikipedia.SmoothSixDPoincare.DoubleSphere

/-!
# Gluing two actual disk maps into a literal standard sphere map

The maps agree on the exact unit boundary. The quotient construction and
the existing sphere homeomorphism retain both hemispherical point formulas
and the exact image. No smoothness across the equator is asserted.
-/

noncomputable section

open Set Function Metric ContinuousMap
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereDiskGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  (A B : C(Hemisphere.Ball n, M))
  (h : ∀ z : DiskDouble.Boundary (Hemisphere.Ambient n),
    A (DiskDouble.boundary _ z) = B (DiskDouble.boundary _ z))

include h in
theorem respects (x y : Hemisphere.Ball n ⊕ Hemisphere.Ball n)
    (hxy : DiskDouble.Rel (Homeomorph.refl (DiskDouble.Boundary (Hemisphere.Ambient n))) x y) :
    Sum.elim A B x = Sum.elim A B y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hxy.elim
    | inr y =>
      obtain ⟨z, rfl, rfl⟩ := hxy
      exact h z
  | inr x => cases y <;> exact hxy.elim

def doubleMap : C(DiskDouble.Space
    (Homeomorph.refl (DiskDouble.Boundary (Hemisphere.Ambient n))), M) :=
  ⟨Quot.lift (Sum.elim A B) (respects A B h),
    continuous_quot_lift (respects A B h)
      (continuous_sum_dom.mpr ⟨A.continuous, B.continuous⟩)⟩

def map : C(Hemisphere.Sphere n, M) :=
  (doubleMap A B h).comp
    ⟨(DiskDouble.homeomorphSphere n).symm, (DiskDouble.homeomorphSphere n).symm.continuous⟩

theorem map_false (u : Hemisphere.Ball n) :
    map A B h (Hemisphere.point false u) = A u := by
  have he : DiskDouble.homeomorphSphere n (Quot.mk _ (.inl u)) =
      Hemisphere.point false u := rfl
  change doubleMap A B h ((DiskDouble.homeomorphSphere n).symm
    (Hemisphere.point false u)) = A u
  rw [← he, Homeomorph.symm_apply_apply]
  rfl

theorem map_true (u : Hemisphere.Ball n) :
    map A B h (Hemisphere.point true u) = B u := by
  have he : DiskDouble.homeomorphSphere n (Quot.mk _ (.inr u)) =
      Hemisphere.point true u := rfl
  change doubleMap A B h ((DiskDouble.homeomorphSphere n).symm
    (Hemisphere.point true u)) = B u
  rw [← he, Homeomorph.symm_apply_apply]
  rfl

theorem range_map : range (map A B h) = range A ∪ range B := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨b, u, rfl⟩ := Hemisphere.point_jointly_surjective z
    cases b
    · exact Or.inl ⟨u, (map_false A B h u).symm⟩
    · exact Or.inr ⟨u, (map_true A B h u).symm⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact ⟨Hemisphere.point false u, map_false A B h u⟩
    · exact ⟨Hemisphere.point true u, map_true A B h u⟩

theorem map_of_nonpos (x : Hemisphere.Sphere n)
    (hx : (x : Hemisphere.Ambient (n + 1)) 0 ≤ 0) :
    map A B h x = A (Hemisphere.disk x) := by
  exact (congrArg (map A B h) (Hemisphere.point_disk_of_nonpos x hx).symm).trans
    (map_false A B h (Hemisphere.disk x))

theorem map_of_nonneg (x : Hemisphere.Sphere n)
    (hx : 0 ≤ (x : Hemisphere.Ambient (n + 1)) 0) :
    map A B h x = B (Hemisphere.disk x) := by
  exact (congrArg (map A B h) (Hemisphere.point_disk_of_nonneg x hx).symm).trans
    (map_true A B h (Hemisphere.disk x))

end Wikipedia.HopfProblem.DegreeCollapse.SphereDiskGluing
