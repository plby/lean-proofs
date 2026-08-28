import Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph

/-!
# Extend an actual cylinder homeomorphism through an inward collar

Fixing the inner end makes the map and its inverse glue with the identity
outside the open collar. The exact boundary map is retained, with no
smooth structure or unproved extension principle imposed on the body.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {i : C(X, Y)}
  (C : InwardBoundaryCollar i)

def region : Set Y := range C.map

def innerRegion : Set Y := C.map '' {q : X × unitInterval | q.2 < 1}

def fixedRegion : Set Y := C.innerRegionᶜ

theorem closed_region : IsClosed C.region := C.closedEmbedding.isClosed_range

theorem closed_fixedRegion : IsClosed C.fixedRegion := C.inner_open.isClosed_compl

theorem region_cover : C.region ∪ C.fixedRegion = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ C.innerRegion
  · obtain ⟨q, _, rfl⟩ := hy
    exact Or.inl ⟨q, rfl⟩
  · exact Or.inr hy

theorem map_mem_fixedRegion_iff (q : X × unitInterval) :
    C.map q ∈ C.fixedRegion ↔ q.2 = 1 := by
  constructor
  · intro hq
    have ht : ¬q.2 < 1 := fun h => hq ⟨q, h, rfl⟩
    apply Subtype.ext
    exact le_antisymm q.2.property.2 (le_of_not_gt ht)
  · intro hq
    rintro ⟨r, hr, he⟩
    have hrq : r = q := C.closedEmbedding.injective he
    subst r
    exact (ne_of_lt hr) hq

def coordinates : (X × unitInterval) ≃ₜ C.region := C.closedEmbedding.isEmbedding.toHomeomorph

variable (a : (X × unitInterval) ≃ₜ (X × unitInterval))
  (ha : ∀ x, a (x, 1) = (x, 1))

def regionChange : C.region ≃ₜ C.region := C.coordinates.symm.trans (a.trans C.coordinates)

include ha in
theorem regionChange_cross (z : C.region) (w : C.fixedRegion) :
    ((C.regionChange a z : C.region) : Y) = w.val ↔ z.val = w.val := by
  obtain ⟨q, rfl⟩ := C.coordinates.surjective z
  change C.map (a (C.coordinates.symm (C.coordinates q))) = w.val ↔ C.map q = w.val
  rw [C.coordinates.symm_apply_apply]
  constructor
  · intro h
    have ht : (a q).2 = 1 := (C.map_mem_fixedRegion_iff (a q)).mp (h.symm ▸ w.property)
    have hqq : a q = ((a q).1, 1) := by
      apply Prod.ext
      · rfl
      · exact ht
    have haa : a (a q) = a q := by
      rw [hqq]
      exact ha _
    have haq : a q = q := a.injective haa
    exact (congrArg C.map haq).symm.trans h
  · intro h
    have ht : q.2 = 1 := (C.map_mem_fixedRegion_iff q).mp (h.symm ▸ w.property)
    have hqq : q = (q.1, 1) := by
      apply Prod.ext
      · rfl
      · exact ht
    have haq : a q = q := by
      rw [hqq]
      exact ha _
    exact (congrArg C.map haq).trans h

def extension : Y ≃ₜ Y :=
  ClosedCover.homeomorph C.region_cover C.region_cover
    C.closed_region C.closed_fixedRegion C.closed_region C.closed_fixedRegion
    (C.regionChange a) (Homeomorph.refl C.fixedRegion) (C.regionChange_cross a ha)

theorem extension_map (q : X × unitInterval) : C.extension a ha (C.map q) = C.map (a q) := by
  have h := ClosedCover.homeomorph_left C.region_cover C.region_cover
    C.closed_region C.closed_fixedRegion C.closed_region C.closed_fixedRegion
    (C.regionChange a) (Homeomorph.refl C.fixedRegion) (C.regionChange_cross a ha)
    (C.coordinates q)
  exact h.trans (congrArg (fun r => C.map (a r)) (C.coordinates.symm_apply_apply q))

theorem extension_fixed (y : Y) (hy : y ∉ C.innerRegion) : C.extension a ha y = y :=
  ClosedCover.homeomorph_right C.region_cover C.region_cover
    C.closed_region C.closed_fixedRegion C.closed_region C.closed_fixedRegion
    (C.regionChange a) (Homeomorph.refl C.fixedRegion) (C.regionChange_cross a ha) ⟨y, hy⟩

theorem extension_boundary (e : X ≃ₜ X) (hzero : ∀ x, a (x, 0) = (e x, 0)) (x : X) :
    C.extension a ha (i x) = i (e x) := by
  rw [← C.zero x, C.extension_map, hzero, C.zero]

end Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
