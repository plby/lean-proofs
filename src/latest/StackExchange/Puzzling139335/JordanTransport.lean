import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transport of Jordan regions by plane homeomorphisms

The bounded complementary component is preserved by a homeomorphism of the
plane.  This supplies the set-level transport needed when straightening arcs.
-/

open Set

namespace Puzzling139335

theorem planeHomeomorph_isBounded_image (e : Plane ≃ₜ Plane) {S : Set Plane} :
    Bornology.IsBounded (e '' S) ↔ Bornology.IsBounded S := by
  constructor
  · intro h
    have h' := (h.isCompact_closure.image e.symm.continuous).isBounded
    have hs : S ⊆ e.symm '' closure (e '' S) := by
      intro x hx
      exact ⟨e x, subset_closure (mem_image_of_mem e hx), e.symm_apply_apply x⟩
    exact h'.subset hs
  · intro h
    exact (h.isCompact_closure.image e.continuous).isBounded.subset
      (image_mono subset_closure)

end Puzzling139335

namespace Schoenflies

theorem IsJordanCurve.image_homeomorph {C : Set Plane} (hC : IsJordanCurve C)
    (e : Plane ≃ₜ Plane) : IsJordanCurve (e '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  refine ⟨e ∘ f, ⟨e.continuous.comp_continuousOn hf.continuousOn,
    congrArg e hf.closes, ?_⟩, ?_⟩
  · intro x hx y hy h
    exact hf.injOn hx hy (e.injective h)
  · exact image_comp e f unitInterval

theorem IsArcBetween.image_homeomorph {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (e : Plane ≃ₜ Plane) :
    IsArcBetween (e '' A) (e p) (e q) := by
  obtain ⟨f, hc, hi, rfl, rfl, rfl⟩ := hA
  refine ⟨e ∘ f, e.continuous.comp_continuousOn hc, ?_, image_comp e f unitInterval,
    rfl, rfl⟩
  intro x hx y hy h
  exact hi hx hy (e.injective h)

theorem homeomorph_mem_inside_iff (e : Plane ≃ₜ Plane) {C : Set Plane} {x : Plane} :
    e x ∈ inside (e '' C) ↔ x ∈ inside C := by
  have hnot : e x ∉ e '' C ↔ x ∉ C := by simp
  by_cases hx : x ∈ C
  · simp [mem_inside_iff, hx]
  · have hcomponent := e.image_connectedComponentIn (s := Cᶜ) hx
    rw [e.image_compl] at hcomponent
    simp only [mem_inside_iff, hnot, ← hcomponent,
      Puzzling139335.planeHomeomorph_isBounded_image]

theorem homeomorph_image_inside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    e '' inside C = inside (e '' C) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (homeomorph_mem_inside_iff e).2 hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (homeomorph_mem_inside_iff e).1 (by simpa using hy)

theorem homeomorph_image_outside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    e '' outside C = outside (e '' C) := by
  have hout (D : Set Plane) : outside D = Dᶜ \ inside D := by
    ext x
    simp only [mem_outside_iff, mem_sdiff, mem_compl_iff, mem_inside_iff]
    tauto
  rw [hout, image_sdiff e.injective, e.image_compl, homeomorph_image_inside, hout]

theorem IsCutPair.image_homeomorph {C A B : Set Plane} {p q : Plane}
    (h : IsCutPair C p q A B) (e : Plane ≃ₜ Plane) :
    IsCutPair (e '' C) (e p) (e q) (e '' A) (e '' B) := by
  refine ⟨h.fst.image_homeomorph e, h.snd.image_homeomorph e, ?_, ?_⟩
  · rw [← image_union, h.union_eq]
  · rw [← image_inter e.injective, h.inter_eq]
    simp only [image_pair]

end Schoenflies

namespace Puzzling139335.IsJordanRegion

theorem image_homeomorph {P : Set Plane} (hP : IsJordanRegion P)
    (e : Plane ≃ₜ Plane) : IsJordanRegion (e '' P) := by
  obtain ⟨C, hC, rfl⟩ := hP
  refine ⟨e '' C, hC.image_homeomorph e, ?_⟩
  rw [e.image_closure, Schoenflies.homeomorph_image_inside]

theorem isPathConnected_interior {P : Set Plane} (hP : IsJordanRegion P) :
    IsPathConnected (interior P) :=
  isOpen_interior.isConnected_iff_isPathConnected.mp hP.isConnected_interior

end Puzzling139335.IsJordanRegion
