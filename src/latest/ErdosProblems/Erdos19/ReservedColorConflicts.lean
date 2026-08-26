import ErdosProblems.Erdos19.Core

/-! # Counting colors seen from a bounded-size edge -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]

noncomputable def forbiddenByColoring (H : SetHypergraph V) (color : H.EdgeColoring C)
    (U : Set V) (palette : Finset C) : Finset C :=
  palette.filter fun a ↦ ∃ e : H, color.color e = a ∧ (U ∩ e.1).Nonempty

theorem card_meeting_family_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (U : Set V) (S : Finset H) (r : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ e ∈ S, r ≤ e.1.ncard)
    (hmeet : ∀ e ∈ S, (U ∩ e.1).Nonempty) :
    S.card ≤ U.ncard * ((Fintype.card V - 1) / (r - 1)) := by
  classical
  have hcount := H.edge_vertex_incidence_bound S U.toFinset 1
    ((Fintype.card V - 1) / (r - 1))
  have he : ∀ e ∈ S, 1 ≤ (U.toFinset.filter fun v ↦ v ∈ e.1).card := by
    intro e he
    obtain ⟨v, hvU, hve⟩ := hmeet e he
    exact card_pos.mpr ⟨v, mem_filter.mpr ⟨Set.mem_toFinset.mpr hvU, hve⟩⟩
  have hv : ∀ v ∈ U.toFinset,
      (S.filter fun e ↦ v ∈ e.1).card ≤ (Fintype.card V - 1) / (r - 1) := by
    intro v _
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).mpr
    have h := H.incidentSubfamily_ncard_mul_sub_one_le hlinear
      ((S.filter fun e ↦ v ∈ e.1) : Set H) v r
      (fun e he ↦ (mem_filter.mp he).2)
      (fun e he ↦ hmin e (mem_filter.mp he).1)
    simpa only [Set.ncard_coe_finset] using h
  have h := hcount he hv
  simpa only [Nat.mul_one, Set.ncard_eq_toFinset_card'] using h

theorem forbiddenByColoring_card_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (color : H.EdgeColoring C) (U : Set V) (palette : Finset C)
    (r : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ e : H, color.color e ∈ palette → r ≤ e.1.ncard) :
    (H.forbiddenByColoring color U palette).card ≤
      U.ncard * ((Fintype.card V - 1) / (r - 1)) := by
  classical
  let S := (univ : Finset H).filter fun e ↦
    color.color e ∈ palette ∧ (U ∩ e.1).Nonempty
  have hsub : H.forbiddenByColoring color U palette ⊆ S.image color.color := by
    intro a ha
    obtain ⟨hap, e, he, hmeet⟩ := mem_filter.mp ha
    refine mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, ?_, hmeet⟩, he⟩
    simpa only [he] using hap
  have hcount := H.card_meeting_family_le hlinear U S r hr
    (fun e he ↦ hmin e (mem_filter.mp he).2.1)
    (fun e he ↦ (mem_filter.mp he).2.2)
  exact (card_le_card hsub).trans (card_image_le.trans hcount)

noncomputable def forbiddenReservedColors (H : SetHypergraph V) (color : H.EdgeColoring C)
    (U : Set V) (palette : Finset C) : Finset palette :=
  univ.filter fun a ↦ ∃ e : H, color.color e = a.1 ∧ (U ∩ e.1).Nonempty

theorem forbiddenReservedColors_card_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (color : H.EdgeColoring C) (U : Set V) (palette : Finset C)
    (r : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ e : H, color.color e ∈ palette → r ≤ e.1.ncard) :
    (H.forbiddenReservedColors color U palette).card ≤
      U.ncard * ((Fintype.card V - 1) / (r - 1)) := by
  have himage : (H.forbiddenReservedColors color U palette).image Subtype.val =
      H.forbiddenByColoring color U palette := by
    ext a
    constructor
    · intro ha
      obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
      exact mem_filter.mpr ⟨a'.2, (mem_filter.mp ha').2⟩
    · intro ha
      obtain ⟨hap, hmeet⟩ := mem_filter.mp ha
      exact mem_image.mpr ⟨⟨a, hap⟩, mem_filter.mpr ⟨mem_univ _, hmeet⟩, rfl⟩
  have hcard := card_image_of_injective (H.forbiddenReservedColors color U palette)
    Subtype.val_injective
  rw [himage] at hcard
  rw [← hcard]
  exact H.forbiddenByColoring_card_le hlinear color U palette r hr hmin

#print axioms forbiddenReservedColors_card_le

end Erdos19.SetHypergraph
