import Arxiv.Arxiv2411_18291.RootedCliquePattern
import Arxiv.Arxiv2411_18291.AlignedGluing

/-!
# Prescribing both cliques of an elimination root

Two pairs of cliques with the same common-edge size have an injective
root map sending each source clique to its prescribed target. First map
one clique while respecting the common edge, then map the other clique's
remaining vertices into the corresponding disjoint remainder.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} {q r : ℕ}

theorem exists_clique_equiv_preserving_edge (P : Block V q) (Q : Block W q)
    (d : Block V r) (e : Block W r) (hdP : d.val ⊆ P.val) (heQ : e.val ⊆ Q.val) :
    ∃ σ : Q.val ≃ P.val, ∀ x (hx : x ∈ e.val), (σ ⟨x, heQ hx⟩).val ∈ d.val := by
  classical
  let δ : e.val ≃ d.val := Fintype.equivOfCardEq
    (by simp only [Fintype.card_coe, e.property, d.property])
  let σ₀ : Q.val ≃ P.val := Fintype.equivOfCardEq
    (by simp only [Fintype.card_coe, Q.property, P.property])
  let f (x : Q.val) : V :=
    if hx : x.val ∈ e.val then (δ ⟨x.val, hx⟩).val else (σ₀ x).val
  have hmap : Set.MapsTo f {x : Q.val | x.val ∈ e.val} (P.val : Set V) := by
    intro x hx
    change x.val ∈ e.val at hx
    change f x ∈ P.val
    simp only [f, dif_pos hx]
    exact hdP (δ ⟨x.val, hx⟩).property
  have hinj : Set.InjOn f {x : Q.val | x.val ∈ e.val} := by
    intro a ha b hb h
    change a.val ∈ e.val at ha
    change b.val ∈ e.val at hb
    simp only [f, dif_pos ha, dif_pos hb] at h
    exact Subtype.ext (congrArg (fun x : e.val => x.val) (δ.injective (Subtype.ext h)))
  obtain ⟨σ, hσ⟩ := hmap.exists_equiv_extend_of_card_eq
    (by simp only [Fintype.card_coe, Q.property, P.property]) hinj
  refine ⟨σ, ?_⟩
  intro x hx
  have h : (σ ⟨x, heQ hx⟩).val = (δ ⟨x, hx⟩).val := by
    simpa only [f, dif_pos hx] using hσ ⟨x, heQ hx⟩ hx
  exact h ▸ (δ ⟨x, hx⟩).property

variable [DecidableEq W] [DecidableEq V]

theorem exists_pair_root_map (P₀ N₀ : Block W q) (e₀ : Block W r)
    (h₀ : P₀.val ∩ N₀.val = e₀.val) (P N : Block V q) (e : Block V r)
    (h : P.val ∩ N.val = e.val) :
    ∃ φ : ↥(P₀.val ∪ N₀.val) ↪ V,
      rootImage φ P₀ subset_union_left = P ∧ rootImage φ N₀ subset_union_right = N := by
  have he₀P : e₀.val ⊆ P₀.val := by rw [← h₀]; exact inter_subset_left
  have heP : e.val ⊆ P.val := by rw [← h]; exact inter_subset_left
  have heN : e.val ⊆ N.val := by rw [← h]; exact inter_subset_right
  obtain ⟨σ, hσ⟩ := exists_clique_equiv_preserving_edge P P₀ e e₀ heP he₀P
  let τ : ↥(N₀.val \ P₀.val) ≃ ↥(N.val \ P.val) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe, card_sdiff, h₀, h, N₀.property, N.property,
      e₀.property, e.property])
  let f (x : ↥(P₀.val ∪ N₀.val)) : V := if hx : x.val ∈ P₀.val then (σ ⟨x.val, hx⟩).val
    else (τ ⟨x.val, mem_sdiff.mpr ⟨(mem_union.mp x.property).resolve_left hx, hx⟩⟩).val
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val ∈ P₀.val <;> by_cases hb : b.val ∈ P₀.val
    · simp only [f, dif_pos ha, dif_pos hb] at hab
      exact Subtype.ext (congrArg (fun x : P₀.val => x.val) (σ.injective (Subtype.ext hab)))
    · simp only [f, dif_pos ha, dif_neg hb] at hab
      exact ((mem_sdiff.mp (τ ⟨b.val,
        mem_sdiff.mpr ⟨(mem_union.mp b.property).resolve_left hb, hb⟩⟩).property).2
        (hab ▸ (σ ⟨a.val, ha⟩).property)).elim
    · simp only [f, dif_neg ha, dif_pos hb] at hab
      exact ((mem_sdiff.mp (τ ⟨a.val,
        mem_sdiff.mpr ⟨(mem_union.mp a.property).resolve_left ha, ha⟩⟩).property).2
        (hab ▸ (σ ⟨b.val, hb⟩).property)).elim
    · simp only [f, dif_neg ha, dif_neg hb] at hab
      exact Subtype.ext (congrArg (fun x : ↥(N₀.val \ P₀.val) => x.val)
        (τ.injective (Subtype.ext hab)))
  let φ : ↥(P₀.val ∪ N₀.val) ↪ V := ⟨f, hinj⟩
  refine ⟨φ, ?_, ?_⟩
  · apply Subtype.ext
    apply eq_of_subset_of_card_le _
      (by rw [P.property, (rootImage φ P₀ subset_union_left).property])
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    have hxP : x.val ∈ P₀.val := by simpa only [rootBlock, mem_subtype] using hx
    change f x ∈ P.val
    simpa only [f, dif_pos hxP] using (σ ⟨x.val, hxP⟩).property
  · apply Subtype.ext
    apply eq_of_subset_of_card_le _
      (by rw [N.property, (rootImage φ N₀ subset_union_right).property])
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    have hxN : x.val ∈ N₀.val := by simpa only [rootBlock, mem_subtype] using hx
    change f x ∈ N.val
    by_cases hxP : x.val ∈ P₀.val
    · have hxe : x.val ∈ e₀.val := h₀ ▸ mem_inter.mpr ⟨hxP, hxN⟩
      simpa only [f, dif_pos hxP] using heN (hσ x.val hxe)
    · simpa only [f, dif_neg hxP] using
        (mem_sdiff.mp (τ ⟨x.val, mem_sdiff.mpr ⟨hxN, hxP⟩⟩).property).1

end Arxiv2411_18291
