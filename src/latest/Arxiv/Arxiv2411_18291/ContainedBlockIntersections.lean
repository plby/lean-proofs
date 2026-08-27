import Arxiv.Arxiv2411_18291.Basic
import Mathlib.Tactic

/-! # Counting contained blocks by their intersection with a fixed subset -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem card_contained_blocks_with_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    (Z A : Finset V) (hAZ : A ⊆ Z) (r t : ℕ) (htr : t ≤ r) :
    (univ.filter fun e : Block V r => e.val ⊆ Z ∧ (e.val \ A).card = t).card =
      A.card.choose (r - t) * (Z.card - A.card).choose t := by
  have hreconstruct (e : Finset V) : (A ∩ e) ∪ (e \ A) = e := by
    rw [inter_comm, union_comm, sdiff_union_inter]
  calc
    _ = (A.powersetCard (r - t) ×ˢ (Z \ A).powersetCard t).card := by
      apply card_bij (fun e _ => (A ∩ e.val, e.val \ A))
      · intro e he
        obtain ⟨heZ, het⟩ := (mem_filter.mp he).2
        apply mem_product.mpr
        constructor
        · apply mem_powersetCard.mpr
          refine ⟨inter_subset_left, ?_⟩
          have hi : (A ∩ e.val).card ≤ r := by
            simpa only [e.property] using card_le_card (inter_subset_right : A ∩ e.val ⊆ e.val)
          rw [card_sdiff, e.property] at het
          change (A ∩ e.val).card = r - t
          omega
        · refine mem_powersetCard.mpr ⟨?_, het⟩
          intro x hx
          exact mem_sdiff.mpr ⟨heZ (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
      · intro e _ f _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        dsimp only at h1 h2
        apply Subtype.ext
        calc
          e.val = (A ∩ e.val) ∪ (e.val \ A) := (hreconstruct _).symm
          _ = (A ∩ f.val) ∪ (f.val \ A) := by rw [h1, h2]
          _ = f.val := hreconstruct _
      · rintro ⟨U, W⟩ hp
        obtain ⟨hU, hW⟩ := mem_product.mp hp
        obtain ⟨hUA, hUr⟩ := mem_powersetCard.mp hU
        obtain ⟨hWA, hWt⟩ := mem_powersetCard.mp hW
        have hd : Disjoint U W := disjoint_left.mpr fun x hxU hxW =>
          (mem_sdiff.mp (hWA hxW)).2 (hUA hxU)
        have hi : A ∩ (U ∪ W) = U := by
          ext x
          simp only [mem_inter, mem_union]
          constructor
          · rintro ⟨hxA, hxU | hxW⟩
            · exact hxU
            · exact False.elim ((mem_sdiff.mp (hWA hxW)).2 hxA)
          · intro hxU
            exact ⟨hUA hxU, Or.inl hxU⟩
        have hw : (U ∪ W) \ A = W := by
          ext x
          simp only [mem_sdiff, mem_union]
          constructor
          · rintro ⟨hxU | hxW, hxA⟩
            · exact False.elim (hxA (hUA hxU))
            · exact hxW
          · intro hxW
            exact ⟨Or.inr hxW, (mem_sdiff.mp (hWA hxW)).2⟩
        let e : Block V r := ⟨U ∪ W, by rw [card_union_of_disjoint hd, hUr, hWt]; omega⟩
        refine ⟨e, mem_filter.mpr ⟨mem_univ _, ?_⟩, Prod.ext hi hw⟩
        constructor
        · exact union_subset (hUA.trans hAZ) (hWA.trans sdiff_subset)
        · change ((U ∪ W) \ A).card = t
          rw [hw, hWt]
    _ = _ := by
      rw [card_product, card_powersetCard, card_powersetCard, card_sdiff_of_subset hAZ]

end Arxiv2411_18291
