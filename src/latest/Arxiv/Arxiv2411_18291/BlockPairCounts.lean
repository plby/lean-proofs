import Arxiv.Arxiv2411_18291.BlockPairOrbits

/-!
# Counting block pairs with a prescribed intersection

Choose the intersection inside the first block and the remaining vertices
outside it. This gives the exact normalizing count for the joint permutation
law, including the depletion of the available vertex set.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem card_blocks_with_intersection (A : Finset V) (b s : ℕ) (hs : s ≤ b) :
    (univ.filter fun Q : Block V b => (A ∩ Q.val).card = s).card =
      A.card.choose s * (Fintype.card V - A.card).choose (b - s) := by
  have hreconstruct (Q : Finset V) : (A ∩ Q) ∪ (Q \ A) = Q := by
    rw [inter_comm, union_comm, sdiff_union_inter]
  calc
    _ = (A.powersetCard s ×ˢ (univ \ A).powersetCard (b - s)).card := by
      apply card_bij (fun Q _ => (A ∩ Q.val, Q.val \ A))
      · intro Q hQ
        have hI := (mem_filter.mp hQ).2
        apply mem_product.mpr
        constructor
        · exact mem_powersetCard.mpr ⟨inter_subset_left, hI⟩
        · apply mem_powersetCard.mpr
          constructor
          · intro x hx
            exact mem_sdiff.mpr ⟨mem_univ x, (mem_sdiff.mp hx).2⟩
          · rw [card_sdiff, Q.property, hI]
      · intro Q _ R _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        dsimp only at h1 h2
        apply Subtype.ext
        calc
          Q.val = (A ∩ Q.val) ∪ (Q.val \ A) := (hreconstruct _).symm
          _ = (A ∩ R.val) ∪ (R.val \ A) := by rw [h1, h2]
          _ = R.val := hreconstruct _
      · rintro ⟨U, W⟩ hp
        obtain ⟨hU, hW⟩ := mem_product.mp hp
        obtain ⟨hUA, hUs⟩ := mem_powersetCard.mp hU
        obtain ⟨hWA, hWs⟩ := mem_powersetCard.mp hW
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
        let Q : Block V b := ⟨U ∪ W, by rw [card_union_of_disjoint hd, hUs, hWs]; omega⟩
        refine ⟨Q, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
        · change (A ∩ (U ∪ W)).card = s
          rw [hi, hUs]
        · exact Prod.ext hi hw
    _ = _ := by
      rw [card_product, card_powersetCard, card_powersetCard,
        card_sdiff_of_subset (subset_univ A), card_univ]

theorem card_intersectingBlockPair (a b s : ℕ) (hs : s ≤ b) :
    Fintype.card (IntersectingBlockPair V a b s) =
      (Fintype.card V).choose a * a.choose s * (Fintype.card V - a).choose (b - s) := by
  let e : IntersectingBlockPair V a b s ≃
      Σ P : Block V a, {Q : Block V b // (P.val ∩ Q.val).card = s} := {
    toFun := fun P => ⟨P.val.1, P.val.2, P.property⟩
    invFun := fun P => ⟨(P.1, P.2.val), P.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hc (P : Block V a) :
      Fintype.card {Q : Block V b // (P.val ∩ Q.val).card = s} =
        a.choose s * (Fintype.card V - a).choose (b - s) := by
    rw [Fintype.card_subtype]
    simpa only [P.property] using card_blocks_with_intersection P.val b s hs
  simp only [hc, sum_const, card_univ, smul_eq_mul, Block, Fintype.card_finset_len]
  exact (Nat.mul_assoc _ _ _).symm

end Arxiv2411_18291
