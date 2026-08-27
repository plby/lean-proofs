import Arxiv.Arxiv2411_18291.DisjointFamilyPermutation

/-!
# Permutation orbits of pairs with a specified intersection

An ordered pair of blocks is recorded together with its intersection size.
Permutations preserve this data and act transitively on every nonempty such
type. All fibers of the random-permutation map therefore have equal size.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

abbrev IntersectingBlockPair (V : Type*) [DecidableEq V] (a b s : ℕ) :=
  {P : Block V a × Block V b // (P.1.val ∩ P.2.val).card = s}

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {a b s : ℕ}

def mapBlockPair (f : V ↪ W) (P : IntersectingBlockPair V a b s) :
    IntersectingBlockPair W a b s :=
  ⟨(mapBlock f P.val.1, mapBlock f P.val.2), by
    change ((P.val.1.val.map f) ∩ (P.val.2.val.map f)).card = s
    rw [← map_inter, card_map]
    exact P.property⟩

def blockPairEquiv (σ : V ≃ W) :
    IntersectingBlockPair V a b s ≃ IntersectingBlockPair W a b s where
  toFun := mapBlockPair σ.toEmbedding
  invFun := mapBlockPair σ.symm.toEmbedding
  left_inv P := by
    apply Subtype.ext
    exact Prod.ext ((blockEquiv σ).left_inv P.val.1) ((blockEquiv σ).left_inv P.val.2)
  right_inv P := by
    apply Subtype.ext
    exact Prod.ext ((blockEquiv σ).right_inv P.val.1) ((blockEquiv σ).right_inv P.val.2)

theorem mapBlockPair_equiv_trans (σ τ : Equiv.Perm V) (P : IntersectingBlockPair V a b s) :
    mapBlockPair (σ.trans τ).toEmbedding P =
      mapBlockPair τ.toEmbedding (mapBlockPair σ.toEmbedding P) := by
  apply Subtype.ext
  exact Prod.ext (mapBlock_equiv_trans σ τ P.val.1) (mapBlock_equiv_trans σ τ P.val.2)

theorem exists_perm_mapBlockPair (P Q : IntersectingBlockPair V a b s) :
    ∃ σ : Equiv.Perm V, mapBlockPair σ.toEmbedding P = Q := by
  obtain ⟨σ, h1, h2⟩ := exists_perm_map_finset_pair P.val.1.val P.val.2.val Q.val.1.val Q.val.2.val
    (by rw [P.val.1.property, Q.val.1.property])
    (by rw [P.val.2.property, Q.val.2.property]) (P.property.trans Q.property.symm)
  exact ⟨σ, Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))⟩

variable [Fintype V]

theorem permutation_blockPair_fiber_card (P Q Q' : IntersectingBlockPair V a b s) :
    (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.toEmbedding P = Q).card =
      (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.toEmbedding P = Q').card := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_mapBlockPair Q Q'
  apply card_bij (fun σ _ => σ.trans τ)
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [mapBlockPair_equiv_trans, hσ, hτ]
  · intro σ _ σ' _ he
    ext x
    exact τ.injective (congrArg (fun f : Equiv.Perm V => f x) he)
  · intro σ hσ
    refine ⟨σ.trans τ.symm, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      rw [mapBlockPair_equiv_trans, hσ, ← hτ]
      exact (blockPairEquiv τ).left_inv Q
    · ext x
      simp

theorem permutation_inverse_blockPair_fiber_card (P Q : IntersectingBlockPair V a b s) :
    (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.symm.toEmbedding P = Q).card =
      (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.toEmbedding P = Q).card := by
  classical
  apply card_bij (fun σ _ => σ.symm)
  · intro σ hσ
    simpa only [mem_filter, mem_univ, true_and] using hσ
  · intro σ _ τ _ he
    simpa using congrArg Equiv.symm he
  · intro σ hσ
    exact ⟨σ.symm, by simpa using hσ, by simp⟩

end Arxiv2411_18291
