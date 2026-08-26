import ErdosProblems.Erdos547.PairedTree
import ErdosProblems.Erdos547.PairChoices

/-!
# Embedding a fresh pair while preserving the seed

The tree attachment and the host pair are combined here. The resulting copy
has exactly the old used images plus the two selected host vertices.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*}

open scoped Classical in
/-- Changing between equal descriptions of the seed set does not change its
used images, even if the two finite-type instances differ. -/
theorem reindex_copy_used {T : SimpleGraph U} {G : SimpleGraph V}
    (A B : Set U) [Fintype A] [Fintype B] (hAB : A = B) (e : (T.induce A).Copy G) :
    ∃ f : (T.induce B).Copy G, Finset.univ.image f = Finset.univ.image e := by
  classical
  subst B
  refine ⟨e, ?_⟩
  ext v
  simp

open scoped Classical in
theorem extend_copy_pair
    {T : SimpleGraph U} {G : SimpleGraph V}
    (hT : T.IsAcyclic) (S : Set U) [Fintype S] (hS : (T.induce S).Connected)
    (e : (T.induce S).Copy G) (p : S) (u v : U) (hu : u ∉ S) (hv : v ∉ S)
    (hpu : T.Adj p.val u) (huv : T.Adj u v)
    (z w : V) (hpz : G.Adj (e p) z) (hzw : G.Adj z w)
    (hz : z ∉ Finset.univ.image e) (hw : w ∉ Finset.univ.image e) :
    ∃ f : (T.induce (insert v (insert u S))).Copy G,
      (∀ x : S, f ⟨x.val, Or.inr (Or.inr x.property)⟩ = e x) ∧
        Finset.univ.image f = insert w (insert z (Finset.univ.image e)) := by
  classical
  have hup : ∀ y ∈ S, T.Adj u y → y = p.val := by
    intro y hy huy
    exact unique_attachment_to_connected hT S hS.preconnected hu hy p.property huy hpu.symm
  obtain ⟨e₁, he₁u, he₁old⟩ := extend_copy_insert S u hu p hup e z hpz (by
    intro x hx
    exact hz (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩))
  have hS₁ := connected_induce_insert S hS u p hpu.symm
  have hv₁ : v ∉ insert u S := by
    intro h
    rcases h with h | h
    · exact huv.ne' h
    · exact hv h
  let u₁ : (insert u S : Set U) := ⟨u, Or.inl rfl⟩
  have hvu : ∀ y ∈ insert u S, T.Adj v y → y = u₁.val := by
    intro y hy hvy
    exact unique_attachment_to_connected hT (insert u S) hS₁.preconnected hv₁
      hy u₁.property hvy huv.symm
  have hnewedge : G.Adj (e₁ u₁) w := by
    rw [show e₁ u₁ = z from he₁u]
    exact hzw
  have hwfresh : ∀ x : (insert u S : Set U), e₁ x ≠ w := by
    intro x hxw
    rcases x.property with hx | hx
    · have hxu : x = u₁ := Subtype.ext hx
      rw [hxu, show e₁ u₁ = z from he₁u] at hxw
      exact hzw.ne hxw
    · have hxo : x = ⟨x.val, Set.mem_insert_of_mem u hx⟩ := rfl
      rw [hxo, he₁old ⟨x.val, hx⟩] at hxw
      exact hw (Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_univ _, hxw⟩)
  obtain ⟨e₂, he₂v, he₂old⟩ := extend_copy_insert (insert u S) v hv₁ u₁ hvu e₁ w hnewedge hwfresh
  have heold (x : S) : e₂ ⟨x.val, Or.inr (Or.inr x.property)⟩ = e x :=
    (he₂old ⟨x.val, Or.inr x.property⟩).trans (he₁old x)
  have heu : e₂ ⟨u, Or.inr (Or.inl rfl)⟩ = z := (he₂old u₁).trans he₁u
  refine ⟨e₂, heold, ?_⟩
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨x, hx⟩
    rcases x.property with hxv | hxu | hxS
    · have heq : x = ⟨v, Or.inl rfl⟩ := Subtype.ext hxv
      rw [heq, he₂v] at hx
      exact Or.inl hx.symm
    · have heq : x = ⟨u, Or.inr (Or.inl rfl)⟩ := Subtype.ext hxu
      rw [heq, heu] at hx
      exact Or.inr (Or.inl hx.symm)
    · have heq : x = ⟨x.val, Or.inr (Or.inr hxS)⟩ := rfl
      rw [heq, heold ⟨x.val, hxS⟩] at hx
      exact Or.inr (Or.inr ⟨⟨x.val, hxS⟩, hx⟩)
  · rintro (hy | hy | ⟨x, hx⟩)
    · exact ⟨⟨v, Or.inl rfl⟩, he₂v.trans hy.symm⟩
    · exact ⟨⟨u, Or.inr (Or.inl rfl)⟩, heu.trans hy.symm⟩
    · exact ⟨⟨x.val, Or.inr (Or.inr x.property)⟩, (heold x).trans hx⟩

open scoped Classical in
/-- The finite-set version packages the reindexing of the two inserted tree
vertices, so iterative proofs need only the equality of used image sets. -/
theorem extend_copy_pair_finset
    {T : SimpleGraph U} {G : SimpleGraph V}
    (hT : T.IsAcyclic) (S : Finset U) (hS : (T.induce (S : Set U)).Connected)
    (e : (T.induce (S : Set U)).Copy G) (p : (S : Set U))
    (u v : U) (hu : u ∉ S) (hv : v ∉ S) (hpu : T.Adj p.val u) (huv : T.Adj u v)
    (z w : V) (hpz : G.Adj (e p) z) (hzw : G.Adj z w)
    (hz : z ∉ Finset.univ.image e) (hw : w ∉ Finset.univ.image e) :
    ∃ f : (T.induce (↑(insert v (insert u S)) : Set U)).Copy G,
      Finset.univ.image f = insert w (insert z (Finset.univ.image e)) := by
  classical
  obtain ⟨e₂, _, himage⟩ := extend_copy_pair hT (S : Set U) hS e p u v hu hv hpu huv
    z w hpz hzw
    (by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hz)
    (by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hw)
  have hsets : insert v (insert u (S : Set U)) = (↑(insert v (insert u S)) : Set U) := by
    ext x
    simp
  obtain ⟨f, hf⟩ := reindex_copy_used (T := T) (G := G)
    (insert v (insert u (S : Set U))) (↑(insert v (insert u S)) : Set U) hsets e₂
  refine ⟨f, ?_⟩
  simpa only [Finset.ext_iff, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert] using hf.trans himage

end Erdos547

#print axioms Erdos547.extend_copy_pair
#print axioms Erdos547.extend_copy_pair_finset
