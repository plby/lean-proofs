import ErdosProblems.Erdos73.BrickStripNetworks

/-! Two vertices of an available strip network need at most two strips of each kind. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

theorem exists_brickStripNetwork_pair
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (x : V) (hx : x ∈ brickStripNetwork S A B) :
    ∃ a ∈ A, ∃ b ∈ B, x ∈ brickFaceRowStrip S a ∨ x ∈ brickFaceColumnStrip S b := by
  rcases (mem_brickStripNetwork S A B x).mp hx with ⟨a, ha, hx⟩ | ⟨b, hb, hx⟩
  · obtain ⟨b, hb⟩ := hB
    exact ⟨a, ha, b, hb, Or.inl hx⟩
  · obtain ⟨a, ha⟩ := hA
    exact ⟨a, ha, b, hb, Or.inr hx⟩

theorem exists_small_brickStripNetwork
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (x y : V)
    (hx : x ∈ brickStripNetwork S A B) (hy : y ∈ brickStripNetwork S A B) :
    ∃ A' : Finset (Fin (r - 1)), ∃ B' : Finset (Fin (c - 1)),
      A' ⊆ A ∧ B' ⊆ B ∧ A'.Nonempty ∧ B'.Nonempty ∧ A'.card ≤ 2 ∧ B'.card ≤ 2 ∧
      x ∈ brickStripNetwork S A' B' ∧ y ∈ brickStripNetwork S A' B' := by
  obtain ⟨a, ha, b, hb, hx⟩ := exists_brickStripNetwork_pair S A B hA hB x hx
  obtain ⟨a', ha', b', hb', hy⟩ := exists_brickStripNetwork_pair S A B hA hB y hy
  refine ⟨{a, a'}, {b, b'}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [insert_subset_iff, singleton_subset_iff] using And.intro ha ha'
  · simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hb hb'
  · exact ⟨a, mem_insert_self _ _⟩
  · exact ⟨b, mem_insert_self _ _⟩
  · exact (card_insert_le _ _).trans (by simp)
  · exact (card_insert_le _ _).trans (by simp)
  · apply (mem_brickStripNetwork S _ _ _).mpr
    exact hx.elim (fun hh => Or.inl ⟨a, mem_insert_self _ _, hh⟩)
      (fun hh => Or.inr ⟨b, mem_insert_self _ _, hh⟩)
  · apply (mem_brickStripNetwork S _ _ _).mpr
    exact hy.elim (fun hh => Or.inl ⟨a', mem_insert_of_mem (mem_singleton_self _), hh⟩)
      (fun hh => Or.inr ⟨b', mem_insert_of_mem (mem_singleton_self _), hh⟩)

end
end Erdos73
