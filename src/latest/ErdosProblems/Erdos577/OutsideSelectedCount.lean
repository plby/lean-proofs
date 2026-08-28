import ErdosProblems.Erdos577.OutsideCoreCount

/-! Degree averaging outside an arbitrary selected block family, without a nonempty assumption. -/

namespace Erdos577.TriangleChain

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma contacts_selected_core_add_outside (c : TriangleChain G) (bs : Finset (Finset V))
    (hbs : bs ⊆ c.blocks) (s : Finset V) :
    contacts G s (c.remainder ∪ bs.biUnion id) +
      ∑ a ∈ c.blocks \ bs, contacts G s a = contacts G s univ := by
  let outside := c.complementPartition.removeMany bs hbs
  have hd : Disjoint (c.remainder ∪ bs.biUnion id)
      ((univ \ c.remainder) \ bs.biUnion id) := by
    apply disjoint_left.mpr
    intro v hv hw
    rcases mem_union.mp hv with hv | hv
    · exact (mem_sdiff.mp (mem_sdiff.mp hw).1).2 hv
    · exact (mem_sdiff.mp hw).2 hv
  have he : (c.remainder ∪ bs.biUnion id) ∪
      ((univ \ c.remainder) \ bs.biUnion id) = univ := by
    ext v
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    tauto
  calc
    _ = contacts G s (c.remainder ∪ bs.biUnion id) +
        contacts G s (outside.blocks.biUnion id) := by
      rw [contacts_biUnion_right G s outside.blocks id outside.disjoint]
      rfl
    _ = _ := by rw [outside.cover, ← contacts_union_right G s hd, he]

lemma exists_heavy_outside_selected (c : TriangleChain G) (bs : Finset (Finset V))
    (hbs : bs ⊆ c.blocks) (s : Finset V) (d threshold : ℕ) (hdeg : ∀ v, d ≤ G.degree v)
    (hbudget : contacts G s (c.remainder ∪ bs.biUnion id) +
      (c.blocks \ bs).card * threshold < s.card * d) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ threshold < contacts G s a := by
  have htotal := minimum_degree_sum G s d (fun v _ ↦ hdeg v)
  have hid := c.contacts_selected_core_add_outside bs hbs s
  obtain ⟨a, ha, hheavy⟩ := exists_heavy_block G s (c.blocks \ bs) id threshold (by
    simp only [id_eq]
    omega)
  exact ⟨a, (mem_sdiff.mp ha).1, (mem_sdiff.mp ha).2, hheavy⟩

lemma exists_thirteen_outside_two (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs2 : bs.card = 2)
    (s : Finset V) (hs : s.card = 6)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) ≤ 32) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ 13 ≤ contacts G s a := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨a, ha, hna, hh⟩ := c.exists_heavy_outside_selected bs hbs s (2 * k) 12 hdeg (by
    rw [hs]
    omega)
  exact ⟨a, ha, hna, Nat.succ_le_of_lt hh⟩

end Erdos577.TriangleChain
