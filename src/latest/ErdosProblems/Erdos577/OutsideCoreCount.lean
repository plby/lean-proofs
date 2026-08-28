import ErdosProblems.Erdos577.PathTransfer

/-! Exact degree averaging outside the remainder and one old block, including an empty outside. -/

namespace Erdos577.TriangleChain

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma contacts_core_add_outside (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (s : Finset V) :
    contacts G s (c.remainder ∪ b) + ∑ a ∈ c.blocks.erase b, contacts G s a =
      contacts G s univ := by
  let outside := c.complementPartition.remove b hb
  have hd : Disjoint (c.remainder ∪ b) ((univ \ c.remainder) \ b) := by
    apply disjoint_left.mpr
    intro v hv hw
    rcases mem_union.mp hv with hv | hv
    · exact (mem_sdiff.mp (mem_sdiff.mp hw).1).2 hv
    · exact (mem_sdiff.mp hw).2 hv
  have he : (c.remainder ∪ b) ∪ ((univ \ c.remainder) \ b) = univ := by
    ext v
    simp only [mem_union, mem_sdiff, mem_univ, true_and]
    tauto
  calc
    contacts G s (c.remainder ∪ b) + ∑ a ∈ c.blocks.erase b, contacts G s a =
        contacts G s (c.remainder ∪ b) + contacts G s (outside.blocks.biUnion id) := by
      rw [contacts_biUnion_right G s outside.blocks id outside.disjoint]
      rfl
    _ = contacts G s univ := by rw [outside.cover, ← contacts_union_right G s hd, he]

lemma exists_heavy_outside_core (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (s : Finset V) (d threshold : ℕ) (hdeg : ∀ v, d ≤ G.degree v)
    (hbudget : contacts G s (c.remainder ∪ b) + (c.blocks.erase b).card * threshold <
      s.card * d) : ∃ a ∈ c.blocks, a ≠ b ∧ threshold < contacts G s a := by
  have htotal := minimum_degree_sum G s d (fun v _ ↦ hdeg v)
  have hid := c.contacts_core_add_outside hb s
  obtain ⟨a, ha, hheavy⟩ := exists_heavy_block G s (c.blocks.erase b) id threshold (by
    simp only [id_eq]
    omega)
  exact ⟨a, (mem_erase.mp ha).2, (mem_erase.mp ha).1, hheavy⟩

lemma exists_nine_contact_outside_core (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    {b : Finset V} (hb : b ∈ c.blocks) (s : Finset V) (hs : s.card = 4)
    (hinside : contacts G s (c.remainder ∪ b) ≤ 15) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 9 ≤ contacts G s a := by
  have hblocks := c.card_vertices
  have herase := card_erase_of_mem hb
  have hpos : 0 < c.blocks.card := card_pos.mpr ⟨b, hb⟩
  obtain ⟨a, ha, hne, hh⟩ := c.exists_heavy_outside_core hb s (2 * k) 8 hdeg (by
    rw [hs]
    omega)
  exact ⟨a, ha, hne, Nat.succ_le_of_lt hh⟩

lemma exists_eleven_contact_outside_core (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    {b : Finset V} (hb : b ∈ c.blocks) (s : Finset V) (hs : s.card = 5)
    (hinside : contacts G s (c.remainder ∪ b) ≤ 19) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 11 ≤ contacts G s a := by
  have hblocks := c.card_vertices
  have herase := card_erase_of_mem hb
  have hpos : 0 < c.blocks.card := card_pos.mpr ⟨b, hb⟩
  obtain ⟨a, ha, hne, hh⟩ := c.exists_heavy_outside_core hb s (2 * k) 10 hdeg (by
    rw [hs]
    omega)
  exact ⟨a, ha, hne, Nat.succ_le_of_lt hh⟩

end Erdos577.TriangleChain
