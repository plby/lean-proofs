import ErdosProblems.Erdos577.FullRowInside

/-! The inside estimates force a retained outside block with at least thirteen contacts. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma new_block_ne_old {c : TriangleChain G} (p : Paw G) (hp : p.support = c.remainder)
    (s : Finset V) (u : V) {a : Finset V} (ha : a ∈ c.blocks) :
    insert p.leaf (s.erase u) ≠ a := by
  intro he
  exact (c.presentPaw p hp).terminal_not_mem_block ha (he ▸ mem_insert_self _ _)

omit [DecidableRel G.Adj] in
lemma retained_after_first_swap {c d : TriangleChain G} (p : Paw G) (q : Quadrilateral G)
    (s : Finset V)
    (hblocks : d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))})
    {a : Finset V} (ha : a ∈ d.blocks) (hne : a ≠ insert p.leaf (s.erase (q 3))) :
    a ∈ c.blocks ∧ a ≠ s := by
  rw [hblocks] at ha
  rcases mem_union.mp ha with ha | ha
  · exact ⟨(mem_erase.mp ha).2, (mem_erase.mp ha).1⟩
  · exact False.elim (hne (mem_singleton.mp ha))

theorem direct_heavy {c d : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (p : Paw G) (hp : p.support = c.remainder) (q : Quadrilateral G) (s : Finset V)
    (hblocks : d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))})
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (v : Quadrilateral G) (hv : v.support = a)
    (hinside : contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ (insert p.leaf (s.erase (q 3)) ∪ a)) ≤ 33) :
    ∃ j ∈ c.blocks, j ≠ s ∧ j ≠ a ∧ j ∈ d.blocks ∧
      13 ≤ contacts G (CoreTransfer.rows d v) j := by
  let t := insert p.leaf (s.erase (q 3))
  have ht : t ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have had : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hta : t ≠ a := new_block_ne_old p hp s (q 3) ha
  have hsel : ({t, a} : Finset (Finset V)) ⊆ d.blocks := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨ht, had⟩
  have hsize : ({t, a} : Finset (Finset V)).card = 2 := card_pair hta
  have hvd : v.support ∈ d.blocks := hv.symm ▸ had
  have hcount : contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ ({t, a} : Finset (Finset V)).biUnion id) + 2 ≤
      12 * (({t, a} : Finset (Finset V)).card + 1) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hsize]
    change contacts G (CoreTransfer.rows d v) (d.remainder ∪ (t ∪ a)) ≤ 33 at hinside
    omega
  obtain ⟨j, hj, hjn, hheavy⟩ := CoreTransfer.exists_heavy d hcard hdeg {t, a} hsel
    (CoreTransfer.rows d v) (CoreTransfer.rows_card d v hvd) hcount
  have hjt : j ≠ t := fun he ↦ hjn (mem_insert.mpr (Or.inl he))
  have hja : j ≠ a := fun he ↦ hjn (mem_insert_of_mem (mem_singleton.mpr he))
  have hold := retained_after_first_swap p q s hblocks hj hjt
  exact ⟨j, hold.1, hold.2, hja, hj, hheavy⟩

theorem other_heavy {c d : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (p : Paw G) (hp : p.support = c.remainder) (q : Quadrilateral G) (s : Finset V)
    (hblocks : d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))})
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s) (hba : b ≠ a)
    (v : Quadrilateral G) (hv : v.support = a)
    (hinside : contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ (insert p.leaf (s.erase (q 3)) ∪ (b ∪ a))) ≤ 41) :
    ∃ j ∈ c.blocks, j ≠ s ∧ j ≠ b ∧ j ≠ a ∧ j ∈ d.blocks ∧
      13 ≤ contacts G (CoreTransfer.rows d v) j := by
  let t := insert p.leaf (s.erase (q 3))
  have ht : t ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have had : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hbd : b ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hbs, hb⟩)
  have hta : t ≠ a := new_block_ne_old p hp s (q 3) ha
  have htb : t ≠ b := new_block_ne_old p hp s (q 3) hb
  have htn : t ∉ ({b, a} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton]
    exact not_or.mpr ⟨htb, hta⟩
  have hsel : ({t, b, a} : Finset (Finset V)) ⊆ d.blocks := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨ht, hbd, had⟩
  have hsize : ({t, b, a} : Finset (Finset V)).card = 3 := by
    rw [card_insert_of_notMem htn, card_pair hba]
  have hvd : v.support ∈ d.blocks := hv.symm ▸ had
  have hcount : contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ ({t, b, a} : Finset (Finset V)).biUnion id) + 2 ≤
      12 * (({t, b, a} : Finset (Finset V)).card + 1) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hsize]
    change contacts G (CoreTransfer.rows d v) (d.remainder ∪ (t ∪ (b ∪ a))) ≤ 41 at hinside
    omega
  obtain ⟨j, hj, hjn, hheavy⟩ := CoreTransfer.exists_heavy d hcard hdeg {t, b, a} hsel
    (CoreTransfer.rows d v) (CoreTransfer.rows_card d v hvd) hcount
  have hjt : j ≠ t := fun he ↦ hjn (mem_insert.mpr (Or.inl he))
  have hjb : j ≠ b := fun he ↦ hjn (mem_insert_of_mem (mem_insert.mpr (Or.inl he)))
  have hja : j ≠ a := fun he ↦ hjn (mem_insert_of_mem (mem_insert_of_mem (mem_singleton.mpr he)))
  have hold := retained_after_first_swap p q s hblocks hj hjt
  exact ⟨j, hold.1, hold.2, hjb, hja, hj, hheavy⟩

end Erdos577.FullRow
