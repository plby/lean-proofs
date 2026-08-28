import ErdosProblems.Erdos577.FullRowFirstBlock

/-! Every vertex of a complete block reached by a full leaf row is an actual feasible terminal. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma unique_row_of_bound (s : Finset V) (x z : V) (hz : z ∈ s) (hxz : G.Adj x z)
    (hbound : degreeIn G x s ≤ 1) :
    degreeIn G x s = 1 ∧ ∀ u ∈ s, G.Adj x u ↔ u = z := by
  classical
  have hm : z ∈ s.filter (G.Adj x) := mem_filter.mpr ⟨hz, hxz⟩
  have he : ({z} : Finset V) = s.filter (G.Adj x) :=
    eq_of_subset_of_card_le (singleton_subset_iff.mpr hm)
      (by simpa only [card_singleton, degreeIn] using hbound)
  constructor
  · rw [degreeIn, ← he, card_singleton]
  · intro u hu
    constructor
    · intro hh
      exact mem_singleton.mp (he.symm ▸ mem_filter.mpr ⟨hu, hh⟩)
    · rintro rfl
      exact hxz

lemma full_row_outside {a : Finset V} (ha : QuadOn G a) (z : V)
    (hrow : degreeIn G z a = 4) : z ∉ a := by
  intro hz
  exact G.irrefl ((degreeIn_eq_card_iff z a).mp (hrow.trans ha.card.symm) z hz)

variable [Fintype V]

theorem full_leaf_clique {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4) :
    G.IsNClique 4 a := (hc.presentPaw_feasible p hp).clique_of_terminal_degree_four ha hrow

theorem full_leaf_replacement {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4) (u : V) (hu : u ∈ a) :
    QuadOn G (insert p.leaf (a.erase u)) ∧
      edgeCount G (insert p.leaf (a.erase u)) = edgeCount G a := by
  have hcl := full_leaf_clique hc p hp ha hrow
  have hout : p.leaf ∉ a := (c.presentPaw p hp).terminal_not_mem_block ha
  have hxu := (degreeIn_eq_card_iff p.leaf a).mp (hrow.trans hcl.card_eq.symm) u hu
  have hdu := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hdu
  have he := degreeIn_erase_add G p.leaf u hu
  rw [hrow, if_pos hxu] at he
  have hscore := edgeCount_replace G u p.leaf hu hout
  exact ⟨(c.property.blocks_quad a ha).replace_of_degree_four hout hrow hu, by omega⟩

theorem exists_full_leaf_swap {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4) (u : V) (hu : u ∈ a) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = u ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase a ∪ {insert p.leaf (a.erase u)} := by
  obtain ⟨hr, he⟩ := full_leaf_replacement hc p hp ha hrow u hu
  exact (hc.presentPaw_feasible p hp).exists_terminal_swap ha hu hr he

theorem full_column_triangle_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4) (u : V) (hu : u ∈ a) :
    degreeIn G u p.triangle ≤ 1 := by
  obtain ⟨d, _, ht, hT, _, _, _⟩ := exists_full_leaf_swap hc p hp ha hrow u hu
  have hh := d.terminal_degree_le_one hcard hn
  rwa [ht, hT] at hh

theorem full_column_core_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4)
    {b : Finset V} (hb : b ∈ c.blocks) (hba : b ≠ a)
    (hcore : ∀ v, v ∉ p.triangle ∪ b → 2 ≤ degreeIn G v (p.triangle ∪ b) →
      LocalFactor G (insert v (p.triangle ∪ b)))
    (u : V) (hu : u ∈ a) : degreeIn G u (p.triangle ∪ b) ≤ 1 := by
  obtain ⟨d, _, ht, hT, _, _, hblocks⟩ := exists_full_leaf_swap hc p hp ha hrow u hu
  have hb' : b ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hba, hb⟩)
  have hout : u ∉ p.triangle ∪ b := by
    intro hh
    rcases mem_union.mp hh with hT | hB
    · have hF : u ∈ p.support := p.support_eq ▸ mem_insert_of_mem hT
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha hu)).2 (hp ▸ hF)
    · exact disjoint_left.mp (c.property.blocks_disjoint ha hb hba.symm) hu hB
  by_contra! hh
  apply d.no_local_factor hcard hn hb'
  change LocalFactor G (insert d.terminal d.triangle ∪ b)
  rw [ht, hT, insert_union]
  exact hcore u hout (by omega)

end Erdos577.FullRow
