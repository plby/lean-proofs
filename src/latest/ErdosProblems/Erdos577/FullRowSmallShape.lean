import ErdosProblems.Erdos577.FullRowDenseExcluded

/-! Expose a full-block vertex to obtain the common replacement in the small-paw case. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_vertex_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hxfull : degreeIn G p.leaf a = 4)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (u : V) (hu : u ∈ a) (hrow : 3 ≤ degreeIn G u j) (w : V) (hw : w ∈ j) :
    QuadOn G (insert u (j.erase w)) := by
  obtain ⟨e, he, ht, _, _, _, hblocks⟩ := exists_full_leaf_swap hc p hp ha hxfull u hu
  have hje : j ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)
  have hh := he.terminal_universal_replace hje (by rw [ht]; exact hrow) hw
  rwa [ht] at hh

theorem full_vertex_triangle_column {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hxfull : degreeIn G p.leaf a = 4)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (u : V) (hu : u ∈ a) (hrow : 3 ≤ degreeIn G u j) (w : V) (hw : w ∈ j) :
    degreeIn G w p.triangle ≤ 1 := by
  obtain ⟨e, he, ht, hT, _, _, hblocks⟩ := exists_full_leaf_swap hc p hp ha hxfull u hu
  have hje : j ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)
  have hrep := he.terminal_universal_replace hje (by rw [ht]; exact hrow) hw
  have hh := (e.replaceBlock j hje (e.swapTerminal hje hw hrep)).terminal_degree_le_one hcard hn
  change degreeIn G w e.triangle ≤ 1 at hh
  rwa [hT] at hh

theorem full_vertex_triangle_total {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hxfull : degreeIn G p.leaf a = 4)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (u : V) (hu : u ∈ a) (hrow : 3 ≤ degreeIn G u j) : contacts G p.triangle j ≤ 4 := by
  rw [contacts_comm]
  calc
    contacts G j p.triangle ≤ ∑ _ ∈ j, 1 := sum_le_sum fun w hw ↦
      full_vertex_triangle_column hc hcard hn p hp ha hxfull hj hja u hu hrow w hw
    _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, (c.property.blocks_quad j hj).card]

theorem small_common_replacement {c d : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hsmall : contacts G d.remainder j ≤ 8) :
    ∃ i l : Fin 4, ((i = 1 ∧ l = 3) ∨ (i = 3 ∧ l = 1)) ∧
      CommonReplacement G d.terminal (v l) (v i) j := by
  have hrows := CoreTransfer.rows_contacts d v (hv.symm ▸ had) j
  obtain ⟨i, l, hpair, hrow⟩ : ∃ i l : Fin 4,
      ((i = 1 ∧ l = 3) ∨ (i = 3 ∧ l = 1)) ∧ 3 ≤ degreeIn G (v i) j := by
    by_cases hh : 3 ≤ degreeIn G (v 1) j
    · exact ⟨1, 3, Or.inl ⟨rfl, rfl⟩, hh⟩
    · exact ⟨3, 1, Or.inr ⟨rfl, rfl⟩, by omega⟩
  have hiA : v i ∈ a := hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩
  have htri := full_vertex_triangle_total hc hcard hn p hp ha hxfull hj hja (v i) hiA hrow
  have hrem := CoreTransfer.remainder_contacts d j
  rw [hT] at hrem
  have hsum : degreeIn G (v i) j + degreeIn G (v l) j =
      degreeIn G (v 1) j + degreeIn G (v 3) j := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · omega
  have hfour := degreeIn_le_card G (v i) j
  rw [(c.property.blocks_quad j hj).card] at hfour
  have hbound : (j.filter (G.Adj d.terminal) ∪ j.filter (G.Adj (v l))).card ≤ 4 := by
    calc
      _ ≤ j.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = 4 := (c.property.blocks_quad j hj).card
  obtain ⟨w, hw, htw, hlw⟩ := common_neighbor_of_union_bound d.terminal (v l) j 4 hbound
    (by omega)
  exact ⟨i, l, hpair, w, hw, htw, hlw,
    full_vertex_universal hc p hp ha hxfull hj hja (v i) hiA hrow w hw⟩

end Erdos577.FullRow
