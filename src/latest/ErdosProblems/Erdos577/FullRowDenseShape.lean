import ErdosProblems.Erdos577.FullRowHeavy
import ErdosProblems.Erdos577.CoreReplacementFactor
import ErdosProblems.Erdos577.DenseOutside

/-! The dense heavy block has no new-leaf contacts and at least eleven triangle contacts. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_terminal_zero {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hdense : 9 ≤ contacts G d.remainder j) : degreeIn G d.terminal j = 0 := by
  obtain ⟨r, hrx, hrT, hr⟩ := hd.exists_paw
  obtain ⟨q, hq⟩ := d.property.blocks_quad j hjd
  have hclass := hd.toFeasible.claim_two_two hcard hdeg hn r hr hjd q hq
    (by rw [hr, hq]; exact hdense)
  rcases hclass with hz | ⟨w, hw, hpat⟩
  · rwa [hrx, hq] at hz
  · have hws : w.support = j := hw.trans hq
    have hnine := (PawBlock.surviving_counts r w (Or.inl hpat)).2
    rw [hr, hws] at hnine
    have hrows := CoreTransfer.rows_contacts d v (hv.symm ▸ had) j
    obtain ⟨i, hi, hrow⟩ : ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ 2 ≤ degreeIn G (v i) j := by
      by_cases hh : 2 ≤ degreeIn G (v 1) j
      · exact ⟨1, Or.inl rfl, hh⟩
      · exact ⟨3, Or.inr rfl, by omega⟩
    have hu : v i ∈ a := hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩
    have hdis : Disjoint r.support w.support := by
      rw [hr, hws]
      exact d.property.remainder_disjoint.mono_right (d.blockPartition.block_subset hjd)
    have hout : v i ∉ r.support ∪ w.support := by
      rw [hr, hws]
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact (mem_sdiff.mp (d.complementPartition.block_subset had hu)).2 hh
      · exact disjoint_left.mp (c.property.blocks_disjoint ha hj hja.symm) hu hh
    have hf := hpat.outside_factor r w hdis (v i) hout (by rw [hws]; exact hrow)
    rw [hrT, hT, hws] at hf
    have hrep := (full_leaf_replacement hc p hp ha hxfull (v i) hu).1
    exact False.elim (hn ((c.presentPaw p hp).hasPacking_of_core_replacement
      hcard ha hj hja.symm hu hf hrep))

theorem full_vertex_dense_row {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hxfull : degreeIn G p.leaf a = 4)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (hdense : 9 ≤ contacts G p.triangle j) (u : V) (hu : u ∈ a) :
    degreeIn G u j ≤ 1 := by
  obtain ⟨e, he, ht, hT, _, _, hblocks⟩ := exists_full_leaf_swap hc p hp ha hxfull u hu
  have hje : j ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)
  have hh := he.terminal_degree_le_one_of_dense hcard hn hje (by rw [hT]; exact hdense)
  rwa [ht] at hh

theorem dense_shape {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hdense : 9 ≤ contacts G d.remainder j) :
    degreeIn G d.terminal j = 0 ∧ 11 ≤ contacts G p.triangle j ∧
      degreeIn G (v 1) j ≤ 1 ∧ degreeIn G (v 3) j ≤ 1 ∧ G.IsNClique 4 j ∧
      ∀ u ∈ p.triangle, ∀ w ∈ j, QuadOn G (insert u (j.erase w)) := by
  have hzero := dense_terminal_zero hc hd hcard hdeg hn p hp hT ha had hxfull v hv
    hj hjd hja hheavy hdense
  have hrem := CoreTransfer.remainder_contacts d j
  rw [hzero, hT, zero_add] at hrem
  have htri : 9 ≤ contacts G p.triangle j := by omega
  have h1 := full_vertex_dense_row hc hcard hn p hp ha hxfull hj hja htri (v 1)
    (hv ▸ (v.mem_support _).mpr ⟨1, rfl⟩)
  have h3 := full_vertex_dense_row hc hcard hn p hp ha hxfull hj hja htri (v 3)
    (hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩)
  have hrows := CoreTransfer.rows_contacts d v (hv.symm ▸ had) j
  have h11 : 11 ≤ contacts G p.triangle j := by omega
  have hreplace := (hc.presentPaw_feasible p hp).all_triangle_universal_replacements hj h11
  exact ⟨hzero, h11, h1, h3, hreplace⟩

end Erdos577.FullRow
