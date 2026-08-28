import ErdosProblems.Erdos577.LargeLeafCoreLabels

/-! Exact ordered full-leaf counts and the five-row average that supplies a dense core. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem ordered_full_two_counts {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hb : 2 ≤ degreeIn G (p.vertices 2) s) :
    degreeIn G (p.vertices 2) s = 2 ∧ degreeIn G (p.vertices 3) s = 0 ∧
      degreeIn G p.center s = 0 := by
  have hsum := TwoExposed.large_leaf_weighted_le_six hc hcard hdeg hn p hp hs (by omega)
  have hr : degreeIn G p.center s = 0 := by
    by_contra hpos
    have hbound := (hc.claim_two_three hcard hdeg hn p hp hs hfull (by omega)).1
    omega
  exact ⟨by omega, by omega, hr⟩

theorem noncentral_link {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hlarge : 3 ≤ degreeIn G p.leaf s) (z : V) (hz : z ∈ s)
    (hadj : G.Adj z (p.vertices 2) ∨ G.Adj z (p.vertices 3)) :
    degreeIn G z {p.vertices 2, p.vertices 3} = 1 := by
  have hbound := JointClaims.triangle_column_le_one hc hcard hn p hp hs hlarge z hz
  have hsub : ({p.vertices 2, p.vertices 3} : Finset V) ⊆ p.triangle := subset_insert _ _
  have hle := (degreeIn_mono G z hsub).trans hbound
  have hpos : 0 < degreeIn G z {p.vertices 2, p.vertices 3} := by
    apply card_pos.mpr
    rcases hadj with hh | hh
    · exact ⟨p.vertices 2, mem_filter.mpr ⟨by simp, hh⟩⟩
    · exact ⟨p.vertices 3, mem_filter.mpr ⟨by simp, hh⟩⟩
  omega

theorem full_dense_from_noncentral {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hr : degreeIn G p.center s = 0)
    (z : V) (hz : z ∈ s) (hadj : G.Adj z (p.vertices 2) ∨ G.Adj z (p.vertices 3)) :
    ∃ a ∈ c.blocks, a ≠ s ∧ 11 ≤ contacts G p.triangle a := by
  have hcl := FullRow.full_leaf_clique hc p hp hs hfull
  have hFS : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hzout : z ∉ p.support := fun hh ↦ disjoint_left.mp hFS hh hz
  have hfive : (insert z p.support).card = 5 := by
    rw [card_insert_of_notMem hzout, p.card_support]
  have hsum := TwoExposed.large_leaf_weighted_le_six hc hcard hdeg hn p hp hs (by omega)
  have hFF : contacts G p.support p.support = 8 := by
    rw [contacts_self_eq_twice_edgeCount G,
      p.edgeCount_of_no_quad (by rw [hp]; exact c.no_quad_remainder hcard hn)]
  have hFQ : contacts G p.support s ≤ 6 := by
    rw [p.contacts_support, p.contacts_triangle]
    change degreeIn G p.leaf s + (degreeIn G p.center s +
      (degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)) ≤ 6
    omega
  have hzT := JointClaims.triangle_column_le_one hc hcard hn p hp hs (by omega) z hz
  have hzF : degreeIn G z p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G z p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hzS : degreeIn G z s = 3 := by
    rw [degreeIn_clique G hcl.isClique hz, hcl.card_eq]
  have hinside : contacts G (insert z p.support) (c.remainder ∪ s) ≤ 19 := by
    rw [← hp, contacts, sum_insert hzout]
    change degreeIn G z (p.support ∪ s) + contacts G p.support (p.support ∪ s) ≤ 19
    rw [degreeIn_union G z hFS, contacts_union_right G _ hFS]
    omega
  obtain ⟨a, ha, has, hweight⟩ := c.exists_eleven_contact_outside_core
    hcard hdeg hs (insert z p.support) hfive hinside
  have hlink := noncentral_link hc hcard hn p hp hs (by omega) z hz hadj
  have hroute := FullRow.full_leaf_replacement hc p hp hs hfull z hz
  exact ⟨a, ha, has,
    (hc.leaf_transport hcard hdeg hn p hp hs ha has z hz hlink hweight (Or.inl hroute)).2.2⟩

end Erdos577.LargeLeaf
