import ErdosProblems.Erdos577.LargeLeafThreeColumns

/-! An occupied low column forces the remaining diagonal, hence a complete first block. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_complete_of_labels {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3) : G.IsNClique 4 q.support := by
  have hrows := three_union_rows hc hcard hdeg hn p hp hs hthree hnon q hq hrow
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hd13 := FullRow.last_diagonal hc p hp hs q hq (fun i hi ↦ (hrow i).mpr hi)
  have hd02 : G.Adj (q 0) (q 2) := by
    by_contra hh
    have hxout : p.leaf ∉ q.support := fun hm ↦ disjoint_left.mp hFQ
      (p.support_eq ▸ mem_insert_self _ _) hm
    have hrep := three_leaf_low_replacement q p.leaf hxout (by rwa [hq])
      (fun i hi ↦ (hrow i).mpr hi) hd13 hh 0 (Or.inl rfl)
    rw [hq] at hrep
    have hm : q 0 ∈ s := hq ▸ (q.mem_support _).mpr ⟨0, rfl⟩
    have hoccupied : G.Adj (q 0) (p.vertices 2) ∨ G.Adj (q 0) (p.vertices 3) := by
      rcases (hrows 0).mpr (by decide) with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm
    have hbound := three_occupied_inside_ge_five hc hcard hdeg hn p hp hs hthree hnon
      (q 0) hm hoccupied hrep.1 hrep.2
    have hcol := JointClaims.triangle_column_le_one hc hcard hn p hp hs (by omega) (q 0) hm
    have hF : degreeIn G (q 0) p.support ≤ 2 := by
      rw [p.support_eq, degreeIn_insert G (q 0) p.leaf p.leaf_not_mem_triangle]
      split_ifs <;> omega
    have hQ : degreeIn G (q 0) q.support = 2 := by
      rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 0) (q 2) then 1 else 0) = 2
      rw [if_neg hh]
    rw [← hq, degreeIn_union G (q 0) hFQ] at hbound
    omega
  exact q.clique_of_diagonals hd02 hd13

theorem three_preparation_ordered {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (hb : 2 ≤ degreeIn G (p.vertices 2) s) :
    G.IsNClique 4 s ∧ s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj p.leaf) ∧
      s.filter (G.Adj (p.vertices 3)) = ∅ := by
  obtain ⟨q0, hq0⟩ := c.property.blocks_quad s hs
  obtain ⟨q, hq, hrow⟩ := q0.exists_three_contact_labels p.leaf (by rwa [hq0])
  have hqs : q.support = s := hq.trans hq0
  have hrows := three_union_rows hc hcard hdeg hn p hp hs hthree hnon q hqs hrow
  have hcl := three_complete_of_labels hc hcard hdeg hn p hp hs hthree hnon q hqs hrow
  have hsum := three_noncentral_sum hc hcard hdeg hn p hp hs hthree hnon
  have hc0 : degreeIn G (p.vertices 3) s = 0 := by
    by_contra hh
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (s.filter (G.Adj (p.vertices 3))).card by
      change 0 < degreeIn G (p.vertices 3) s
      omega)
    obtain ⟨hv, hcv⟩ := mem_filter.mp hv
    obtain ⟨i, hi⟩ := (q.mem_support v).mp (hqs.symm ▸ hv)
    have hxi : G.Adj p.leaf v := by
      have hcqi : G.Adj (p.vertices 3) (q i) := hi.symm ▸ hcv
      exact hi ▸ (hrow i).mpr ((hrows i).mp (Or.inr hcqi))
    have hcol := JointClaims.triangle_column_le_one hc hcard hn p hp hs (by omega) v hv
    have hbnot := (JointClaims.third_neighbor_noncontacts p v hcol hcv).2
    have hbout : p.vertices 2 ∉ s := fun hm ↦
      disjoint_left.mp ((c.presentPaw p hp).triangle_disjoint_block hs)
        (show p.vertices 2 ∈ p.triangle by simp [Paw.triangle]) hm
    have hrep := JointClaims.clique_replace_nonadjacent (hqs ▸ hcl) (p.vertices 2) v
      hbout hv hb hbnot
    exact JointClaims.third_common_false hcard hn p hp hs ⟨v, hv, hxi, hcv, hrep⟩
  have hsub : s.filter (G.Adj (p.vertices 2)) ⊆ s.filter (G.Adj p.leaf) := by
    intro v hv
    obtain ⟨hv, hbv⟩ := mem_filter.mp hv
    obtain ⟨i, hi⟩ := (q.mem_support v).mp (hqs.symm ▸ hv)
    have hbqi : G.Adj (p.vertices 2) (q i) := hi.symm ▸ hbv
    exact mem_filter.mpr ⟨hv, hi ▸ (hrow i).mpr ((hrows i).mp (Or.inl hbqi))⟩
  have heq : s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj p.leaf) :=
    eq_of_subset_of_card_le hsub (by
      change degreeIn G p.leaf s ≤ degreeIn G (p.vertices 2) s
      omega)
  exact ⟨hqs ▸ hcl, heq, card_eq_zero.mp hc0⟩

end Erdos577.LargeLeaf
