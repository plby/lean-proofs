import ErdosProblems.Erdos577.LargeLeafThreeCompatible

/-! The two diagonal arguments and the final split-row two-cycle factor. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_no_compatible_clique {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hthree : degreeIn G p.leaf q.support = 3)
    (hrow : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hb : 2 ≤ degreeIn G (p.vertices 2) q.support)
    (hno : ∀ z ∈ q.support, QuadOn G (insert p.leaf (q.support.erase z)) →
      edgeCount G (insert p.leaf (q.support.erase z)) = edgeCount G q.support →
      ¬QuadOn G (insert (p.vertices 2) (q.support.erase z))) :
    G.IsNClique 4 q.support ∧ degreeIn G (p.vertices 2) q.support = 2 ∧
      G.Adj (p.vertices 2) (q 3) := by
  have hFS : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hout (i : Fin 4) : p.vertices i ∉ q.support := fun hh ↦ disjoint_left.mp hFS
    ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) hh
  have hfirst := FullRow.first_replacement hc p hp hs q hq hrow
  have hnotlast := hno (q 3) (hm 3) hfirst.1 hfirst.2
  have hd13 := FullRow.last_diagonal hc p hp hs q hq hrow
  have hnot : ¬(G.Adj (p.vertices 2) (q 0) ∧ G.Adj (p.vertices 2) (q 2)) := by
    rintro ⟨h0, h2⟩
    exact hnotlast (q.replace_using_path (p.vertices 2) (hout 2) 3 0 1 2 (by decide)
      (by decide) h0 (q.adjacent 0) (q.adjacent 1) h2)
  have hd02 : G.Adj (q 0) (q 2) := by
    by_contra hh
    obtain ⟨i, hi, hrep⟩ := two_contact_low_replacement q (p.vertices 2) (hout 2) hd13 hb hnot
    have hxrep := three_leaf_low_replacement q p.leaf (hout 0) hthree hrow hd13 hh i hi
    exact hno (q i) (hm i) hxrep.1 hxrep.2 hrep
  have hcl := q.clique_of_diagonals hd02 hd13
  have hsmall : degreeIn G (p.vertices 2) (q.support.erase (q 3)) ≤ 1 := by
    by_contra hh
    exact hnotlast ((clique_replace_iff_two_contacts hcl (hout 2) (hm 3)).mpr (by omega))
  have herase := degreeIn_erase_add G (p.vertices 2) (q 3) (hm 3)
  have hb3 : G.Adj (p.vertices 2) (q 3) := by
    by_contra hh
    rw [if_neg hh] at herase
    omega
  rw [if_pos hb3] at herase
  exact ⟨hcl, by omega, hb3⟩

theorem three_no_compatible_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hthree : degreeIn G p.leaf q.support = 3)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support)
    (hb : 2 ≤ degreeIn G (p.vertices 2) q.support)
    (hno : ∀ z ∈ q.support, QuadOn G (insert p.leaf (q.support.erase z)) →
      edgeCount G (insert p.leaf (q.support.erase z)) = edgeCount G q.support →
      ¬QuadOn G (insert (p.vertices 2) (q.support.erase z))) : False := by
  obtain ⟨hcl, hb2, hb3⟩ := three_no_compatible_clique hc p hp hs q hq hthree
    (fun i hi ↦ (hrow i).mpr hi) hb hno
  have hsum := TwoExposed.large_leaf_weighted_le_six hc hcard hdeg hn p hp hs
    (by rw [← hq]; omega)
  rw [← hq] at hsum
  have hc1 : degreeIn G (p.vertices 3) q.support = 1 := by omega
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (q.support.filter (G.Adj (p.vertices 3))).card by
    change 0 < degreeIn G (p.vertices 3) q.support
    omega)
  obtain ⟨hv, hcv⟩ := mem_filter.mp hv
  have hcol := JointClaims.triangle_column_le_one hc hcard hn p hp hs
    (by rw [← hq]; omega) v (hq ▸ hv)
  have hbnot := (JointClaims.third_neighbor_noncontacts p v hcol hcv).2
  have hv3 : v ≠ q 3 := by
    intro hh
    exact hbnot (hh.symm ▸ hb3)
  obtain ⟨i, hi⟩ := (q.mem_support v).mp hv
  have hxi : G.Adj p.leaf v := by
    rw [← hi]
    apply (hrow i).mpr
    intro hh
    exact hv3 (hi.symm.trans (congrArg q hh))
  have hbout : p.vertices 2 ∉ q.support := fun hh ↦
    disjoint_left.mp ((c.presentPaw p hp).triangle_disjoint_block hs)
      (show p.vertices 2 ∈ p.triangle by simp [Paw.triangle]) (hq ▸ hh)
  have hrep := JointClaims.clique_replace_nonadjacent hcl (p.vertices 2) v hbout hv hb hbnot
  apply JointClaims.third_common_false hcard hn p hp hs
  rw [← hq]
  exact ⟨v, hv, hxi, hcv, hrep⟩

end Erdos577.LargeLeaf
