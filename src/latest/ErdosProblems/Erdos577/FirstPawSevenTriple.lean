import ErdosProblems.Erdos577.FirstPawSevenRows
import ErdosProblems.Erdos577.SmallLeafClassification
import ErdosProblems.Erdos577.CommonTriple

/-! All hypotheses of the common-triple lemma hold for the actual alternate paw. -/

namespace Erdos577.FirstPawSeven

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_triple {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a) :
    ∃ v : Quadrilateral G, v.support = a ∧
      (∀ j : Fin 4, j ≠ 0 → G.Adj (q 1) (v j) ∧ G.Adj (p.vertices 2) (v j)) ∧
      G.Adj p.leaf (v 2) := by
  have hx : degreeIn G p.leaf a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd h ha hab hheavy false
  have hy : degreeIn G (q 3) a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd h ha hab hheavy true
  obtain ⟨d, hdf, _, hp', hkeep⟩ := exists_alternate hc p hp hb q hq hd h
  let p' := swappedPaw p q hd h
  have ha' : a ∈ d.blocks := hkeep a ha hab
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hd' : Disjoint p'.support v.support := by
    rw [hp', hv]
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (d.complementPartition.block_subset ha' hua)).2 hu
  have hz : p.leaf ∉ p'.support ∪ v.support := by
    intro hz
    rcases mem_union.mp hz with hz | hz
    · exact original_leaf_not_swapped p q hd h hz
    · have hm : p.leaf ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hv ▸ hz))).2 hm
  have hno : ¬CommonReplacement G (p'.vertices 2) (p'.vertices 3) p.leaf v.support := by
    rw [hv]
    exact no_common_replacement hcard hn p hp hb q hq hd h ha hab 2
  have hgain : ¬TwoEdgeReduction G (p'.support ∪ v.support) (edgeCount G v.support + 2) := by
    rw [hp', hv]
    exact hdf.no_two_edge_gain hcard hdeg hn ha'
  have hsmall : degreeIn G p'.leaf v.support ≤ 2 := by rw [hv]; exact hy
  have hthree : 7 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support := by
    rw [hv]
    change 7 ≤ degreeIn G (q 3) a + degreeIn G (q 1) a + degreeIn G (p.vertices 2) a
    rw [rows_contacts] at hheavy
    omega
  have hfour : 9 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support + degreeIn G p.leaf v.support := by
    rw [hv]
    change 9 ≤ degreeIn G (q 3) a + degreeIn G (q 1) a + degreeIn G (p.vertices 2) a +
      degreeIn G p.leaf a
    rw [rows_contacts] at hheavy
    omega
  have hcases :
      (degreeIn G p'.leaf v.support = 1 ∧ degreeIn G (p'.vertices 2) v.support = 3 ∧
        ∀ u ∈ v.support, G.Adj (p'.vertices 2) u ↔ G.Adj (p'.vertices 3) u) ∨
      (degreeIn G p'.leaf v.support = 0 ∧
        7 ≤ degreeIn G (p'.vertices 2) v.support + degreeIn G (p'.vertices 3) v.support) := by
    by_cases hzero : degreeIn G p'.leaf v.support = 0
    · exact Or.inr ⟨hzero, by omega⟩
    · obtain ⟨hl, s, _, hs3, hbset, hcset⟩ := hdf.small_leaf_precise hcard hdeg hn
        p' hp' ha' v hv hsmall (by omega) hthree
      refine Or.inl ⟨hl, ?_, ?_⟩
      · change (v.support.filter (G.Adj (p'.vertices 2))).card = 3
        rw [hbset, hs3]
      · intro u hu
        have he : u ∈ v.support.filter (G.Adj (p'.vertices 2)) ↔
            u ∈ v.support.filter (G.Adj (p'.vertices 3)) := by rw [hbset, hcset]
        simpa only [mem_filter, hu, true_and] using he
  obtain ⟨_, v', hv', hrows, hxv⟩ := p'.common_triple v hd' p.leaf hz hno hgain hfour hcases
  exact ⟨v', hv'.trans hv, hrows, hxv⟩

end Erdos577.FirstPawSeven
