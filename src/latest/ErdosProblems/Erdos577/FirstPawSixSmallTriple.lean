import ErdosProblems.Erdos577.FirstPawSixSmallRows
import ErdosProblems.Erdos577.SmallLeafClassification
import ErdosProblems.Erdos577.CommonTriple

/-! The common-triple lemma applies to the first alternate paw in cases (22)/(23). -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_triple {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a) :
    ∃ v : Quadrilateral G, v.support = a ∧
      (∀ j : Fin 4, j ≠ 0 → G.Adj p.leaf (v j) ∧ G.Adj (q 1) (v j)) ∧
      G.Adj (p.vertices 3) (v 2) := by
  have hx : degreeIn G (p.vertices 3) a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd hdiag variant hrows ha hab hheavy true
  have hy : degreeIn G (q 3) a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd hdiag variant hrows ha hab hheavy false
  obtain ⟨d, hdf, _, hp', hkeep⟩ :=
    FirstPawSix.exists_alternate hc p hp hb q hq hd hdiag (index variant) hrows false
  let p' := alternatePaw p q hd hdiag (index variant) hrows false
  have ha' : a ∈ d.blocks := hkeep a ha hab
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hd' : Disjoint p'.support v.support := by
    rw [hp', hv]
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (d.complementPartition.block_subset ha' hua)).2 hu
  have hz : p.vertices 3 ∉ p'.support ∪ v.support := by
    intro hz
    rcases mem_union.mp hz with hz | hz
    · exact other_terminal_not_alternate p q hd hdiag (index variant) hrows false hz
    · have hm : p.vertices 3 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hv ▸ hz))).2 hm
  have hno : ¬CommonReplacement G (p'.vertices 2) (p'.vertices 3) (p.vertices 3) v.support := by
    rw [hv]
    exact no_common_replacement hcard hn p hp hb q hq hd hdiag variant hrows ha hab 1
  have hgain : ¬TwoEdgeReduction G (p'.support ∪ v.support) (edgeCount G v.support + 2) := by
    rw [hp', hv]
    exact hdf.no_two_edge_gain hcard hdeg hn ha'
  have hsmall : degreeIn G p'.leaf v.support ≤ 2 := by rw [hv]; exact hy
  have hthree : 7 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support := by
    rw [hv]
    change 7 ≤ degreeIn G (q 3) a + degreeIn G p.leaf a + degreeIn G (q 1) a
    rw [rows_contacts] at hheavy
    omega
  have hfour : 9 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support + degreeIn G (p.vertices 3) v.support := by
    rw [hv]
    exact (rows_contacts p q hd a) ▸ hheavy
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
  obtain ⟨_, v', hv', htriple, hzv⟩ :=
    p'.common_triple v hd' (p.vertices 3) hz hno hgain hfour hcases
  exact ⟨v', hv'.trans hv, htriple, hzv⟩

end Erdos577.FirstPawSix.SmallCases
