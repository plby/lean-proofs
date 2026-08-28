import ErdosProblems.Erdos577.FullLeafCoreChoice

/-! TeX9.71: full-leaf core restrictions and the actual maximum-preserving interchange. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.preparation {c : TriangleChain G} {p : Paw G}
    {s a : Finset V} {y : V} (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    degreeIn G p.center s = 0 ∧ degreeIn G (p.vertices 2) s ≤ 1 ∧
      degreeIn G (p.vertices 3) s ≤ 1 := by
  have hpos : 0 < degreeIn G (p.vertices 2) s :=
    card_pos.mpr ⟨y, mem_filter.mpr ⟨h.exposed, h.attached⟩⟩
  obtain ⟨hr, hb, hc, _⟩ := h.feasible.full_leaf_preparation hcard hdeg hn p h.paw h.first
    h.full (by omega)
  exact ⟨hr, hb, hc⟩

theorem Maximal.interchange {c : TriangleChain G} {p : Paw G}
    {s a : Finset V} {y : V} (h : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ (e : TriangleChain G) (p' : Paw G),
      Maximal e p' (insert p.leaf (s.erase y)) a p.leaf ∧ e.Strong ∧
      p'.leaf = y ∧ p'.center = p.vertices 2 ∧ p'.vertices 2 = p.center ∧
      p'.vertices 3 = p.vertices 3 ∧ p'.triangle = p.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      e.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase y)} := by
  obtain ⟨e, p', he, hstrong, hleaf, hcenter, hsecond, hthird, htri, hedge, hcomplete,
    hblocks, hscore⟩ := h.1.swapped_chain hcard hn
  exact ⟨e, p', h.transfer he hscore, hstrong, hleaf, hcenter, hsecond, hthird, htri,
    hedge, hcomplete, hblocks⟩

end Erdos577.FullLeafCore
