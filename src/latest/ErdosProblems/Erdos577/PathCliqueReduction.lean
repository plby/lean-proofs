import ErdosProblems.Erdos577.MatchingExchange
import ErdosProblems.Erdos577.PathOptimality

/-! Local path optimality reduces the path classification to a complete old block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem path_triangle_or_complete (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hheavy : 9 ≤ contacts G p.support q.support)
    (hn : ¬LocalFactor G (p.support ∪ q.support))
    (hopt : ¬PathReduction G (p.support ∪ q.support) (edgeCount G q.support + 1)) :
    TriangleReduction G (p.support ∪ q.support) (edgeCount G q.support) ∨
      G.IsNClique 4 q.support := by
  by_cases hq5 : edgeCount G q.support ≤ 5
  · have hex := matching_scored_exchange (TwoEdges.ofPath p) q
      (by simpa only [TwoEdges.ofPath_support] using hd)
      (by simpa only [TwoEdges.ofPath_support] using hheavy)
    simp only [TwoEdges.ofPath_support] at hex
    rcases hex with (hfactor | ⟨d, hd⟩) | ⟨path, hp, hq, he⟩
    · exact False.elim (hn hfactor)
    · exact Or.inl ⟨d, hq5.trans hd⟩
    · exact False.elim (hopt ⟨path, hp, hq, by omega⟩)
  · have hq6 := (show QuadOn G q.support from ⟨q, rfl⟩).edgeCount_le_six
    exact Or.inr (clique_of_four_six q.card_support (by omega))

variable [Fintype V]

theorem TriangleChain.Feasible.complete_heavy_block_at_path_upper_score
    {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : FourPath G) (parts : BlockPartition G (univ \ p.support))
    (hscore : parts.weightSum (edgeCount G) = c.edgeScore + 1)
    {b : Finset V} (hb : b ∈ parts.blocks) (hheavy : 9 ≤ contacts G p.support b) :
    G.IsNClique 4 b := by
  obtain ⟨q, hq⟩ := parts.quad b hb
  have hd : Disjoint p.support q.support := by
    rw [hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (parts.block_subset hb hvb)).2 hv
  have hnlocal : ¬LocalFactor G (p.support ∪ q.support) := by
    rw [hq]
    exact fun h ↦ hn (parts.hasPacking_of_local_factor hcard hb h)
  have hopt : ¬PathReduction G (p.support ∪ q.support) (edgeCount G q.support + 1) := by
    rw [hq]
    exact hc.no_path_improvement hcard hdeg hn p parts hscore hb
  rcases path_triangle_or_complete p q hd (by rw [hq]; exact hheavy) hnlocal hopt with ht | hcq
  · rw [hq] at ht
    exact False.elim (hc.no_triangle_tie_at_path_upper_score p parts hscore hb ht)
  · exact hq ▸ hcq

end Erdos577
