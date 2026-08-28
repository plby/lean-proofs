import ErdosProblems.Erdos577.PathTransfer

/-! TeX9.43: the path-score transfer applies to any whole partition at the upper score. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Feasible.global_path_transfer {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : FourPath G) (parts : BlockPartition G (univ \ p.support))
    (hscore : parts.weightSum (edgeCount G) = c.edgeScore + 1)
    {a : Finset V} (ha : a ∈ parts.blocks) :
    ¬LocalFactor G (p.support ∪ a) ∧
      ¬TriangleReduction G (p.support ∪ a) (edgeCount G a) ∧
      ¬PathReduction G (p.support ∪ a) (edgeCount G a + 1) ∧
      ∀ q : Quadrilateral G, q.support = a → 9 ≤ contacts G p.support q.support →
        G.IsNClique 4 q.support ∧ PathBlock.Classified p q ∧
          TriangleReduction G (p.support ∪ q.support) 5 := by
  refine ⟨?_, hc.no_triangle_tie_at_path_upper_score p parts hscore ha,
    hc.no_path_improvement hcard hdeg hn p parts hscore ha, ?_⟩
  · exact fun h ↦ hn (parts.hasPacking_of_local_factor hcard ha h)
  · intro q hq hheavy
    exact hc.classification_at_path_upper_score hcard hdeg hn p parts hscore ha q hq hheavy

end Erdos577.TriangleChain
