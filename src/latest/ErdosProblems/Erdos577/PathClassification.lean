import ErdosProblems.Erdos577.PathClassFinite
import ErdosProblems.Erdos577.PathClassPatterns
import ErdosProblems.Erdos577.PathCliqueReduction

/-! Wang's full path-block classification, with actual cycle and replacement conclusions. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem path_clique_classification (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    ScoredExchange G (p.support ∪ q.support) 6 ∨ PathBlock.Classified p q := by
  have hf := PathClass.finite_classification (PathExchange.encoded p q)
    (by rw [PathExchange.crossCount_encoded]; exact hheavy)
  rcases hf with hp | hc
  · exact Or.inl (hp.transport p q hd hq)
  · exact Or.inr (hc.transport p q hd hq)

/-- The complete version of Wang 3.5. In the exceptional case the path
is reversed at most once, the block is cyclically relabeled, all source
common-neighbor replacements hold, and a five-edge triangle reduction exists. -/
theorem path_block_classification (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hheavy : 9 ≤ contacts G p.support q.support)
    (hn : ¬LocalFactor G (p.support ∪ q.support))
    (hopt : ¬PathReduction G (p.support ∪ q.support) (edgeCount G q.support + 1)) :
    TriangleReduction G (p.support ∪ q.support) (edgeCount G q.support) ∨
      (G.IsNClique 4 q.support ∧ PathBlock.Classified p q ∧
        TriangleReduction G (p.support ∪ q.support) 5) := by
  rcases path_triangle_or_complete p q hd hheavy hn hopt with ht | hq
  · exact Or.inl ht
  · have he : edgeCount G q.support = 6 := by
      rw [edgeCount_clique hq.isClique, q.card_support]
      decide +kernel
    rcases path_clique_classification p q hd hq hheavy with (hf | ht) | hc
    · exact False.elim (hn hf)
    · left
      rw [he]
      exact ht
    · right
      refine ⟨hq, hc, ?_⟩
      have hex := path_scored_exchange p q hd hheavy
      rw [he] at hex
      rcases hex with hf | ht
      · exact False.elim (hn hf)
      · exact ht

end Erdos577
