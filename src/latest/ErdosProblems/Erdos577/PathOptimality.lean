import ErdosProblems.Erdos577.PathLoss
import ErdosProblems.Erdos577.MatchingData
import ErdosProblems.Erdos577.RemainderSplice

/-! The global path bound supplies local optimality for a path partition at the upper score. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Feasible.no_path_improvement {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : FourPath G) (parts : BlockPartition G (univ \ p.support))
    (hscore : parts.weightSum (edgeCount G) = c.edgeScore + 1)
    {b : Finset V} (hb : b ∈ parts.blocks) :
    ¬PathReduction G (p.support ∪ b) (edgeCount G b + 1) := by
  rintro ⟨path, hpath, hquad, hgain⟩
  let newParts := parts.replaceRemainder b hb path.support hpath hquad
  have hbound := (hc.path_score_bound hcard hdeg hn path newParts).1
  have hid := parts.weightSum_replaceRemainder_add b hb path.support hpath hquad (edgeCount G)
  change newParts.weightSum (edgeCount G) + edgeCount G b = _ at hid
  omega

lemma Feasible.no_triangle_tie_at_path_upper_score {c : TriangleChain G} (hc : c.Feasible)
    (p : FourPath G) (parts : BlockPartition G (univ \ p.support))
    (hscore : parts.weightSum (edgeCount G) = c.edgeScore + 1)
    {b : Finset V} (hb : b ∈ parts.blocks) :
    ¬TriangleReduction G (p.support ∪ b) (edgeCount G b) := by
  rintro ⟨d, hd⟩
  have hid := parts.chainOfLocal_edgeScore b hb d
  have hmax := hc.edge_max (parts.chainOfLocal b hb d)
  omega

end Erdos577.TriangleChain
