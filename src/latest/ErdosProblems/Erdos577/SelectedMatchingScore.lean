import ErdosProblems.Erdos577.MatchingExchange
import ErdosProblems.Erdos577.MultiScores

/-! The global matching-remainder bound applies to any explicitly selected block exchange. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Feasible.selected_matching_edges_le {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) {u : Finset V} (q : BlockPartition G u)
    (hu : u ⊆ c.remainder ∪ bs.biUnion id) (p : TwoEdges G)
    (hp : p.support = (c.remainder ∪ bs.biUnion id) \ u) :
    q.weightSum (edgeCount G) ≤
      (c.complementPartition.select bs hbs).weightSum (edgeCount G) + 1 := by
  let spliced := c.complementPartition.splice bs hbs q hu
  let parts : BlockPartition G (univ \ p.support) := {
    blocks := spliced.blocks
    disjoint := spliced.disjoint
    cover := spliced.cover.trans (congrArg (fun s : Finset V ↦ univ \ s) hp.symm)
    quad := spliced.quad }
  have hbound := hc.matching_score_bound hcard hdeg hn p parts
  have he := c.complementPartition.weightSum_splice_add bs hbs q hu (edgeCount G)
  change parts.weightSum (edgeCount G) +
    (c.complementPartition.select bs hbs).weightSum (edgeCount G) =
      c.edgeScore + q.weightSum (edgeCount G) at he
  omega

end Erdos577.TriangleChain
