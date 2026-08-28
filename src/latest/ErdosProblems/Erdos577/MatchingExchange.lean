import ErdosProblems.Erdos577.MatchingWitnesses
import ErdosProblems.Erdos577.MatchingTransport
import ErdosProblems.Erdos577.PathLoss
import ErdosProblems.Erdos577.RemainderCounts
import ErdosProblems.Erdos577.RemainderSplice

/-! Wang's matching exchange and the global matching-remainder edge-score bound. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem matching_scored_exchange (p : TwoEdges G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : 9 ≤ contacts G p.support q.support) :
    ScoredExchange G (p.support ∪ q.support) 5 ∨ PathReduction G (p.support ∪ q.support) 6 := by
  have hf := MatchingExchange.finite_positive (MatchingExchange.encoded p q)
    (by rw [MatchingExchange.crossCount_encoded]; exact h)
  exact hf.transport p q hd

variable [Fintype V]

/-- A remainder containing two disjoint edges loses at most one edge in
comparison with the feasible triangle-chain score. -/
theorem TriangleChain.Feasible.matching_score_bound {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : TwoEdges G) (parts : BlockPartition G (univ \ p.support)) :
    parts.weightSum (edgeCount G) ≤ c.edgeScore + 1 := by
  by_cases ht : TriangleIn G p.support
  · have he := hc.partition_score_le p.card_support parts ht
    omega
  · obtain ⟨b, hb, hheavy⟩ := parts.exists_heavy_block_of_four_remainder
      p.card_support hcard hdeg hn ht
    obtain ⟨q, hq⟩ := parts.quad b hb
    have hd : Disjoint p.support q.support := by
      rw [hq]
      apply disjoint_left.mpr
      intro v hv hvb
      exact (mem_sdiff.mp (parts.block_subset hb hvb)).2 hv
    have hex := matching_scored_exchange p q hd (by rw [hq]; exact hheavy)
    rw [hq] at hex
    rcases hex with (hfactor | ⟨d, hd⟩) | ⟨path, hpath, hnew, he6⟩
    · exact False.elim (hn (parts.hasPacking_of_local_factor hcard hb hfactor))
    · have hb6 := (parts.quad b hb).edgeCount_le_six
      exact (hc.one_edge_loss_bound parts hb d (by omega)).1
    · let newParts := parts.replaceRemainder b hb path.support hpath hnew
      have hid := parts.weightSum_replaceRemainder_add b hb path.support hpath hnew (edgeCount G)
      have hb6 := (parts.quad b hb).edgeCount_le_six
      have hbound := (hc.path_score_bound hcard hdeg hn path newParts).1
      change newParts.weightSum (edgeCount G) + edgeCount G b = _ at hid
      omega

end Erdos577
