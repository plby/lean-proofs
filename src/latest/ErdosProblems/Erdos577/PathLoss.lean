import ErdosProblems.Erdos577.PathLossWitnesses1
import ErdosProblems.Erdos577.PathLossWitnesses2
import ErdosProblems.Erdos577.PathLossWitnesses3
import ErdosProblems.Erdos577.PathLossTransport
import ErdosProblems.Erdos577.LocalScoreBounds

/-! The bounded-loss path exchange and both global path-remainder score bounds. -/

namespace Erdos577

open Finset

namespace PathLoss

theorem finite_positive (diagonal : Fin 4) (m : Fin 65536)
    (h : 9 ≤ PathExchange.crossCount m.val) : Positive diagonal m.val := by
  fin_cases diagonal
  · exact finite_zero m h
  · exact D1.finite_positive m h
  · exact D2.finite_positive m h
  · exact D3.finite_positive m h

end PathLoss

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem path_scored_exchange (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : 9 ≤ contacts G p.support q.support) :
    ScoredExchange G (p.support ∪ q.support) (min (edgeCount G q.support) 5) := by
  have hf := PathLoss.finite_positive (Unattached.diagonal q) (PathExchange.encoded p q)
    (by rw [PathExchange.crossCount_encoded]; exact h)
  exact hf.transport p q hd

variable [Fintype V]

/-- Every path-remainder partition is bounded by the feasible triangle
scores plus (1,1), in lexicographic order. No extra maximum is assumed. -/
theorem TriangleChain.Feasible.path_score_bound {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : FourPath G) (parts : BlockPartition G (univ \ p.support)) :
    parts.weightSum (edgeCount G) ≤ c.edgeScore + 1 ∧
      (parts.weightSum (edgeCount G) = c.edgeScore + 1 →
        parts.weightSum (fun b ↦ if edgeCount G b = 6 then 1 else 0) ≤ c.completeScore + 1) := by
  by_cases ht : TriangleIn G p.support
  · have he := hc.partition_score_le p.card_support parts ht
    exact ⟨by omega, fun h ↦ False.elim (by omega)⟩
  · obtain ⟨b, hb, hheavy⟩ := BlockPartition.exists_path_heavy_block p parts hcard hdeg hn ht
    obtain ⟨q, hq⟩ := parts.quad b hb
    have hd : Disjoint p.support q.support := by
      rw [hq]
      apply disjoint_left.mpr
      intro v hv hvb
      exact (mem_sdiff.mp (parts.block_subset hb hvb)).2 hv
    have hex := path_scored_exchange p q hd (by rw [hq]; exact hheavy)
    rw [hq] at hex
    rcases hex with hfactor | ⟨d, hd⟩
    · exact False.elim (hn (parts.hasPacking_of_local_factor hcard hb hfactor))
    · exact hc.min_five_reduction_bound parts hb d hd

end Erdos577
