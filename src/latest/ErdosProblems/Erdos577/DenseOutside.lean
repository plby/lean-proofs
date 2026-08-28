import ErdosProblems.Erdos577.DenseOutsideWitnesses0
import ErdosProblems.Erdos577.DenseOutsideWitnesses1
import ErdosProblems.Erdos577.DenseOutsideWitnesses2
import ErdosProblems.Erdos577.DenseOutsideWitnesses3
import ErdosProblems.Erdos577.DenseOutsideTransport

/-! Wang 3.2 for every feasible chain, using only its edge-score maximum. -/

namespace Erdos577

open Finset

namespace DenseOutside

theorem finite_positive (diagonal : Fin 4) (m : Fin 65536)
    (hz : 2 ≤ terminalCount m.val) (ht : 9 ≤ triangleCount m.val) :
    Positive diagonal m.val := by
  fin_cases diagonal
  · exact D0.finite_positive m hz ht
  · exact D1.finite_positive m hz ht
  · exact D2.finite_positive m hz ht
  · exact D3.finite_positive m hz ht

end DenseOutside

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No attachment maximization is used: a strict gain contradicts feasibility. -/
theorem TriangleChain.Feasible.terminal_degree_le_one_of_dense
    {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (ht : 9 ≤ contacts G c.triangle b) :
    degreeIn G c.terminal b ≤ 1 := by
  by_contra hh
  have hz : 2 ≤ degreeIn G c.terminal b := by omega
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  have hd : Disjoint c.remainder q.support := by
    rw [hq]
    exact c.property.remainder_disjoint.mono le_rfl (c.blockPartition.block_subset hb)
  have hp := DenseOutside.finite_positive (Unattached.diagonal q) (Unattached.encoded c q)
    (by rw [DenseOutside.terminalCount_encoded, hq]; exact hz)
    (by rw [DenseOutside.triangleCount_encoded, hq]; exact ht)
  have hg := hp.chain_outcome c q hd
  rw [hq] at hg
  rcases hg with hfac | himp
  · exact c.no_local_factor hcard hn hb hfac
  · exact hc.no_strict_improvement hb himp

end Erdos577
