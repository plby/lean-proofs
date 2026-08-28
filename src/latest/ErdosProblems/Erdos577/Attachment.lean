import ErdosProblems.Erdos577.UnattachedWitnesses0
import ErdosProblems.Erdos577.UnattachedWitnesses1
import ErdosProblems.Erdos577.UnattachedWitnesses2
import ErdosProblems.Erdos577.UnattachedWitnesses3
import ErdosProblems.Erdos577.UnattachedTransport
import ErdosProblems.Erdos577.AttachmentCount

/-! A third-score optimum supplies an attached chain; later chains retain only two maxima. -/

namespace Erdos577

open Finset

namespace Unattached

theorem finite_positive (diagonal : Fin 4) (m : Fin 65536)
    (h : 13 ≤ weightedCount m.val) : Positive diagonal m.val := by
  fin_cases diagonal
  · exact D0.finite_positive m h
  · exact D1.finite_positive m h
  · exact D2.finite_positive m h
  · exact D3.finite_positive m h

end Unattached

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace TriangleChain

/-- This local bound uses all three maxima only when the old terminal is
unattached. All finite factors and improvements are transported to G. -/
lemma Refined.unattached_weight {c : TriangleChain G} (hc : c.Refined) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (hzero : c.attachmentScore = 0) (b : Finset V) (hb : b ∈ c.blocks) :
    3 * degreeIn G c.terminal b + contacts G c.triangle b ≤ 12 := by
  by_contra hh
  have h13 : 13 ≤ 3 * degreeIn G c.terminal b + contacts G c.triangle b := by omega
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  have hd : Disjoint c.remainder q.support := by
    rw [hq]
    exact c.property.remainder_disjoint.mono le_rfl (c.blockPartition.block_subset hb)
  have hp := Unattached.finite_positive (Unattached.diagonal q) (Unattached.encoded c q)
    (by rw [Unattached.weightedCount_encoded, hq]; exact h13)
  rcases hp with hfac | himp
  · have hg := hfac.image (Unattached.modelCopy c q hd)
    rw [Unattached.modelCopy_image, hq] at hg
    exact c.no_local_factor hcard hn hb hg
  · have hg := himp.image (Unattached.modelCopy c q hd)
    rw [Unattached.modelCopy_image, Unattached.oldEdges_diagonal, hq] at hg
    exact hc.no_local_improvement hzero hb hg

theorem Refined.attachment_eq_one {c : TriangleChain G} (hc : c.Refined) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) : c.attachmentScore = 1 := by
  have hle : c.attachmentScore ≤ 1 := c.terminal_degree_le_one hcard hn
  have hne : c.attachmentScore ≠ 0 := by
    intro hz
    exact c.unattached_degree_contradiction hcard hdeg hz (hc.unattached_weight hcard hn hz)
  omega

/-- Strong chains have an actual attachment and only the two source maxima.
The auxiliary third maximum is deliberately absent from this structure. -/
structure Strong (c : TriangleChain G) : Prop extends c.Feasible where
  attached : c.attachmentScore = 1

end TriangleChain

theorem Saturated.exists_strong_chain {k : ℕ} (h : Saturated G k)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) :
    ∃ c : TriangleChain G, c.Strong := by
  obtain ⟨c, hc⟩ := h.exists_refined_chain hcard hdeg
  exact ⟨c, hc.toFeasible, hc.attachment_eq_one hcard hdeg h.1⟩

end Erdos577
