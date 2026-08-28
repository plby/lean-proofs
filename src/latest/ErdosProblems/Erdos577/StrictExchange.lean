import ErdosProblems.Erdos577.ChainExchange

/-! Strict improvements of a single block, independent of attachment scores. -/

namespace Erdos577

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def StrictImprovement (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (oldEdges : ℕ) : Prop :=
  ∃ d : LocalChain G s, oldEdges < edgeCount G d.block

lemma StrictImprovement.image {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {s : Finset V} {oldEdges : ℕ}
    (h : StrictImprovement G s oldEdges) (f : G.Copy H) :
    StrictImprovement H (s.image f) oldEdges := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d.image f, hd.trans_le (d.image_edgeCount_le f)⟩

lemma TriangleChain.Feasible.no_strict_improvement [Fintype V]
    {c : TriangleChain G} (hc : c.Feasible) {b : Finset V} (hb : b ∈ c.blocks) :
    ¬StrictImprovement G (c.remainder ∪ b) (edgeCount G b) := by
  rintro ⟨d, hd⟩
  exact (not_lt_of_ge (hc.local_edges_le hb d)) hd

end Erdos577
