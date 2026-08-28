import ErdosProblems.Erdos577.JointClaimFourCompletion

/-! Two applications of the universal local classification exclude the maximal CaseII core. -/

namespace Erdos577.JointFinal

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.impossible {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a) : False := by
  obtain ⟨j, hj, hjq, hja, hnine⟩ := h.exists_heavy_block hcard hdeg
  have hfirst := h.local_conclusion hc hcard hdeg hn hj hjq hja hnine
  have hmiss := h.classified_pair_nonadjacent hc hcard hn hj hjq hja hfirst
  have hreverse := h.reversed_early hc hcard hn hmiss
  obtain ⟨b, hb, hbq, hba, hbj, hheavy⟩ :=
    hreverse.exists_second_heavy_block hc hcard hdeg hn hj hjq hja
  have hsecond := hreverse.local_conclusion hc hcard hdeg hn hb hbq hba hheavy
  exact h.two_classified_false hc hcard hn hmiss hj hjq hja hb hbq hba hbj hfirst hsecond

end Erdos577.JointFinal
