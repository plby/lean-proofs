import ErdosProblems.Erdos577.TripleFinalFactor

/-! The two applications of the universal heavy-block theorem exclude every triple configuration. -/

namespace Erdos577.UniversalTriple

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

theorem Configuration.false (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) : False := by
  obtain ⟨a, u, hh⟩ := h.exists_heavy_choice hc hcard hdeg hn
  obtain ⟨j, s, z, hj, _, hja, hs, _, hsa, hsj, hz, hrepJ, hcommon⟩ :=
    hh.exists_final_blocks hc hcard hdeg hn
  exact hn (h.final_factor hcard hh.heavy_mem j hj hs hja hsa hsj hh.chosen_mem hz
    hh.leaf_replaces_chosen hrepJ hcommon)

end Erdos577.UniversalTriple
