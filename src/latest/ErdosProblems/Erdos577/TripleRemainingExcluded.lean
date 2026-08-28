import ErdosProblems.Erdos577.TripleRemainingCount

/-! The remaining C configuration contradicts leaf transport and the universal triangle bound. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

theorem CCase.false (s : CCase p a w u v) (h : HighCore c p q a w) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : False := by
  obtain ⟨j, hj, hjQ, hja, hheavy⟩ := s.exists_eleven_outside h hcard hdeg hn
  obtain ⟨d, hd, hp, _, hT, _, _, hkeep⟩ := s.exists_chain h hc hcard hn
  have hQ : q.support ∈ d.blocks := hkeep q.support h.block h.core_ne.symm
  have hJ : j ∈ d.blocks := hkeep j hj hja
  have hrep : QuadOn G (insert (s.paw h).leaf (q.support.erase (q 3))) :=
    QuadOn.of_clique h.toConfiguration.leaf_replacement_complete.card_eq
      h.toConfiguration.leaf_replacement_complete.isClique
  have hscore : edgeCount G (insert (s.paw h).leaf (q.support.erase (q 3))) =
      edgeCount G q.support := h.toConfiguration.leaf_replacement_score
  obtain ⟨_, _, hlarge⟩ := hd.toFeasible.leaf_transport hcard hdeg hn (s.paw h) hp
    hQ hJ hjQ (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩)
    (s.exposed_pair_degree h) hheavy (Or.inl ⟨hrep, hscore⟩)
  have hsmall := hd.triangle_block_bound hcard hdeg hn j hJ
  rw [hT] at hsmall
  rw [s.paw_triangle] at hlarge
  omega

end Erdos577.UniversalTriple
