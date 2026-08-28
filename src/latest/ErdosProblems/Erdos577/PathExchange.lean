import ErdosProblems.Erdos577.PathWitnesses
import ErdosProblems.Erdos577.PathModel
import ErdosProblems.Erdos577.PartitionExchange

/-! The eight-vertex exchange and the unconditional existence of a triangle remainder. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At least nine cross edges suffice for an actual eight-vertex exchange.
Optional chords in either four-set are allowed and are never removed from G. -/
theorem path_quadrilateral_exchange (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : 9 ≤ contacts G p.support q.support) :
    LocalExchange G (p.support ∪ q.support) := by
  have hc : 9 ≤ PathExchange.crossCount (PathExchange.encoded p q).val := by
    rw [PathExchange.crossCount_encoded]
    exact h
  have hm := (PathExchange.finite_exchange (PathExchange.encoded p q) hc).image
    (PathExchange.modelCopy p q hd)
  rwa [PathExchange.modelCopy_image] at hm

/-- The path supplied by saturation can always be exchanged for a triangle
remainder under the exact boundary minimum-degree hypothesis. -/
theorem Saturated.exists_triangle_chain [Fintype V] {k : ℕ} (h : Saturated G k)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) :
    Nonempty (TriangleChain G) := by
  classical
  obtain ⟨p, ⟨b⟩⟩ := h.exists_path_remainder hcard
  by_cases ht : TriangleIn G p.support
  · exact TriangleChain.exists_of_triangle p.card_support b ht
  · obtain ⟨s, hs, hh⟩ := b.exists_path_heavy_block p hcard hdeg h.1 ht
    obtain ⟨q, hq⟩ := b.quad s hs
    have hd : Disjoint p.support q.support := by
      rw [hq]
      apply disjoint_left.mpr
      intro v hv hvq
      exact (mem_sdiff.mp (b.block_subset hs hvq)).2 hv
    have he := path_quadrilateral_exchange p q hd (by rwa [hq])
    rw [hq] at he
    exact b.chain_of_local_exchange p.card_support hcard h.1 hs he

/-- The source's two-score optimum exists without assuming a chain family. -/
theorem Saturated.exists_feasible_chain [Fintype V] {k : ℕ} (h : Saturated G k)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) :
    ∃ c : TriangleChain G, c.Feasible :=
  TriangleChain.exists_feasible (h.exists_triangle_chain hcard hdeg)

end Erdos577
