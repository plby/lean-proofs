import ErdosProblems.Erdos577.FullLeafHeavyAdjacentCore

/-! The adjacent first-row case forces exactly five induced edges on its further block. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.adjacent_edges_ge_five {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) {x : V} (hx : x ∈ insert p.leaf s)
    (h0 : G.Adj x (q 0)) (h1 : G.Adj x (q 1))
    (hpair : 6 ≤ degreeIn G (q 0) (insert (p.vertices 3) a) +
      degreeIn G (q 2) (insert (p.vertices 3) a)) : 5 ≤ edgeCount G q.support := by
  classical
  have hout (i : Fin 4) : q i ∉ p.triangle ∪ a := fun hh ↦
    disjoint_left.mp (h.core_disjoint_block hj hja) hh ((q.mem_support _).mpr ⟨i, rfl⟩)
  by_cases hsplit : ∃ f : BlockPartition G (insert (q 0) (p.triangle ∪ a)),
      f.weightSum (edgeCount G) = 12
  · obtain ⟨f, hf⟩ := hsplit
    have hxout : x ∉ q.support := fun hh ↦
      disjoint_left.mp (h.five_disjoint_block hj hjs) hx hh
    obtain ⟨m, hm⟩ := FullLeafHeavy.adjacent_matching_remainder q hxout h1
    have hb := h.core_insertion_matching_bound hcard hdeg hn hx hj hjs hja
      ((q.mem_support _).mpr ⟨0, rfl⟩) f m hm
    omega
  · obtain ⟨u, hu, v, hv, h2u, h2v, huv⟩ :=
      h.second_neighbor_edge_of_heavy_pair (hout 0) hpair hsplit
    obtain ⟨f, hf⟩ := h.core_partition_of_second_neighbor_edge (hout 2) hu hv h2u h2v huv
    have hb := h.core_insertion_triangle_bound hx hj hjs hja
      ((q.mem_support _).mpr ⟨2, rfl⟩) f (FullLeafHeavy.adjacent_triangle_remainder q h0 h1)
    omega

theorem Configuration.first_two_edges_eq_five {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    edgeCount G q.support = 5 := by
  obtain ⟨v, hv, hrow, hpair, hupper⟩ :=
    h.adjacent_heavy_preparation hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  have hlower := h.adjacent_edges_ge_five hcard hdeg hn v (by rwa [hv]) (by rwa [hv])
    (by rwa [hv]) hx ((hrow 0).mpr (Or.inl rfl)) ((hrow 1).mpr (Or.inr rfl)) hpair
  rw [hv] at hlower hupper
  omega

end Erdos577.FullLeafCore
