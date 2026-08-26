import ErdosProblems.Erdos633b.BoundaryTopology

/-! At an outer boundary point that is a vertex of one tile, every incident
tile also has a vertex there. Open-edge incidence would occupy the whole local half-plane. -/

namespace Erdos633b

namespace Triangle

theorem vertex_not_mem_openEdge (T : Triangle) (i j : Fin 3) :
    T.points j ∉ T.openEdge i := by
  intro h
  obtain ⟨k, hki, hkj⟩ := (by decide : ∀ i j : Fin 3, ∃ k, k ≠ i ∧ k ≠ j) i j
  have hk := h.2 k hki
  rw [T.coord_vertex, if_neg hkj] at hk
  exact lt_irrefl _ hk

theorem openEdge_of_boundary_nonvertex (T S : Triangle) (hST : S.support ⊆ T.support)
    (i : Fin 3) {p : Plane} (hpS : p ∈ S.support) (hpT : p ∈ T.edge i)
    (hvertex : ∀ j, p ≠ S.points j) :
    ∃ j, S.edge j ⊆ T.edge i ∧ p ∈ S.openEdge j := by
  have hp : p ∈ S.support ∩ T.edge i := ⟨hpS, hpT⟩
  rcases T.support_inter_edge_cases S hST i with he | ⟨j, he⟩ | ⟨j, he⟩
  · rw [he] at hp
    exact hp.elim
  · rw [he, Set.mem_singleton_iff] at hp
    exact False.elim (hvertex j hp)
  · refine ⟨j, ?_, ?_⟩
    · rw [← he]
      exact Set.inter_subset_right
    · rw [he] at hp
      rw [S.openEdge_eq_openSegment]
      apply mem_openSegment_of_ne_left_right (hvertex (j + 1)).symm (hvertex (j + 2)).symm
      rwa [← S.edge_eq_segment]

theorem interiors_inter_of_openEdge_and_mem (T S R : Triangle)
    (hST : S.support ⊆ T.support) (hRT : R.support ⊆ T.support)
    (i j : Fin 3) (he : S.edge j ⊆ T.edge i) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.support) :
    (interior S.support ∩ interior R.support).Nonempty := by
  obtain ⟨U, hU, hpU, hSU⟩ := T.openEdge_neighborhood S hST i j he hpS
  have hpcl : p ∈ closure (interior R.support) := by rwa [R.closure_interior_support]
  obtain ⟨x, hxU, hxR⟩ := mem_closure_iff.mp hpcl U hU hpU
  exact ⟨x, hSU ⟨hxU, interior_mono hRT hxR⟩, hxR⟩

end Triangle

namespace Tiling

theorem boundary_openEdge_exclusive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (a b : Fin n)
    (he : (d.tile.move (d.place a)).edge j ⊆ T.edge i) {p : Plane}
    (hpA : p ∈ (d.tile.move (d.place a)).openEdge j)
    (hpB : p ∈ d.place b '' d.tile.support) : b = a := by
  by_contra hn
  have hA : (d.tile.move (d.place a)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset a
  have hB : (d.tile.move (d.place b)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset b
  have hpB' : p ∈ (d.tile.move (d.place b)).support := by rwa [Triangle.support_move]
  obtain ⟨x, hxA, hxB⟩ := T.interiors_inter_of_openEdge_and_mem
    (d.tile.move (d.place a)) (d.tile.move (d.place b)) hA hB i j he hpA hpB'
  rw [Triangle.support_move] at hxA hxB
  exact Set.disjoint_left.mp (d.disjoint_interiors (Ne.symm hn)) hxA hxB

theorem boundary_vertex_of_mem_piece {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hpT : p ∈ T.edge i)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    (b : Fin n) (hpB : p ∈ d.place b '' d.tile.support) :
    ∃ k, d.place b (d.tile.points k) = p := by
  by_contra hn
  push Not at hn
  let S : Triangle := d.tile.move (d.place b)
  have hST : S.support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset b
  have hpS : p ∈ S.support := by rwa [Triangle.support_move]
  have hvertex (k : Fin 3) : p ≠ S.points k := Ne.symm (hn k)
  obtain ⟨k, hk, hpk⟩ := T.openEdge_of_boundary_nonvertex S hST i hpS hpT hvertex
  have hpA : p ∈ d.place a '' d.tile.support := by
    exact ⟨d.tile.points j, d.tile.vertex_mem_support j, ha⟩
  have hab := d.boundary_openEdge_exclusive i k b a hk hpk hpA
  rw [hab] at ha
  exact hn j ha

theorem local_boundary_vertex_cover {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) {p : Plane} (hpT : p ∈ T.edge i)
    (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    ∃ ε > 0, ∀ x ∈ Metric.ball p ε,
      x ∈ T.support ↔ ∃ b : Fin n, ∃ k : Fin 3,
        d.place b (d.tile.points k) = p ∧ x ∈ d.place b '' d.tile.support := by
  obtain ⟨ε, hε, hlocal⟩ := d.exists_incidence_radius p
  refine ⟨ε, hε, ?_⟩
  intro x hx
  constructor
  · intro hxT
    rw [← d.covers, Set.mem_iUnion] at hxT
    obtain ⟨b, hb⟩ := hxT
    obtain ⟨k, hk⟩ := d.boundary_vertex_of_mem_piece i hpT a j ha b (hlocal b x hx hb)
    exact ⟨b, k, hk, hb⟩
  · rintro ⟨b, k, _, hb⟩
    exact d.piece_subset b hb

end Tiling

end Erdos633b
