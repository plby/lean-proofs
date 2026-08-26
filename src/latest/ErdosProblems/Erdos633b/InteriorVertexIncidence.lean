import ErdosProblems.Erdos633b.BoundaryStarPartition

/-! Every tile incident with an actual tile vertex has a vertex or an open
edge there, even when the point lies in the interior of the large triangle. -/

namespace Erdos633b
namespace Triangle

theorem vertex_not_mem_interior_support (S : Triangle) (j : Fin 3) :
    S.points j ∉ interior S.support := by
  intro h
  have hc := (S.mem_interior_support_iff_all_coords _).mp h (j + 1)
  rw [S.coord_vertex, if_neg ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)] at hc
  exact lt_irrefl _ hc

theorem openEdge_of_not_interior_nonvertex (S : Triangle) {p : Plane}
    (hp : p ∈ S.support) (hn : p ∉ interior S.support)
    (hv : ∀ j, p ≠ S.points j) : ∃ j, p ∈ S.openEdge j := by
  have hzero : ∃ j, S.coord j p = 0 := by
    by_contra h
    push Not at h
    apply hn
    exact (S.mem_interior_support_iff_all_coords p).mpr
      (fun j => lt_of_le_of_ne (S.coord_nonneg hp j) (Ne.symm (h j)))
  obtain ⟨j, hj⟩ := hzero
  refine ⟨j, ?_⟩
  rw [S.openEdge_eq_openSegment]
  apply mem_openSegment_of_ne_left_right (hv (j + 1)).symm (hv (j + 2)).symm
  rw [← S.edge_eq_segment]
  exact ⟨hp, hj⟩

theorem interiors_inter_of_mem_interior_and_support (S R : Triangle) {p : Plane}
    (hpS : p ∈ interior S.support) (hpR : p ∈ R.support) :
    (interior S.support ∩ interior R.support).Nonempty := by
  have hpcl : p ∈ closure (interior R.support) := by rwa [R.closure_interior_support]
  obtain ⟨x, hxS, hxR⟩ := mem_closure_iff.mp hpcl (interior S.support) isOpen_interior hpS
  exact ⟨x, hxS, hxR⟩

end Triangle
namespace Tiling

theorem vertex_not_mem_piece_interior {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    (b : Fin n) : p ∉ interior (d.tile.move (d.place b)).support := by
  intro hp
  by_cases hab : b = a
  · subst b
    have he : (d.tile.move (d.place a)).points j = p := ha
    rw [← he] at hp
    exact (d.tile.move (d.place a)).vertex_not_mem_interior_support j hp
  · have hpA : p ∈ (d.tile.move (d.place a)).support := by
      rw [Triangle.support_move]
      exact ⟨d.tile.points j, d.tile.vertex_mem_support j, ha⟩
    obtain ⟨x, hxB, hxA⟩ := (d.tile.move (d.place b)).interiors_inter_of_mem_interior_and_support
      (d.tile.move (d.place a)) hp hpA
    rw [Triangle.support_move] at hxB hxA
    exact Set.disjoint_left.mp (d.disjoint_interiors hab) hxB hxA

theorem vertex_incident_piece_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p)
    (b : Fin n) (hpB : p ∈ (d.tile.move (d.place b)).support) :
    (∃ k, (d.tile.move (d.place b)).points k = p) ∨
      ∃ k, p ∈ (d.tile.move (d.place b)).openEdge k := by
  by_cases hv : ∃ k, (d.tile.move (d.place b)).points k = p
  · exact Or.inl hv
  · right
    apply (d.tile.move (d.place b)).openEdge_of_not_interior_nonvertex hpB
      (d.vertex_not_mem_piece_interior a j ha b)
    intro k he
    exact hv ⟨k, he.symm⟩

end Tiling
end Erdos633b
