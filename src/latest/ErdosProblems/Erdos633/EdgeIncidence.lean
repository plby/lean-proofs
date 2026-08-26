import ErdosProblems.Erdos633.BoundaryLongestEdge

/-!
# Edge incidence away from all dissection vertices

Every incident tile at a nonvertex edge point contributes a half-disk sector.
The actual sector partition therefore gives one boundary tile or two interior
tiles. These statements permit partial edge contacts.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def TriangleDissection.incidentTiles {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun i => z ∈ (T.tile i).carrier

theorem TriangleDissection.mem_incidentTiles {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (i : Fin N) :
    i ∈ T.incidentTiles z ↔ z ∈ (T.tile i).carrier := by
  classical
  simp [TriangleDissection.incidentTiles]

theorem TriangleDissection.not_outer_vertex_of_not_vertexFinset
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (hv : z ∉ T.vertexFinset) : z ∉ Set.range P.vertex := by
  rintro ⟨j, rfl⟩
  exact hv (T.outer_vertex_mem_vertexFinset j)

theorem TriangleDissection.not_mem_tile_interior_of_mem_tile_edge
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (i : Fin N) (k : Fin 3) (hz : z ∈ (T.tile i).edge k) (j : Fin N) :
    z ∉ interior (T.tile j).carrier := by
  by_cases hji : j = i
  · subst j
    exact (T.tile i).edge_not_mem_interior k hz
  · intro h
    exact Set.disjoint_left.mp (T.interior_disjoint_carrier hji) h
      ((T.tile i).edge_subset_carrier k hz)

theorem TriangleDissection.localSectorArea_eq_incident_count_half_pi
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (hv : z ∉ T.vertexFinset) (i : Fin N) (k : Fin 3)
    (hz : z ∈ (T.tile i).edge k) :
    P.localSectorArea z = (T.incidentTiles z).card * (Real.pi / 2) := by
  classical
  have hzP := T.tile_subset i ((T.tile i).edge_subset_carrier k hz)
  rw [T.localSectorArea_eq_sum_ite z hzP]
  have heq (j : Fin N) :
      (if z ∈ (T.tile j).carrier then (T.tile j).localSectorArea z else 0) =
        if z ∈ (T.tile j).carrier then Real.pi / 2 else 0 := by
    split_ifs with hj
    · exact (T.tile j).localSectorArea_boundary_nonvertex z hj
        (T.not_mem_tile_interior_of_mem_tile_edge i k hz j)
        (T.not_tile_vertex_of_not_vertexFinset hv j)
    · rfl
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp [TriangleDissection.incidentTiles]

theorem TriangleDissection.incidentTiles_card_eq_two_of_interior_edge
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (hv : z ∉ T.vertexFinset) (hP : z ∈ interior P.carrier)
    (i : Fin N) (k : Fin 3) (hz : z ∈ (T.tile i).edge k) :
    (T.incidentTiles z).card = 2 := by
  have h := T.localSectorArea_eq_incident_count_half_pi hv i k hz
  rw [P.localSectorArea_interior z hP] at h
  have hr : ((T.incidentTiles z).card : ℝ) = 2 := by nlinarith [Real.pi_pos]
  exact_mod_cast hr

theorem TriangleDissection.incidentTiles_card_eq_one_of_boundary
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (hv : z ∉ T.vertexFinset) (hP : z ∈ P.carrier)
    (hint : z ∉ interior P.carrier) : (T.incidentTiles z).card = 1 := by
  have hcover := hP
  rw [← T.covers, Set.mem_iUnion] at hcover
  obtain ⟨i, hi⟩ := hcover
  have hni : z ∉ interior (T.tile i).carrier :=
    fun h => hint (interior_mono (T.tile_subset i) h)
  obtain ⟨k, hk⟩ := (T.tile i).boundary_nonvertex_mem_openEdge z hi hni
    (T.not_tile_vertex_of_not_vertexFinset hv i)
  have h := T.localSectorArea_eq_incident_count_half_pi hv i k
    ((T.tile i).openEdge_subset_edge k hk)
  rw [P.localSectorArea_boundary_nonvertex z hP hint
    (T.not_outer_vertex_of_not_vertexFinset hv)] at h
  have hr : ((T.incidentTiles z).card : ℝ) = 1 := by nlinarith [Real.pi_pos]
  exact_mod_cast hr

theorem TriangleDissection.incident_tile_has_open_edge
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {z : ℂ}
    (hv : z ∉ T.vertexFinset) (i : Fin N) (k : Fin 3)
    (hz : z ∈ (T.tile i).edge k) {j : Fin N} (hj : j ∈ T.incidentTiles z) :
    ∃! l : Fin 3, z ∈ (T.tile j).openEdge l := by
  obtain ⟨l, hl⟩ := (T.tile j).boundary_nonvertex_mem_openEdge z
    ((T.mem_incidentTiles z j).mp hj)
    (T.not_mem_tile_interior_of_mem_tile_edge i k hz j)
    (T.not_tile_vertex_of_not_vertexFinset hv j)
  refine ⟨l, hl, ?_⟩
  intro m hm
  by_contra hml
  exact Set.disjoint_left.mp ((T.tile j).openEdges_disjoint hml) hm hl

end Erdos633
