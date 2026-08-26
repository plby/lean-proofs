import ErdosProblems.Erdos633.OrientedEdges

/-!
# Pointwise cancellation of oriented boundary densities

For an arbitrary odd real function on directions, the outer boundary density
equals the sum of tile boundary densities away from the finite vertex set.
The direction function need not be continuous or measurable: on each edge its
value is a fixed constant.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def Triangle.edgeDensity (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3) : ℂ → ℝ :=
  (P.edge k).indicator (fun _ => φ (P.unitEdgeVector k))

noncomputable def Triangle.boundaryDensity (P : Triangle) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∑ k : Fin 3, P.edgeDensity φ k z

theorem Triangle.edgeDensity_of_mem (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3)
    {z : ℂ} (hz : z ∈ P.edge k) : P.edgeDensity φ k z = φ (P.unitEdgeVector k) :=
  Set.indicator_of_mem hz _

theorem Triangle.edgeDensity_of_not_mem (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3)
    {z : ℂ} (hz : z ∉ P.edge k) : P.edgeDensity φ k z = 0 :=
  Set.indicator_of_notMem hz _

theorem Triangle.boundaryDensity_openEdge (P : Triangle) (φ : ℂ → ℝ) (k : Fin 3)
    {z : ℂ} (hz : z ∈ P.openEdge k) : P.boundaryDensity φ z = φ (P.unitEdgeVector k) := by
  classical
  unfold Triangle.boundaryDensity
  rw [Finset.sum_eq_single k]
  · exact P.edgeDensity_of_mem φ k (P.openEdge_subset_edge k hz)
  · intro j _ hjk
    apply P.edgeDensity_of_not_mem
    intro hj
    have hpos := P.barycentric_pos_of_mem_openEdge k j hjk hz
    have hzero := ((P.mem_edge_iff j z).mp hj).2
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

theorem Triangle.boundaryDensity_zero_of_no_edges (P : Triangle) (φ : ℂ → ℝ)
    {z : ℂ} (hz : ∀ k, z ∉ P.edge k) : P.boundaryDensity φ z = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  exact P.edgeDensity_of_not_mem φ k (hz k)

theorem Triangle.boundaryDensity_zero_of_not_carrier (P : Triangle) (φ : ℂ → ℝ)
    {z : ℂ} (hz : z ∉ P.carrier) : P.boundaryDensity φ z = 0 :=
  P.boundaryDensity_zero_of_no_edges φ (fun k hk => hz (P.edge_subset_carrier k hk))

theorem Triangle.boundaryDensity_zero_of_interior (P : Triangle) (φ : ℂ → ℝ)
    {z : ℂ} (hz : z ∈ interior P.carrier) : P.boundaryDensity φ z = 0 :=
  P.boundaryDensity_zero_of_no_edges φ (fun k hk => P.edge_not_mem_interior k hk hz)

theorem TriangleDissection.sum_boundaryDensity_eq_incident
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (φ : ℂ → ℝ) (z : ℂ) :
    (∑ i : Fin N, (T.tile i).boundaryDensity φ z) =
      ∑ i ∈ T.incidentTiles z, (T.tile i).boundaryDensity φ z := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply (T.tile i).boundaryDensity_zero_of_not_carrier
  exact fun h => hi ((T.mem_incidentTiles z i).mpr h)

theorem TriangleDissection.boundaryDensity_eq_sum_of_not_vertex
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (φ : ℂ → ℝ) (hodd : ∀ w, φ (-w) = -φ w) {z : ℂ}
    (hv : z ∉ T.vertexFinset) :
    P.boundaryDensity φ z = ∑ i : Fin N, (T.tile i).boundaryDensity φ z := by
  classical
  by_cases hzP : z ∈ P.carrier
  · rw [T.sum_boundaryDensity_eq_incident]
    by_cases hint : z ∈ interior P.carrier
    · rw [P.boundaryDensity_zero_of_interior φ hint]
      symm
      by_cases he : ∃ i : Fin N, ∃ k : Fin 3, z ∈ (T.tile i).edge k
      · obtain ⟨i₀, k₀, hz⟩ := he
        obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp
          (T.incidentTiles_card_eq_two_of_interior_edge hv hint i₀ k₀ hz)
        have hi : i ∈ T.incidentTiles z := by rw [hset]; simp
        have hj : j ∈ T.incidentTiles z := by rw [hset]; simp
        obtain ⟨k, hk, _⟩ := T.incident_tile_has_open_edge hv i₀ k₀ hz hi
        obtain ⟨l, hl, _⟩ := T.incident_tile_has_open_edge hv i₀ k₀ hz hj
        rw [hset, Finset.sum_pair hij,
          (T.tile i).boundaryDensity_openEdge φ k hk,
          (T.tile j).boundaryDensity_openEdge φ l hl]
        exact T.shared_open_edges_odd_cancel φ hodd hij k l hk hl
      · apply Finset.sum_eq_zero
        intro i _
        exact (T.tile i).boundaryDensity_zero_of_no_edges φ
          (fun k hk => he ⟨i, k, hk⟩)
    · obtain ⟨k, hk⟩ := P.boundary_nonvertex_mem_openEdge z hzP hint
        (T.not_outer_vertex_of_not_vertexFinset hv)
      obtain ⟨i, hset⟩ := Finset.card_eq_one.mp
        (T.incidentTiles_card_eq_one_of_boundary hv hzP hint)
      have hi : z ∈ (T.tile i).carrier := (T.mem_incidentTiles z i).mp (by rw [hset]; simp)
      have hni : z ∉ interior (T.tile i).carrier :=
        fun h => hint (interior_mono (T.tile_subset i) h)
      obtain ⟨l, hl⟩ := (T.tile i).boundary_nonvertex_mem_openEdge z hi hni
        (T.not_tile_vertex_of_not_vertexFinset hv i)
      rw [hset, Finset.sum_singleton, P.boundaryDensity_openEdge φ k hk,
        (T.tile i).boundaryDensity_openEdge φ l hl]
      congr 1
      symm
      apply P.unitEdgeVector_eq_of_edge_subset (T.tile i) k l (T.tile_subset i)
      exact P.edge_contains_segment_of_open_point k
        (T.tile_subset i ((T.tile i).edgeStart_mem_carrier l))
        (T.tile_subset i ((T.tile i).edgeEnd_mem_carrier l))
        (P.openEdge_subset_edge k hk) hl
  · rw [P.boundaryDensity_zero_of_not_carrier φ hzP]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact (T.tile i).boundaryDensity_zero_of_not_carrier φ
      (fun h => hzP (T.tile_subset i h))

end Erdos633
