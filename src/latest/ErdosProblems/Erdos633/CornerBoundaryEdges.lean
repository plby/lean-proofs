import ErdosProblems.Erdos633.BoundaryLongestEdge

/-!
# Boundary edges incident to a single outer tile corner

Finite-exception boundary coverage extends to the endpoints by closedness.
If an outer corner contains exactly one tile corner with a specified label,
its two incident outer sides contain the two distinct adjacent tile edges.
-/

namespace Erdos633

open scoped BigOperators

theorem TriangleDissection.boundaryEdges_cover_all
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (k : Fin 3) :
    P.edge k = ⋃ p : T.boundaryEdgeIndices k, (T.tile p.val.1).edge p.val.2 := by
  classical
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap (P.edgeStart k) (P.edgeEnd k)
  let S := ⋃ p : T.boundaryEdgeIndices k, (T.tile p.val.1).edge p.val.2
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun p => by
    rw [Triangle.edge, segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed)
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ (P.edgeStart_ne_edgeEnd k)
  have hF : (f ⁻¹' (T.vertexFinset : Set ℂ)).Finite := T.vertexFinset.finite_toSet.preimage hf.injOn
  have hc : Set.Icc (0 : ℝ) 1 ⊆ f ⁻¹' S := by
    apply closed_cover_Icc_of_finite_exception (hS.preimage AffineMap.lineMap_continuous) hF
    intro t ht htF
    exact (T.boundaryEdges_cover_away_from_vertices k htF).mp
      (lineMap_mem_segment ℝ (P.edgeStart k) (P.edgeEnd k) ht)
  apply Set.Subset.antisymm
  · intro z hz
    rw [Triangle.edge, segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact hc ht
  · intro z hz
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
    exact (T.mem_boundaryEdgeIndices k p.val).mp p.property hp

theorem Triangle.vertex_mem_edge_iff (P : Triangle) (j k : Fin 3) :
    P.vertex j ∈ P.edge k ↔ j ≠ k := by
  rw [P.mem_edge_iff, P.barycentric_vertex]
  simp [P.vertex_mem_carrier j]

theorem Triangle.eq_of_mem_two_edges (P : Triangle) (i j : Fin 3) (hij : i ≠ j)
    {x y : ℂ} (hxi : x ∈ P.edge i) (hxj : x ∈ P.edge j)
    (hyi : y ∈ P.edge i) (hyj : y ∈ P.edge j) : x = y := by
  have hxi0 := ((P.mem_edge_iff i x).mp hxi).2
  have hxj0 := ((P.mem_edge_iff j x).mp hxj).2
  have hyi0 := ((P.mem_edge_iff i y).mp hyi).2
  have hyj0 := ((P.mem_edge_iff j y).mp hyj).2
  have hc (k : Fin 3) : P.barycentric x k = P.barycentric y k := by
    by_cases hki : k = i
    · subst k
      rw [hxi0, hyi0]
    by_cases hkj : k = j
    · subst k
      rw [hxj0, hyj0]
    have hcover (l : Fin 3) : l = k ∨ l = i ∨ l = j := by omega
    have hxsum : ∑ l : Fin 3, P.barycentric x l = P.barycentric x k := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        rcases hcover l with h | h | h
        · exact False.elim (hl h)
        · rw [h, hxi0]
        · rw [h, hxj0]
      · simp
    have hysum : ∑ l : Fin 3, P.barycentric y l = P.barycentric y k := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        rcases hcover l with h | h | h
        · exact False.elim (hl h)
        · rw [h, hyi0]
        · rw [h, hyj0]
      · simp
    rw [P.sum_barycentric] at hxsum hysum
    exact hxsum.symm.trans hysum
  apply P.coordinateEquiv.symm.injective
  exact Complex.ext (hc 1) (hc 2)

theorem Triangle.edge_supporting_label_unique (P Q : Triangle) (k i j : Fin 3)
    (hi : Q.edge k ⊆ P.edge i) (hj : Q.edge k ⊆ P.edge j) : i = j := by
  by_contra hij
  exact Q.edgeStart_ne_edgeEnd k (P.eq_of_mem_two_edges i j hij
    (hi (left_mem_segment ℝ _ _)) (hj (left_mem_segment ℝ _ _))
    (hi (right_mem_segment ℝ _ _)) (hj (right_mem_segment ℝ _ _)))

theorem CongruentTiling.boundarySideCount_pos_of_edge_subset
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (i : Fin N) (k l : Fin 3)
    (h : (T.labelledTile i).edge l ⊆ P.edge k) : 0 < T.boundarySideCount k l := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨⟨(i, l), (T.labelledDissection.mem_boundaryEdgeIndices k (i, l)).mpr h⟩, ?_⟩
  simp

theorem CongruentTiling.cornerCount_one_tile_unique
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (z : ℂ) (k : Fin 3)
    (h : T.cornerCount z k = 1) (i j : Fin N)
    (hi : (T.labelledTile i).vertex k = z) (hj : (T.labelledTile j).vertex k = z) : i = j := by
  classical
  apply Finset.card_le_one.mp (le_of_eq h)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩

theorem CongruentTiling.two_boundary_edges_at_single_corner
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hone : T.cornerCount (P.vertex j) j = 1)
    (hzero : ∀ m : Fin 3, m ≠ j → T.cornerCount (P.vertex j) m = 0) :
    ∃ u v : Fin 3, u ≠ j ∧ v ≠ j ∧ u ≠ v ∧
      0 < T.boundarySideCount k u ∧ 0 < T.boundarySideCount l v := by
  classical
  have hk := (P.vertex_mem_edge_iff j k).mpr hjk
  have hl := (P.vertex_mem_edge_iff j l).mpr hjl
  rw [T.labelledDissection.boundaryEdges_cover_all k] at hk
  rw [T.labelledDissection.boundaryEdges_cover_all l] at hl
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hk
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hl
  have hlabel (i : Fin N) (hmem : P.vertex j ∈ (T.labelledTile i).carrier) :
      (T.labelledTile i).vertex j = P.vertex j := by
    obtain ⟨m, hm⟩ := P.vertex_of_mem_subtriangle (T.labelledTile i)
      (T.labelledDissection.tile_subset i) j hmem
    have hmpos := (T.cornerCount_pos_iff (P.vertex j) m).mpr ⟨i, hm⟩
    have hmj : m = j := by
      by_contra hne
      rw [hzero m hne] at hmpos
      omega
    simpa only [hmj] using hm
  have hpi := hlabel p.val.1 ((T.labelledTile p.val.1).edge_subset_carrier p.val.2 hp)
  have hqi := hlabel q.val.1 ((T.labelledTile q.val.1).edge_subset_carrier q.val.2 hq)
  have hpq := T.cornerCount_one_tile_unique (P.vertex j) j hone p.val.1 q.val.1 hpi hqi
  have hps := (T.labelledDissection.mem_boundaryEdgeIndices k p.val).mp p.property
  have hqs := (T.labelledDissection.mem_boundaryEdgeIndices l q.val).mp q.property
  have hpu : p.val.2 ≠ j := by
    have hmem : (T.labelledTile p.val.1).vertex j ∈ (T.labelledTile p.val.1).edge p.val.2 := by
      rwa [hpi]
    exact ((T.labelledTile p.val.1).vertex_mem_edge_iff j p.val.2).mp hmem |>.symm
  have hqv : q.val.2 ≠ j := by
    have hmem : (T.labelledTile q.val.1).vertex j ∈ (T.labelledTile q.val.1).edge q.val.2 := by
      rwa [hqi]
    exact ((T.labelledTile q.val.1).vertex_mem_edge_iff j q.val.2).mp hmem |>.symm
  have huv : p.val.2 ≠ q.val.2 := by
    intro he
    rw [← hpq, ← he] at hqs
    exact hkl (P.edge_supporting_label_unique (T.labelledTile p.val.1) p.val.2 k l hps hqs)
  exact ⟨p.val.2, q.val.2, hpu, hqv, huv,
    T.boundarySideCount_pos_of_edge_subset p.val.1 k p.val.2 hps,
    T.boundarySideCount_pos_of_edge_subset q.val.1 l q.val.2 hqs⟩

end Erdos633
