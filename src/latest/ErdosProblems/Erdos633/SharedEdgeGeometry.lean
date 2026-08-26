import ErdosProblems.Erdos633.EdgeIncidence

/-!
# Supporting lines and opposite sides at shared open edges

The local open cone at an open edge is its inward open half-plane. Disjoint
tile interiors force two incident half-planes to have the same boundary line
and opposite inward sides. No whole-edge matching assumption is needed.
-/

namespace Erdos633

theorem Triangle.barycentric_eq_zero_iff_lineMap (P : Triangle) (k : Fin 3) (z : ℂ) :
    P.barycentric z k = 0 ↔
      ∃ t : ℝ, AffineMap.lineMap (P.edgeStart k) (P.edgeEnd k) t = z := by
  constructor
  · intro hk
    have hs := P.sum_barycentric z
    norm_num [Fin.sum_univ_succ] at hs
    have hr := P.barycentric_repr z
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · refine ⟨P.barycentric z 2, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      change (1 - P.barycentric z 2) • P.b + P.barycentric z 2 • P.c = z
      have h1 : 1 - P.barycentric z 2 = P.barycentric z 1 := by linarith
      rw [h1]
      simpa only [hk, zero_smul, zero_add] using hr
    · refine ⟨P.barycentric z 0, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      change (1 - P.barycentric z 0) • P.c + P.barycentric z 0 • P.a = z
      have h2 : 1 - P.barycentric z 0 = P.barycentric z 2 := by linarith
      rw [h2]
      simpa only [hk, zero_smul, add_zero, zero_add, add_comm] using hr
    · refine ⟨P.barycentric z 1, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      change (1 - P.barycentric z 1) • P.a + P.barycentric z 1 • P.b = z
      have h0 : 1 - P.barycentric z 1 = P.barycentric z 0 := by linarith
      rw [h0]
      simpa only [hk, zero_smul, add_zero] using hr
  · rintro ⟨t, rfl⟩
    rw [P.barycentric_lineMap, P.barycentric_edgeStart_self,
      P.barycentric_edgeEnd_self]
    ring

theorem Triangle.collinear_barycentric_zero (P : Triangle) (k : Fin 3) :
    Collinear ℝ {z | P.barycentric z k = 0} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨P.edgeStart k, P.edgeEnd k - P.edgeStart k, ?_⟩
  intro z hz
  obtain ⟨t, rfl⟩ := (P.barycentric_eq_zero_iff_lineMap k z).mp hz
  exact ⟨t, AffineMap.lineMap_apply_module' _ _ _⟩

theorem Triangle.localOpenConeAt_openEdge (P : Triangle) (k : Fin 3) {z : ℂ}
    (hz : z ∈ P.openEdge k) :
    P.localOpenConeAt z = {x | 0 < P.barycentric x k} := by
  have hk := ((P.mem_edge_iff k z).mp (P.openEdge_subset_edge k hz)).2
  ext x
  constructor
  · intro h
    exact h k hk
  · intro h j hj
    by_cases hjk : j = k
    · simpa only [hjk, Set.mem_ofPred_eq] using h
    · exact False.elim ((ne_of_gt (P.barycentric_pos_of_mem_openEdge k j hjk hz)) hj)

/-- Two disjoint open affine half-planes through a common point have the same
boundary line. The proof constructs a point positive for both if a kernel
point of the first coordinate were nonzero for the second. -/
theorem Triangle.barycentric_zero_of_disjoint_halfplanes (P Q : Triangle)
    (k l : Fin 3) (z : ℂ) (hzP : P.barycentric z k = 0)
    (hzQ : Q.barycentric z l = 0)
    (hd : Disjoint {x | 0 < P.barycentric x k} {x | 0 < Q.barycentric x l})
    (x : ℂ) (hx : P.barycentric x k = 0) : Q.barycentric x l = 0 := by
  by_contra hqx
  let w := P.vertex k
  let t := (1 - Q.barycentric w l) / Q.barycentric x l
  let y := AffineMap.lineMap z x t
  have hw : P.barycentric w k = 1 := by simp [w, P.barycentric_vertex]
  have hyP : P.barycentric y k = 0 := by
    rw [P.barycentric_lineMap, hzP, hx]
    ring
  have hyQ : Q.barycentric y l = 1 - Q.barycentric w l := by
    rw [Q.barycentric_lineMap, hzQ, mul_zero, zero_add]
    exact div_mul_cancel₀ _ hqx
  have hP : 0 < P.barycentric (AffineMap.lineMap w y (1 / 2 : ℝ)) k := by
    rw [P.barycentric_lineMap, hw, hyP]
    norm_num
  have hQ : 0 < Q.barycentric (AffineMap.lineMap w y (1 / 2 : ℝ)) l := by
    rw [Q.barycentric_lineMap, hyQ]
    linarith
  exact Set.disjoint_left.mp hd hP hQ

theorem Triangle.opposite_vertex_negative_of_disjoint_halfplanes (P Q : Triangle)
    (k l : Fin 3) (z : ℂ) (hzP : P.barycentric z k = 0)
    (hzQ : Q.barycentric z l = 0)
    (hd : Disjoint {x | 0 < P.barycentric x k} {x | 0 < Q.barycentric x l}) :
    Q.barycentric (P.vertex k) l < 0 := by
  have hp : 0 < P.barycentric (P.vertex k) k := by simp [P.barycentric_vertex]
  have hle : Q.barycentric (P.vertex k) l ≤ 0 :=
    le_of_not_gt (fun h => Set.disjoint_left.mp hd hp h)
  apply lt_of_le_of_ne hle
  intro heq
  have hv (j : Fin 3) : Q.barycentric (P.vertex j) l = 0 := by
    by_cases hj : j = k
    · simpa only [hj] using heq
    · apply P.barycentric_zero_of_disjoint_halfplanes Q k l z hzP hzQ hd
      rw [P.barycentric_vertex, if_neg hj]
  apply P.not_collinear
  apply (Q.collinear_barycentric_zero l).subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hv 0
  · exact hv 1
  · exact hv 2

theorem TriangleDissection.shared_open_edges_halfplanes_disjoint
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {i j : Fin N}
    (hij : i ≠ j) (k l : Fin 3) {z : ℂ}
    (hi : z ∈ (T.tile i).openEdge k) (hj : z ∈ (T.tile j).openEdge l) :
    Disjoint {x | 0 < (T.tile i).barycentric x k}
      {x | 0 < (T.tile j).barycentric x l} := by
  rw [← (T.tile i).localOpenConeAt_openEdge k hi,
    ← (T.tile j).localOpenConeAt_openEdge l hj]
  exact T.localOpenConeAt_disjoint z hij
    ((T.tile i).edge_subset_carrier k ((T.tile i).openEdge_subset_edge k hi))
    ((T.tile j).edge_subset_carrier l ((T.tile j).openEdge_subset_edge l hj))

theorem TriangleDissection.shared_open_edges_same_supporting_line
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {i j : Fin N}
    (hij : i ≠ j) (k l : Fin 3) {z : ℂ}
    (hi : z ∈ (T.tile i).openEdge k) (hj : z ∈ (T.tile j).openEdge l) (x : ℂ) :
    (T.tile i).barycentric x k = 0 ↔ (T.tile j).barycentric x l = 0 := by
  have hzP := (((T.tile i).mem_edge_iff k z).mp
    ((T.tile i).openEdge_subset_edge k hi)).2
  have hzQ := (((T.tile j).mem_edge_iff l z).mp
    ((T.tile j).openEdge_subset_edge l hj)).2
  have hd := T.shared_open_edges_halfplanes_disjoint hij k l hi hj
  exact ⟨(T.tile i).barycentric_zero_of_disjoint_halfplanes (T.tile j) k l z hzP hzQ hd x,
    (T.tile j).barycentric_zero_of_disjoint_halfplanes (T.tile i) l k z hzQ hzP hd.symm x⟩

theorem TriangleDissection.shared_open_edges_opposite_vertices
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) {i j : Fin N}
    (hij : i ≠ j) (k l : Fin 3) {z : ℂ}
    (hi : z ∈ (T.tile i).openEdge k) (hj : z ∈ (T.tile j).openEdge l) :
    (T.tile j).barycentric ((T.tile i).vertex k) l < 0 ∧
      (T.tile i).barycentric ((T.tile j).vertex l) k < 0 := by
  have hzP := (((T.tile i).mem_edge_iff k z).mp
    ((T.tile i).openEdge_subset_edge k hi)).2
  have hzQ := (((T.tile j).mem_edge_iff l z).mp
    ((T.tile j).openEdge_subset_edge l hj)).2
  have hd := T.shared_open_edges_halfplanes_disjoint hij k l hi hj
  exact ⟨(T.tile i).opposite_vertex_negative_of_disjoint_halfplanes
      (T.tile j) k l z hzP hzQ hd,
    (T.tile j).opposite_vertex_negative_of_disjoint_halfplanes
      (T.tile i) l k z hzQ hzP hd.symm⟩

end Erdos633
