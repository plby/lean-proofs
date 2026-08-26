import ErdosProblems.Erdos633b.CornerCoordinates

/-! Exact closed and open interval descriptions of a triangle's sector at
a shared outer corner, obtained by radial projection of its other vertices. -/

namespace Erdos633b.Triangle

noncomputable def cornerSection (T S : Triangle) (i j : Fin 3) : Set Plane :=
  segment ℝ (T.cornerProject i (S.points (j + 1))) (T.cornerProject i (S.points (j + 2)))

noncomputable def openCornerSection (T S : Triangle) (i j : Fin 3) : Set Plane :=
  openSegment ℝ (T.cornerProject i (S.points (j + 1))) (T.cornerProject i (S.points (j + 2)))

theorem coord_lineMap (S : Triangle) (j : Fin 3) (p q : Plane) (t : ℝ) :
    S.coord j (AffineMap.lineMap p q t) = (1 - t) * S.coord j p + t * S.coord j q := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]

theorem edge_convex (T : Triangle) (i : Fin 3) : Convex ℝ (T.edge i) :=
  T.support_convex.inter ((convex_singleton (0 : ℝ)).affine_preimage (T.coord i))

theorem cornerSection_subset_edge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) : T.cornerSection S i j ⊆ T.edge i := by
  apply (T.edge_convex i).segment_subset
  · exact T.cornerProject_mem_edge i (hST (S.vertex_mem_support (j + 1)))
      (T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  · exact T.cornerProject_mem_edge i (hST (S.vertex_mem_support (j + 2)))
      (T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))

theorem corner_section_lineMap (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) {q : Plane} (hq : q ∈ T.edge i) :
    AffineMap.lineMap (T.cornerProject i (S.points (j + 1)))
      (T.cornerProject i (S.points (j + 2)))
      (T.cornerScale i (S.points (j + 2)) * S.coord (j + 2) q) = q := by
  have hu := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 1)))
    (T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  have hv := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 2)))
    (T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))
  obtain ⟨hAa, hBa, hAb, hBb⟩ := T.cornerProject_pair_coords S i j hO
  have hs := T.corner_section_scale_identity S i j hO hq
  apply S.ext_coords_cyclic j
  · rw [S.coord_lineMap, hAa, hAb, mul_zero, add_zero]
    field_simp
    nlinarith
  · rw [S.coord_lineMap, hBa, hBb, mul_zero, zero_add]
    field_simp

theorem mem_cornerSection_iff (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) (q : Plane) :
    q ∈ T.cornerSection S i j ↔ q ∈ T.edge i ∧
      0 ≤ S.coord (j + 1) q ∧ 0 ≤ S.coord (j + 2) q := by
  have hu := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 1)))
    (T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  have hv := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 2)))
    (T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))
  obtain ⟨hAa, hBa, hAb, hBb⟩ := T.cornerProject_pair_coords S i j hO
  constructor
  · intro hq
    refine ⟨T.cornerSection_subset_edge S hST i j hO hq, ?_, ?_⟩
    · exact ((convex_Ici (0 : ℝ)).affine_preimage (S.coord (j + 1))).segment_subset
        (by simpa only [Set.mem_preimage, Set.mem_Ici, hAa] using (inv_pos.mpr hu).le)
        (by simp only [Set.mem_preimage, Set.mem_Ici, hAb, le_refl]) hq
    · exact ((convex_Ici (0 : ℝ)).affine_preimage (S.coord (j + 2))).segment_subset
        (by simp only [Set.mem_preimage, Set.mem_Ici, hBa, le_refl])
        (by simpa only [Set.mem_preimage, Set.mem_Ici, hBb] using (inv_pos.mpr hv).le) hq
  · rintro ⟨hq, hqa, hqb⟩
    have hs := T.corner_section_scale_identity S i j hO hq
    rw [← T.corner_section_lineMap S hST i j hO hq]
    exact lineMap_mem_segment ℝ _ _ ⟨mul_nonneg hv.le hqb, by nlinarith [mul_nonneg hu.le hqa]⟩

theorem mem_openCornerSection_iff (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) (q : Plane) :
    q ∈ T.openCornerSection S i j ↔ q ∈ T.edge i ∧
      0 < S.coord (j + 1) q ∧ 0 < S.coord (j + 2) q := by
  have hu := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 1)))
    (T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  have hv := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 2)))
    (T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))
  obtain ⟨hAa, hBa, hAb, hBb⟩ := T.cornerProject_pair_coords S i j hO
  constructor
  · intro hq
    refine ⟨T.cornerSection_subset_edge S hST i j hO (openSegment_subset_segment ℝ _ _ hq), ?_, ?_⟩
    · have h : S.coord (j + 1) q ∈
          openSegment ℝ (T.cornerScale i (S.points (j + 1)))⁻¹ 0 := by
        rw [← hAa, ← hAb, ← image_openSegment ℝ (S.coord (j + 1))]
        exact ⟨q, hq, rfl⟩
      rw [openSegment_symm, openSegment_eq_Ioo (inv_pos.mpr hu)] at h
      exact h.1
    · have h : S.coord (j + 2) q ∈
          openSegment ℝ 0 (T.cornerScale i (S.points (j + 2)))⁻¹ := by
        rw [← hBa, ← hBb, ← image_openSegment ℝ (S.coord (j + 2))]
        exact ⟨q, hq, rfl⟩
      rw [openSegment_eq_Ioo (inv_pos.mpr hv)] at h
      exact h.1
  · rintro ⟨hq, hqa, hqb⟩
    have hs := T.corner_section_scale_identity S i j hO hq
    rw [← T.corner_section_lineMap S hST i j hO hq]
    exact lineMap_mem_openSegment ℝ _ _ ⟨mul_pos hv hqb, by nlinarith [mul_pos hu hqa]⟩

end Erdos633b.Triangle
