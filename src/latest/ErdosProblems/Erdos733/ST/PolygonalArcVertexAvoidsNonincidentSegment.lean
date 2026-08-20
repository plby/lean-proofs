import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcVertexAvoidsNonincidentSegment]
lemma PolygonalArcVertexAvoidsNonincidentSegment (γ : PolygonalArc)
    {i j : ℕ} (hi : i < γ.vertices.length)
    (hj : j + 1 < γ.vertices.length) (hij : i ≠ j) (hijs : i ≠ j + 1) :
    γ.vertices[i] ∉ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
-- BODY
  intro hseg
  rw [segment_eq_image_lineMap] at hseg
  rcases hseg with ⟨t, ht, htline⟩
  by_cases ht0eq : t = 0
  · have hpoint : γ.vertices[j] = γ.vertices[i] := by
      simpa [ht0eq] using htline
    have hidx : j = i :=
      (List.Nodup.getElem_inj_iff γ.simple_vertices).mp hpoint
    exact hij hidx.symm
  · by_cases ht1eq : t = 1
    · have hpoint : γ.vertices[j + 1] = γ.vertices[i] := by
        simpa [ht1eq] using htline
      have hidx : j + 1 = i :=
        (List.Nodup.getElem_inj_iff γ.simple_vertices).mp hpoint
      exact hijs hidx.symm
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0eq)
      have ht1 : t < 1 := lt_of_le_of_ne ht.2 ht1eq
      have hopen :
          γ.vertices[i] ∈ openSegment ℝ γ.vertices[j] γ.vertices[j + 1] := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨ht0, ht1⟩, htline⟩
      exact γ.vertices_avoid_nonincident_interiors hj hi hij hijs hopen
