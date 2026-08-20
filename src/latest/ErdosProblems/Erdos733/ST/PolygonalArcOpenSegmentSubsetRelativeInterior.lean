import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcOpenSegmentSubsetRelativeInterior]
lemma PolygonalArcOpenSegmentSubsetRelativeInterior (γ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < γ.vertices.length) :
    openSegment ℝ γ.vertices[j] γ.vertices[j + 1] ⊆ γ.relativeInterior := by
-- BODY
  intro z hzOpen
  have hseg : z ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
    openSegment_subset_segment ℝ γ.vertices[j] γ.vertices[j + 1] hzOpen
  have hcarrier : z ∈ γ.carrier := by
    rw [γ.carrier_eq]
    exact ⟨j, hj, hseg⟩
  rw [γ.relativeInterior_eq]
  refine ⟨hcarrier, ?_⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (hz_source | hz_target)
  · have h0lt : 0 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    have hsource : γ.vertices[0] = γ.source := by
      have hget : γ.vertices[0]? = some γ.vertices[0] :=
        List.getElem?_eq_getElem h0lt
      rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    have hsource_open : γ.vertices[0] ∈ openSegment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      simpa [hsource, hz_source] using hzOpen
    by_cases h0j : 0 = j
    · subst j
      have hne01 : γ.vertices[0] ≠ γ.vertices[0 + 1] := by
        intro hEq
        have hidx : (0 : ℕ) = 0 + 1 :=
          (γ.simple_vertices.getElem_inj_iff).mp hEq
        omega
      exact hne01 ((left_mem_openSegment_iff (𝕜 := ℝ)
        (x := γ.vertices[0]) (y := γ.vertices[0 + 1])).1
          (by simpa using hsource_open))
    · have h0j1 : 0 ≠ j + 1 := by omega
      exact γ.vertices_avoid_nonincident_interiors hj h0lt h0j h0j1 hsource_open
  · let last : ℕ := γ.vertices.length - 1
    have hlast_lt : last < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      dsimp [last]
      omega
    have htarget : γ.vertices[last] = γ.target := by
      have hlastEq := γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlastEq
      rw [List.getElem?_eq_getElem hlast_lt] at hlastEq
      exact Option.some.inj hlastEq
    have htarget_open : γ.vertices[last] ∈ openSegment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      simpa [htarget, hz_target] using hzOpen
    by_cases hlast_j : last = j
    · have : j + 1 < γ.vertices.length := hj
      dsimp [last] at hlast_j
      omega
    · by_cases hlast_j1 : last = j + 1
      · have htarget_open_right :
            γ.vertices[j + 1] ∈ openSegment ℝ γ.vertices[j] γ.vertices[j + 1] := by
          convert htarget_open using 2
          exact hlast_j1.symm
        have hne : γ.vertices[j] ≠ γ.vertices[j + 1] := by
          intro hEq
          have hidx : j = j + 1 :=
            (γ.simple_vertices.getElem_inj_iff).mp hEq
          omega
        exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)
          (x := γ.vertices[j]) (y := γ.vertices[j + 1])).1
            htarget_open_right)
      · exact γ.vertices_avoid_nonincident_interiors hj hlast_lt hlast_j hlast_j1
          htarget_open
