import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma StraightSegmentPolygonalArc
    (a b : EuclideanSpace ℝ (Fin 2)) (hab : a ≠ b) :
    ∃ Γ : PolygonalArc,
      Γ.source = a ∧
        Γ.target = b ∧
          Γ.carrier = segment ℝ a b ∧
            Γ.relativeInterior = openSegment ℝ a b := by
  refine ⟨
    { vertices := [a, b]
      length_ge_two := by norm_num
      source := a
      target := b
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := segment ℝ a b
      relativeInterior := openSegment ℝ a b
      carrier_eq := ?_
      relativeInterior_eq := ?_
      simple_vertices := by simpa [List.pairwise_cons] using hab
      segment_intersections := ?_
      vertices_avoid_nonincident_interiors := ?_ },
    by simp⟩
  · ext p
    constructor
    · intro hp
      exact ⟨0, by norm_num, by simpa using hp⟩
    · rintro ⟨i, hi, hp⟩
      have hi' : i + 1 < 2 := by simpa using hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hp
  · ext p
    constructor
    · intro hp
      have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
      have hpa : p ≠ a := by
        intro h
        have hmem : a ∈ openSegment ℝ a b := by simpa [h] using hp
        exact hab ((left_mem_openSegment_iff (𝕜 := ℝ) (x := a) (y := b)).1 hmem)
      have hpb : p ≠ b := by
        intro h
        have hmem : b ∈ openSegment ℝ a b := by simpa [h] using hp
        exact hab ((right_mem_openSegment_iff (𝕜 := ℝ) (x := a) (y := b)).1 hmem)
      exact ⟨hpseg, by simp [hpa, hpb]⟩
    · intro hp
      have hpseg : p ∈ segment ℝ a b := hp.1
      have hpa : a ≠ p := by
        intro h
        exact hp.2 (by simp [h])
      have hpb : b ≠ p := by
        intro h
        exact hp.2 (by simp [h])
      exact mem_openSegment_of_ne_left_right hpa hpb hpseg
  · intro i j hi hj hij
    have hi' : i + 1 < 2 := by simpa using hi
    have hj' : j + 1 < 2 := by simpa using hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    omega
  · intro i k hi hk hki hkine
    have hi' : i + 1 < 2 := by simpa using hi
    have hk' : k < 2 := by simpa using hk
    have hi0 : i = 0 := by omega
    subst hi0
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · exact (hki rfl).elim
    · exact (hkine rfl).elim

