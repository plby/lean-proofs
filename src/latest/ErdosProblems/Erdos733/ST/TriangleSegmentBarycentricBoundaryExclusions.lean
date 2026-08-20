import ErdosProblems.Erdos733.ST.TriangleAffineBasisBarycentricCoordinates

open Classical
noncomputable section

-- [TABLET NODE: TriangleSegmentBarycentricBoundaryExclusions]
lemma TriangleSegmentBarycentricBoundaryExclusions
    (β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2))
    (hxOff :
      x ∉ segment ℝ (β 0) (β 1) ∧
        x ∉ segment ℝ (β 1) (β 2) ∧
          x ∉ segment ℝ (β 2) (β 0))
    (hyOff :
      y ∉ segment ℝ (β 0) (β 1) ∧
        y ∉ segment ℝ (β 1) (β 2) ∧
          y ∉ segment ℝ (β 2) (β 0))
    (h0Miss : β 0 ∉ segment ℝ x y)
    (h1Miss : β 1 ∉ segment ℝ x y)
    (h2Miss : β 2 ∉ segment ℝ x y) :
    (¬ (0 < β.coord 0 x ∧ 0 < β.coord 1 x ∧ β.coord 2 x = 0) ∧
        ¬ (β.coord 0 x = 0 ∧ 0 < β.coord 1 x ∧ 0 < β.coord 2 x) ∧
          ¬ (0 < β.coord 0 x ∧ β.coord 1 x = 0 ∧ 0 < β.coord 2 x)) ∧
      (¬ (0 < β.coord 0 y ∧ 0 < β.coord 1 y ∧ β.coord 2 y = 0) ∧
        ¬ (β.coord 0 y = 0 ∧ 0 < β.coord 1 y ∧ 0 < β.coord 2 y) ∧
          ¬ (0 < β.coord 0 y ∧ β.coord 1 y = 0 ∧ 0 < β.coord 2 y)) ∧
      (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
        ¬ (β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
            β.coord 2 (AffineMap.lineMap x y t) = 0) ∧
          ¬ (β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
              β.coord 2 (AffineMap.lineMap x y t) = 0) ∧
            ¬ (β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
                β.coord 1 (AffineMap.lineMap x y t) = 0)) := by
-- BODY
  have hbary := TriangleAffineBasisBarycentricCoordinates β
  have endpointExclusions
      (p : EuclideanSpace ℝ (Fin 2))
      (hpOff :
        p ∉ segment ℝ (β 0) (β 1) ∧
          p ∉ segment ℝ (β 1) (β 2) ∧
            p ∉ segment ℝ (β 2) (β 0)) :
      ¬ (0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0) ∧
        ¬ (β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p) ∧
          ¬ (0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p) := by
    constructor
    · intro hp
      exact hpOff.1 (openSegment_subset_segment ℝ (β 0) (β 1) ((hbary.2.1 p).2 hp))
    constructor
    · intro hp
      exact hpOff.2.1 (openSegment_subset_segment ℝ (β 1) (β 2) ((hbary.2.2.1 p).2 hp))
    · intro hp
      exact hpOff.2.2 (openSegment_subset_segment ℝ (β 2) (β 0) ((hbary.2.2.2 p).2 hp))
  have parameterMemSegment
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      AffineMap.lineMap x y t ∈ segment ℝ x y := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
  have vertexExclusions
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      ¬ (β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
          β.coord 2 (AffineMap.lineMap x y t) = 0) ∧
        ¬ (β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
            β.coord 2 (AffineMap.lineMap x y t) = 0) ∧
          ¬ (β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
              β.coord 1 (AffineMap.lineMap x y t) = 0) := by
    let p : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap x y t
    have hpseg : p ∈ segment ℝ x y := parameterMemSegment t ht
    constructor
    · rintro ⟨h1, h2⟩
      have hsum := β.sum_coord_apply_eq_one p
      rw [Fin.sum_univ_three] at hsum
      have h0 : β.coord 0 p = 1 := by linarith
      have hp : p = β 0 := by
        apply β.ext_elem
        intro i
        fin_cases i
        · simp [p, h0]
        · simp [p, h1]
        · simp [p, h2]
      exact h0Miss (by simpa [hp] using hpseg)
    constructor
    · rintro ⟨h0, h2⟩
      have hsum := β.sum_coord_apply_eq_one p
      rw [Fin.sum_univ_three] at hsum
      have h1 : β.coord 1 p = 1 := by linarith
      have hp : p = β 1 := by
        apply β.ext_elem
        intro i
        fin_cases i
        · simp [p, h0]
        · simp [p, h1]
        · simp [p, h2]
      exact h1Miss (by simpa [hp] using hpseg)
    · rintro ⟨h0, h1⟩
      have hsum := β.sum_coord_apply_eq_one p
      rw [Fin.sum_univ_three] at hsum
      have h2 : β.coord 2 p = 1 := by linarith
      have hp : p = β 2 := by
        apply β.ext_elem
        intro i
        fin_cases i
        · simp [p, h0]
        · simp [p, h1]
        · simp [p, h2]
      exact h2Miss (by simpa [hp] using hpseg)
  exact ⟨endpointExclusions x hxOff, endpointExclusions y hyOff, vertexExclusions⟩
