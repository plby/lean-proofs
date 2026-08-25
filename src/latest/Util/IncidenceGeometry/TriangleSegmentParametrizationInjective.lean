import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma TriangleSegmentParametrizationInjective
    (x y : EuclideanSpace ℝ (Fin 2)) (hxy : x ≠ y) :
    Function.Injective
        (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} =>
          AffineMap.lineMap x y t.1) ∧
      Set.BijOn
        (fun t : ℝ => AffineMap.lineMap x y t)
        (Set.Ioo (0 : ℝ) 1) (openSegment ℝ x y) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    exact AffineMap.lineMap_injective (k := ℝ) hxy hst
  · refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    · intro s hs t ht hst
      exact AffineMap.lineMap_injective (k := ℝ) hxy hst
    · intro p hp
      rw [openSegment_eq_image_lineMap] at hp
      exact hp
