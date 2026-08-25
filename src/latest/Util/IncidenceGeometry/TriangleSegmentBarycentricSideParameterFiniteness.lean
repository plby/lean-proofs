import Mathlib.Data.Set.Finite.Basic
import Util.IncidenceGeometry.TriangleAffineBasisBarycentricCoordinates
import Util.IncidenceGeometry.TriangleSegmentParametrizationInjective

open Classical
noncomputable section

lemma TriangleSegmentBarycentricSideParameterFiniteness
    (β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2)) (hxy : x ≠ y)
    (hfiniteZA :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 0) (β 1) :
        Set (EuclideanSpace ℝ (Fin 2))))
    (hfiniteAB :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 1) (β 2) :
        Set (EuclideanSpace ℝ (Fin 2))))
    (hfiniteBZ :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 2) (β 0) :
        Set (EuclideanSpace ℝ (Fin 2)))) :
    Set.Finite
        {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
          0 < β.coord 0 (AffineMap.lineMap x y t) ∧
          0 < β.coord 1 (AffineMap.lineMap x y t) ∧
          β.coord 2 (AffineMap.lineMap x y t) = 0} ∧
      Set.Finite
        {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
          β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
          0 < β.coord 1 (AffineMap.lineMap x y t) ∧
          0 < β.coord 2 (AffineMap.lineMap x y t)} ∧
        Set.Finite
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < β.coord 0 (AffineMap.lineMap x y t) ∧
            β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
            0 < β.coord 2 (AffineMap.lineMap x y t)} := by
  have hparam := (TriangleSegmentParametrizationInjective x y hxy).2
  have hbary := TriangleAffineBasisBarycentricCoordinates β
  have hfiniteParam
      (side : Set (EuclideanSpace ℝ (Fin 2)))
      (P : EuclideanSpace ℝ (Fin 2) → Prop)
      (hP : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ side ↔ P p)
      (hfiniteSide : Set.Finite (openSegment ℝ x y ∩ side)) :
      Set.Finite
        {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
          P (AffineMap.lineMap x y t)} := by
    let S : Set ℝ :=
      {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        P (AffineMap.lineMap x y t)}
    have himage_subset :
        (fun t : ℝ => AffineMap.lineMap x y t) '' S ⊆
          openSegment ℝ x y ∩ side := by
      rintro p ⟨t, ht, rfl⟩
      exact ⟨hparam.mapsTo ht.1, (hP _).2 ht.2⟩
    have himage_finite :
        ((fun t : ℝ => AffineMap.lineMap x y t) '' S).Finite :=
      hfiniteSide.subset himage_subset
    have hinj :
        Set.InjOn (fun t : ℝ => AffineMap.lineMap x y t) S := by
      intro t ht s hs hts
      exact hparam.injOn ht.1 hs.1 hts
    simpa [S] using Set.Finite.of_finite_image himage_finite hinj
  constructor
  · exact
      hfiniteParam (openSegment ℝ (β 0) (β 1))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0)
        hbary.2.1 hfiniteZA
  constructor
  · exact
      hfiniteParam (openSegment ℝ (β 1) (β 2))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p)
        hbary.2.2.1 hfiniteAB
  · exact
      hfiniteParam (openSegment ℝ (β 2) (β 0))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p)
        hbary.2.2.2 hfiniteBZ
