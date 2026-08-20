import Mathlib.Data.Set.Card
import ErdosProblems.Erdos733.ST.TriangleAffineBasisBarycentricCoordinates
import ErdosProblems.Erdos733.ST.TriangleSegmentParametrizationInjective

open Classical
noncomputable section

-- [TABLET NODE: TriangleSegmentBarycentricSideParameterCounts]
lemma TriangleSegmentBarycentricSideParameterCounts
    (β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (x y : EuclideanSpace ℝ (Fin 2)) (hxy : x ≠ y) :
    Set.ncard (openSegment ℝ x y ∩ openSegment ℝ (β 0) (β 1)) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < β.coord 0 (AffineMap.lineMap x y t) ∧
            0 < β.coord 1 (AffineMap.lineMap x y t) ∧
            β.coord 2 (AffineMap.lineMap x y t) = 0} ∧
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ (β 1) (β 2)) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
            0 < β.coord 1 (AffineMap.lineMap x y t) ∧
            0 < β.coord 2 (AffineMap.lineMap x y t)} ∧
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ (β 2) (β 0)) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < β.coord 0 (AffineMap.lineMap x y t) ∧
            β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
            0 < β.coord 2 (AffineMap.lineMap x y t)} := by
-- BODY
  have hparam := (TriangleSegmentParametrizationInjective x y hxy).2
  have hbary := TriangleAffineBasisBarycentricCoordinates β
  have hcount
      (side : Set (EuclideanSpace ℝ (Fin 2)))
      (P : EuclideanSpace ℝ (Fin 2) → Prop)
      (hP : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ side ↔ P p) :
      Set.ncard (openSegment ℝ x y ∩ side) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            P (AffineMap.lineMap x y t)} := by
    let S : Set ℝ :=
      {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        P (AffineMap.lineMap x y t)}
    let T : Set (EuclideanSpace ℝ (Fin 2)) := openSegment ℝ x y ∩ side
    have hbij :
        Set.BijOn (fun t : ℝ => AffineMap.lineMap x y t) S T := by
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro t ht
        exact ⟨hparam.mapsTo ht.1, (hP _).2 ht.2⟩
      · intro t ht s hs hts
        exact hparam.injOn ht.1 hs.1 hts
      · intro p hp
        rcases hparam.surjOn hp.1 with ⟨t, ht, htp⟩
        refine ⟨t, ?_, htp⟩
        exact ⟨ht, (hP _).1 (by simpa [htp] using hp.2)⟩
    simpa [S, T] using hbij.ncard_eq.symm
  constructor
  · simpa [and_assoc] using
      hcount (openSegment ℝ (β 0) (β 1))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0)
        hbary.2.1
  constructor
  · simpa [and_assoc] using
      hcount (openSegment ℝ (β 1) (β 2))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p)
        hbary.2.2.1
  · simpa [and_assoc] using
      hcount (openSegment ℝ (β 2) (β 0))
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p)
        hbary.2.2.2
