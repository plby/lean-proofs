import Mathlib.Data.Set.Card.Arithmetic
import ErdosProblems.Erdos733.ST.AffineInterpolationInteriorZeroParity
import ErdosProblems.Erdos733.ST.Preamble
import ErdosProblems.Erdos733.ST.TriangleAffineBasisBarycentricCoordinates
import ErdosProblems.Erdos733.ST.TriangleNoncollinearAffineBasis
import ErdosProblems.Erdos733.ST.TriangleSegmentBarycentricBoundaryExclusions
import ErdosProblems.Erdos733.ST.TriangleSegmentBarycentricEndpointClosedSideExclusions
import ErdosProblems.Erdos733.ST.TriangleSegmentBarycentricSideParameterCounts
import ErdosProblems.Erdos733.ST.TriangleSegmentBarycentricSideParameterFiniteness
import ErdosProblems.Erdos733.ST.TriangleSegmentNoOverlapIntersectionSubsingleton
import ErdosProblems.Erdos733.ST.TriangleSegmentParametrizationInjective
import ErdosProblems.Erdos733.ST.ThreeCoordinateInsideToOutsideSideCountOdd
import ErdosProblems.Erdos733.ST.ThreeCoordinateOutsideToOutsideSideCountEven
import ErdosProblems.Erdos733.ST.ThreeCoordinateSideEventNonconstantOfFinite

open Classical
noncomputable section

-- [TABLET NODE: TriangleSegmentBoundaryParityToggle]
lemma TriangleSegmentBoundaryParityToggle
    (x y z a b : EuclideanSpace ℝ (Fin 2))
    (hxy : x ≠ y)
    (hza : z ≠ a) (hab : a ≠ b) (hbz : b ≠ z)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a))
    (hxOff : x ∉ segment ℝ z a ∧ x ∉ segment ℝ a b ∧ x ∉ segment ℝ b z)
    (hyOff : y ∉ segment ℝ z a ∧ y ∉ segment ℝ a b ∧ y ∉ segment ℝ b z)
    (hzMiss : z ∉ segment ℝ x y)
    (haMiss : a ∉ segment ℝ x y)
    (hbMiss : b ∉ segment ℝ x y)
    (hNoOverlapZA :
      ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
        u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ segment ℝ z a)
    (hNoOverlapAB :
      ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
        u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ segment ℝ a b)
    (hNoOverlapBZ :
      ¬ ∃ u v : EuclideanSpace ℝ (Fin 2),
        u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ segment ℝ b z)
    (hTransZA :
      ∀ w : EuclideanSpace ℝ (Fin 2),
        w ∈ openSegment ℝ x y →
          w ∈ openSegment ℝ z a →
            ¬ ∃ c : ℝ, a - z = c • (y - x))
    (hTransAB :
      ∀ w : EuclideanSpace ℝ (Fin 2),
        w ∈ openSegment ℝ x y →
          w ∈ openSegment ℝ a b →
            ¬ ∃ c : ℝ, b - a = c • (y - x))
    (hTransBZ :
      ∀ w : EuclideanSpace ℝ (Fin 2),
        w ∈ openSegment ℝ x y →
          w ∈ openSegment ℝ b z →
            ¬ ∃ c : ℝ, z - b = c • (y - x)) :
    Odd
      (Set.ncard (openSegment ℝ x y ∩ openSegment ℝ z a) +
        Set.ncard (openSegment ℝ x y ∩ openSegment ℝ a b) +
          Set.ncard (openSegment ℝ x y ∩ openSegment ℝ b z)) ↔
      decide
          (x ∈
            convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
              (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z)) ≠
        decide
          (y ∈
            convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
              (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z)) := by
-- BODY
  have hparam := TriangleSegmentParametrizationInjective x y hxy
  have hZA := TriangleSegmentNoOverlapIntersectionSubsingleton x y z a hNoOverlapZA
  have hAB := TriangleSegmentNoOverlapIntersectionSubsingleton x y a b hNoOverlapAB
  have hBZ := TriangleSegmentNoOverlapIntersectionSubsingleton x y b z hNoOverlapBZ
  have hfiniteZA :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ z a :
        Set (EuclideanSpace ℝ (Fin 2))) := hZA.2
  have hfiniteAB :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ a b :
        Set (EuclideanSpace ℝ (Fin 2))) := hAB.2
  have hfiniteBZ :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ b z :
        Set (EuclideanSpace ℝ (Fin 2))) := hBZ.2
  rcases TriangleNoncollinearAffineBasis z a b hza hncol with ⟨β, hβz, hβa, hβb⟩
  have hbary := TriangleAffineBasisBarycentricCoordinates β
  have htriangleInterior :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈
            convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
              (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z) ↔
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p := by
    intro p
    simpa [hβz, hβa, hβb] using hbary.1 p
  have hsideZA :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ z a ↔
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0 := by
    intro p
    simpa [hβz, hβa, hβb] using hbary.2.1 p
  have hsideAB :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ a b ↔
          β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p := by
    intro p
    simpa [hβz, hβa, hβb] using hbary.2.2.1 p
  have hsideBZ :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ b z ↔
          0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p := by
    intro p
    simpa [hβz, hβa, hβb] using hbary.2.2.2 p
  have hcoordLine :
      ∀ i : Fin 3, ∀ t : ℝ,
        β.coord i (AffineMap.lineMap x y t) =
          (1 - t) * β.coord i x + t * β.coord i y := by
    intro i t
    simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hparamCounts := TriangleSegmentBarycentricSideParameterCounts β x y hxy
  have hsingleCoordinateZeroParity :
      ∀ u v : ℝ, u ≠ 0 → v ≠ 0 →
        (Odd
            (Set.ncard
              {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - t) * u + t * v = 0}) ↔
          decide (0 < u) ≠ decide (0 < v)) :=
    AffineInterpolationInteriorZeroParity
  have hcoordinateZeroParity :
      ∀ i : Fin 3, β.coord i x ≠ 0 → β.coord i y ≠ 0 →
        (Odd
            (Set.ncard
              {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                β.coord i (AffineMap.lineMap x y t) = 0}) ↔
          decide (0 < β.coord i x) ≠ decide (0 < β.coord i y)) := by
    intro i hix hiy
    simpa [hcoordLine i] using
      hsingleCoordinateZeroParity (β.coord i x) (β.coord i y) hix hiy
  have hZA_params :
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ z a) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < β.coord 0 (AffineMap.lineMap x y t) ∧
            0 < β.coord 1 (AffineMap.lineMap x y t) ∧
            β.coord 2 (AffineMap.lineMap x y t) = 0} := by
    simpa [hβz, hβa, hβb] using hparamCounts.1
  have hAB_params :
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ a b) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
            0 < β.coord 1 (AffineMap.lineMap x y t) ∧
            0 < β.coord 2 (AffineMap.lineMap x y t)} := by
    simpa [hβz, hβa, hβb] using hparamCounts.2.1
  have hBZ_params :
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ b z) =
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < β.coord 0 (AffineMap.lineMap x y t) ∧
            β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
            0 < β.coord 2 (AffineMap.lineMap x y t)} := by
    simpa [hβz, hβa, hβb] using hparamCounts.2.2
  have hxOffβ :
      x ∉ segment ℝ (β 0) (β 1) ∧
        x ∉ segment ℝ (β 1) (β 2) ∧
          x ∉ segment ℝ (β 2) (β 0) := by
    simpa [hβz, hβa, hβb] using hxOff
  have hyOffβ :
      y ∉ segment ℝ (β 0) (β 1) ∧
        y ∉ segment ℝ (β 1) (β 2) ∧
          y ∉ segment ℝ (β 2) (β 0) := by
    simpa [hβz, hβa, hβb] using hyOff
  have hboundaryExclusions :=
    TriangleSegmentBarycentricBoundaryExclusions β x y hxOffβ hyOffβ
      (by simpa [hβz] using hzMiss)
      (by simpa [hβa] using haMiss)
      (by simpa [hβb] using hbMiss)
  have hfiniteZAβ :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 0) (β 1) :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [hβz, hβa] using hfiniteZA
  have hfiniteABβ :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 1) (β 2) :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [hβa, hβb] using hfiniteAB
  have hfiniteBZβ :
      Set.Finite (openSegment ℝ x y ∩ openSegment ℝ (β 2) (β 0) :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [hβb, hβz] using hfiniteBZ
  have hparameterSetFiniteness :=
    TriangleSegmentBarycentricSideParameterFiniteness β x y hxy
      hfiniteZAβ hfiniteABβ hfiniteBZβ
  have hxClosedSideExclusions :=
    TriangleSegmentBarycentricEndpointClosedSideExclusions β x hxOffβ
  have hyClosedSideExclusions :=
    TriangleSegmentBarycentricEndpointClosedSideExclusions β y hyOffβ
  have hxSideEndpointExclusions := hboundaryExclusions.1
  have hySideEndpointExclusions := hboundaryExclusions.2.1
  have hvertexParameterExclusions := hboundaryExclusions.2.2
  let u : Fin 3 → ℝ := fun i => β.coord i x
  let v : Fin 3 → ℝ := fun i => β.coord i y
  let Side (u v : Fin 3 → ℝ) (i : Fin 3) : Set ℝ :=
    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1 - t) * u i + t * v i = 0 ∧
        ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j}
  have hSide2_param :
      {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        0 < β.coord 0 (AffineMap.lineMap x y t) ∧
        0 < β.coord 1 (AffineMap.lineMap x y t) ∧
        β.coord 2 (AffineMap.lineMap x y t) = 0} =
        Side u v 2 := by
    ext t
    dsimp [Side]
    constructor
    · rintro ⟨ht, h0, h1, h2⟩
      refine ⟨ht, ?_, ?_⟩
      · simpa [u, v, ← hcoordLine 2 t] using h2
      · intro j hj
        fin_cases j
        · simpa [u, v, ← hcoordLine 0 t] using h0
        · simpa [u, v, ← hcoordLine 1 t] using h1
        · exact False.elim (hj rfl)
    · rintro ⟨ht, h2, hpos⟩
      refine ⟨ht, ?_, ?_, ?_⟩
      · simpa [u, v, hcoordLine 0 t] using hpos 0 (by decide)
      · simpa [u, v, hcoordLine 1 t] using hpos 1 (by decide)
      · simpa [u, v, hcoordLine 2 t] using h2
  have hSide0_param :
      {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        β.coord 0 (AffineMap.lineMap x y t) = 0 ∧
        0 < β.coord 1 (AffineMap.lineMap x y t) ∧
        0 < β.coord 2 (AffineMap.lineMap x y t)} =
        Side u v 0 := by
    ext t
    dsimp [Side]
    constructor
    · rintro ⟨ht, h0, h1, h2⟩
      refine ⟨ht, ?_, ?_⟩
      · simpa [u, v, ← hcoordLine 0 t] using h0
      · intro j hj
        fin_cases j
        · exact False.elim (hj rfl)
        · simpa [u, v, ← hcoordLine 1 t] using h1
        · simpa [u, v, ← hcoordLine 2 t] using h2
    · rintro ⟨ht, h0, hpos⟩
      refine ⟨ht, ?_, ?_, ?_⟩
      · simpa [u, v, hcoordLine 0 t] using h0
      · simpa [u, v, hcoordLine 1 t] using hpos 1 (by decide)
      · simpa [u, v, hcoordLine 2 t] using hpos 2 (by decide)
  have hSide1_param :
      {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
        0 < β.coord 0 (AffineMap.lineMap x y t) ∧
        β.coord 1 (AffineMap.lineMap x y t) = 0 ∧
        0 < β.coord 2 (AffineMap.lineMap x y t)} =
        Side u v 1 := by
    ext t
    dsimp [Side]
    constructor
    · rintro ⟨ht, h0, h1, h2⟩
      refine ⟨ht, ?_, ?_⟩
      · simpa [u, v, ← hcoordLine 1 t] using h1
      · intro j hj
        fin_cases j
        · simpa [u, v, ← hcoordLine 0 t] using h0
        · exact False.elim (hj rfl)
        · simpa [u, v, ← hcoordLine 2 t] using h2
    · rintro ⟨ht, h1, hpos⟩
      refine ⟨ht, ?_, ?_, ?_⟩
      · simpa [u, v, hcoordLine 0 t] using hpos 0 (by decide)
      · simpa [u, v, hcoordLine 1 t] using h1
      · simpa [u, v, hcoordLine 2 t] using hpos 2 (by decide)
  have hfiniteSide : ∀ i : Fin 3, (Side u v i).Finite := by
    intro i
    fin_cases i
    · change (Side u v 0).Finite
      rw [← hSide0_param]
      exact hparameterSetFiniteness.2.1
    · change (Side u v 1).Finite
      rw [← hSide1_param]
      exact hparameterSetFiniteness.2.2
    · change (Side u v 2).Finite
      rw [← hSide2_param]
      exact hparameterSetFiniteness.1
  have hfiniteSide_formula :
      ∀ i : Fin 3,
        Set.Finite
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * u i + t * v i = 0 ∧
              ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j} := by
    simpa [Side] using hfiniteSide
  have hNoDouble :
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ i j : Fin 3, i ≠ j →
          ¬ (((1 - t) * u i + t * v i = 0) ∧
              ((1 - t) * u j + t * v j = 0)) := by
    intro t ht i j hij hzero
    have hz0 (k : Fin 3) :
        (1 - t) * u k + t * v k = 0 →
          β.coord k (AffineMap.lineMap x y t) = 0 := by
      intro hk
      simpa [u, v, hcoordLine k t] using hk
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact (hvertexParameterExclusions t ht).2.2
        ⟨hz0 0 hzero.1, hz0 1 hzero.2⟩
    · exact (hvertexParameterExclusions t ht).2.1
        ⟨hz0 0 hzero.1, hz0 2 hzero.2⟩
    · exact (hvertexParameterExclusions t ht).2.2
        ⟨hz0 0 hzero.2, hz0 1 hzero.1⟩
    · exact hij rfl
    · exact (hvertexParameterExclusions t ht).1
        ⟨hz0 1 hzero.1, hz0 2 hzero.2⟩
    · exact (hvertexParameterExclusions t ht).2.1
        ⟨hz0 0 hzero.2, hz0 2 hzero.1⟩
    · exact (hvertexParameterExclusions t ht).1
        ⟨hz0 1 hzero.2, hz0 2 hzero.1⟩
    · exact hij rfl
  have hNonconstant_formula :
      ∀ i : Fin 3,
        ({t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
          (1 - t) * u i + t * v i = 0 ∧
            ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j} :
          Set ℝ).Nonempty →
          u i ≠ v i :=
    ThreeCoordinateSideEventNonconstantOfFinite u v hfiniteSide_formula
  have hcount_eq :
      Set.ncard (openSegment ℝ x y ∩ openSegment ℝ z a) +
        Set.ncard (openSegment ℝ x y ∩ openSegment ℝ a b) +
          Set.ncard (openSegment ℝ x y ∩ openSegment ℝ b z) =
        Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
          Set.ncard (Side u v 1) := by
    rw [hZA_params, hAB_params, hBZ_params]
    rw [hSide2_param, hSide0_param, hSide1_param]
  let XInside : Prop := ∀ i : Fin 3, 0 < u i
  let YInside : Prop := ∀ i : Fin 3, 0 < v i
  have hxMem_iff :
      x ∈
          convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
            (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z) ↔
        XInside := by
    rw [htriangleInterior x]
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> simpa [XInside, u]
    · intro hx
      exact ⟨by simpa [XInside, u] using hx 0,
        by simpa [XInside, u] using hx 1,
        by simpa [XInside, u] using hx 2⟩
  have hyMem_iff :
      y ∈
          convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
            (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z) ↔
        YInside := by
    rw [htriangleInterior y]
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> simpa [YInside, v]
    · intro hy
      exact ⟨by simpa [YInside, v] using hy 0,
        by simpa [YInside, v] using hy 1,
        by simpa [YInside, v] using hy 2⟩
  have hxNeg_of_not : ¬ XInside → ∃ i : Fin 3, u i < 0 := by
    intro hxnot
    by_contra hnoneg
    have hnonneg : ∀ i : Fin 3, 0 ≤ u i := by
      intro i
      exact le_of_not_gt (fun hi => hnoneg ⟨i, hi⟩)
    have hsome_nonpos : ∃ i : Fin 3, u i ≤ 0 := by
      by_contra hnone
      apply hxnot
      intro i
      exact lt_of_not_ge (fun hi => hnone ⟨i, hi⟩)
    rcases hsome_nonpos with ⟨i, hi⟩
    have hizero : u i = 0 := le_antisymm hi (hnonneg i)
    fin_cases i
    · exact hxClosedSideExclusions.2.1
        ⟨by simpa [u] using hizero,
          by simpa [u] using hnonneg 1,
          by simpa [u] using hnonneg 2⟩
    · exact hxClosedSideExclusions.2.2
        ⟨by simpa [u] using hizero,
          by simpa [u] using hnonneg 0,
          by simpa [u] using hnonneg 2⟩
    · exact hxClosedSideExclusions.1
        ⟨by simpa [u] using hizero,
          by simpa [u] using hnonneg 0,
          by simpa [u] using hnonneg 1⟩
  have hyNeg_of_not : ¬ YInside → ∃ i : Fin 3, v i < 0 := by
    intro hynot
    by_contra hnoneg
    have hnonneg : ∀ i : Fin 3, 0 ≤ v i := by
      intro i
      exact le_of_not_gt (fun hi => hnoneg ⟨i, hi⟩)
    have hsome_nonpos : ∃ i : Fin 3, v i ≤ 0 := by
      by_contra hnone
      apply hynot
      intro i
      exact lt_of_not_ge (fun hi => hnone ⟨i, hi⟩)
    rcases hsome_nonpos with ⟨i, hi⟩
    have hizero : v i = 0 := le_antisymm hi (hnonneg i)
    fin_cases i
    · exact hyClosedSideExclusions.2.1
        ⟨by simpa [v] using hizero,
          by simpa [v] using hnonneg 1,
          by simpa [v] using hnonneg 2⟩
    · exact hyClosedSideExclusions.2.2
        ⟨by simpa [v] using hizero,
          by simpa [v] using hnonneg 0,
          by simpa [v] using hnonneg 2⟩
    · exact hyClosedSideExclusions.1
        ⟨by simpa [v] using hizero,
          by simpa [v] using hnonneg 0,
          by simpa [v] using hnonneg 1⟩
  have hSide_empty_of_inside_inside
      (hxIn : XInside) (hyIn : YInside) :
      ∀ i : Fin 3, Side u v i = ∅ := by
    intro i
    ext t
    constructor
    · intro ht
      dsimp [Side] at ht
      have hpos : 0 < (1 - t) * u i + t * v i := by
        have ht0 := ht.1.1
        have ht1 := ht.1.2
        have hux := hxIn i
        have hvy := hyIn i
        nlinarith
      exact False.elim (lt_irrefl (0 : ℝ) (by simpa [ht.2.1] using hpos))
    · intro ht
      cases ht
  have hNoDouble_rev :
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ i j : Fin 3, i ≠ j →
          ¬ (((1 - t) * v i + t * u i = 0) ∧
              ((1 - t) * v j + t * u j = 0)) := by
    intro t ht i j hij hzero
    have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hz_i : (1 - (1 - t)) * u i + (1 - t) * v i = 0 := by
      convert hzero.1 using 1 <;> ring
    have hz_j : (1 - (1 - t)) * u j + (1 - t) * v j = 0 := by
      convert hzero.2 using 1 <;> ring
    exact hNoDouble (1 - t) ht' i j hij ⟨hz_i, hz_j⟩
  have hSide_reverse_image :
      ∀ i : Fin 3, Side v u i = (fun t : ℝ => 1 - t) '' Side u v i := by
    intro i
    ext s
    constructor
    · intro hs
      refine ⟨1 - s, ?_, by ring⟩
      dsimp [Side] at hs ⊢
      refine ⟨⟨by linarith [hs.1.1, hs.1.2], by linarith [hs.1.1, hs.1.2]⟩, ?_, ?_⟩
      · convert hs.2.1 using 1 <;> ring
      · intro j hji
        convert hs.2.2 j hji using 1 <;> ring
    · rintro ⟨t, ht, rfl⟩
      dsimp [Side] at ht ⊢
      refine ⟨⟨by linarith [ht.1.1, ht.1.2], by linarith [ht.1.1, ht.1.2]⟩, ?_, ?_⟩
      · convert ht.2.1 using 1 <;> ring
      · intro j hji
        convert ht.2.2 j hji using 1 <;> ring
  have hfiniteSide_rev : ∀ i : Fin 3, (Side v u i).Finite := by
    intro i
    rw [hSide_reverse_image i]
    exact (hfiniteSide i).image (fun t : ℝ => 1 - t)
  have hfiniteSide_rev_formula :
      ∀ i : Fin 3,
        Set.Finite
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * v i + t * u i = 0 ∧
              ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * v j + t * u j} := by
    simpa [Side] using hfiniteSide_rev
  have hreverse_ncard :
      ∀ i : Fin 3, Set.ncard (Side u v i) = Set.ncard (Side v u i) := by
    intro i
    refine Set.ncard_congr (fun t _ht => 1 - t) ?_ ?_ ?_
    · intro t ht
      dsimp [Side] at ht ⊢
      refine ⟨⟨by linarith [ht.1.1, ht.1.2], by linarith [ht.1.1, ht.1.2]⟩, ?_, ?_⟩
      · convert ht.2.1 using 1 <;> ring
      · intro j hji
        convert ht.2.2 j hji using 1 <;> ring
    · intro a b ha hb hab
      linarith
    · intro b hb
      refine ⟨1 - b, ?_, ?_⟩
      · dsimp [Side] at hb ⊢
        refine ⟨⟨by linarith [hb.1.1, hb.1.2], by linarith [hb.1.1, hb.1.2]⟩, ?_, ?_⟩
        · convert hb.2.1 using 1 <;> ring
        · intro j hji
          convert hb.2.2 j hji using 1 <;> ring
      · ring
  have hmain :
      Odd (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
          Set.ncard (Side u v 1)) ↔
        decide XInside ≠ decide YInside := by
    by_cases hxIn : XInside
    · by_cases hyIn : YInside
      · have hS0 := hSide_empty_of_inside_inside hxIn hyIn 0
        have hS1 := hSide_empty_of_inside_inside hxIn hyIn 1
        have hS2 := hSide_empty_of_inside_inside hxIn hyIn 2
        have hsum0 :
            Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1) = 0 := by
          rw [hS2, hS0, hS1]
          simp
        simp [hxIn, hyIn, hsum0]
      · have hyNeg := hyNeg_of_not hyIn
        have hodd :
            Odd (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1)) := by
          change
            Odd
              (Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * u 2 + t * v 2 = 0 ∧
                      ∀ j : Fin 3, j ≠ 2 → 0 < (1 - t) * u j + t * v j} +
                Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * u 0 + t * v 0 = 0 ∧
                      ∀ j : Fin 3, j ≠ 0 → 0 < (1 - t) * u j + t * v j} +
                  Set.ncard
                    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                      (1 - t) * u 1 + t * v 1 = 0 ∧
                        ∀ j : Fin 3, j ≠ 1 → 0 < (1 - t) * u j + t * v j})
          exact ThreeCoordinateInsideToOutsideSideCountOdd u v hxIn hyNeg
            hNoDouble hfiniteSide_formula
        simp [hxIn, hyIn, hodd]
    · by_cases hyIn : YInside
      · have hxNeg := hxNeg_of_not hxIn
        have hodd_rev :
            Odd (Set.ncard (Side v u 2) + Set.ncard (Side v u 0) +
                Set.ncard (Side v u 1)) := by
          change
            Odd
              (Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * v 2 + t * u 2 = 0 ∧
                      ∀ j : Fin 3, j ≠ 2 → 0 < (1 - t) * v j + t * u j} +
                Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * v 0 + t * u 0 = 0 ∧
                      ∀ j : Fin 3, j ≠ 0 → 0 < (1 - t) * v j + t * u j} +
                  Set.ncard
                    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                      (1 - t) * v 1 + t * u 1 = 0 ∧
                        ∀ j : Fin 3, j ≠ 1 → 0 < (1 - t) * v j + t * u j})
          exact ThreeCoordinateInsideToOutsideSideCountOdd v u hyIn hxNeg
            hNoDouble_rev hfiniteSide_rev_formula
        have hsum_rev :
            Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1) =
              Set.ncard (Side v u 2) + Set.ncard (Side v u 0) +
                Set.ncard (Side v u 1) := by
          rw [hreverse_ncard 2, hreverse_ncard 0, hreverse_ncard 1]
        have hodd :
            Odd (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1)) := by
          rwa [hsum_rev]
        simp [hxIn, hyIn, hodd]
      · have hxNeg := hxNeg_of_not hxIn
        have hyNeg := hyNeg_of_not hyIn
        have heven :
            Even (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1)) := by
          change
            Even
              (Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * u 2 + t * v 2 = 0 ∧
                      ∀ j : Fin 3, j ≠ 2 → 0 < (1 - t) * u j + t * v j} +
                Set.ncard
                  {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                    (1 - t) * u 0 + t * v 0 = 0 ∧
                      ∀ j : Fin 3, j ≠ 0 → 0 < (1 - t) * u j + t * v j} +
                  Set.ncard
                    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
                      (1 - t) * u 1 + t * v 1 = 0 ∧
                        ∀ j : Fin 3, j ≠ 1 → 0 < (1 - t) * u j + t * v j})
          exact ThreeCoordinateOutsideToOutsideSideCountEven u v hxNeg hyNeg
            hNoDouble hfiniteSide_formula hNonconstant_formula
        have hnotodd :
            ¬ Odd (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) +
                Set.ncard (Side u v 1)) :=
          (Nat.not_odd_iff_even).2 heven
        simp [hxIn, hyIn, hnotodd]
  rw [hcount_eq]
  simpa [hxMem_iff, hyMem_iff] using hmain
