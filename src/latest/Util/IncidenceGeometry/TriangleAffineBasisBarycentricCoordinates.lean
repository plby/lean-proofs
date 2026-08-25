import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Between
import Util.IncidenceGeometry.Basic

open Classical
open Set
noncomputable section

lemma TriangleAffineBasisBarycentricCoordinates
    (β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈
            convexHull ℝ
                ({β 0, β 1, β 2} : Set (EuclideanSpace ℝ (Fin 2))) \
              (segment ℝ (β 0) (β 1) ∪ segment ℝ (β 1) (β 2) ∪
                segment ℝ (β 2) (β 0)) ↔
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ (β 0) (β 1) ↔
          0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ (β 1) (β 2) ↔
          β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ openSegment ℝ (β 2) (β 0) ↔
          0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p) := by
  have hrange :
      Set.range β =
        ({β 0, β 1, β 2} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro h
      rcases h with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  have hconv : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈
          convexHull ℝ
            ({β 0, β 1, β 2} : Set (EuclideanSpace ℝ (Fin 2))) ↔
        0 ≤ β.coord 0 p ∧ 0 ≤ β.coord 1 p ∧ 0 ≤ β.coord 2 p := by
    intro p
    rw [← hrange, β.convexHull_eq_nonneg_coord]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩
      intro i
      fin_cases i <;> assumption
  have hseg01 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ segment ℝ (β 0) (β 1) ↔
        0 ≤ β.coord 0 p ∧ 0 ≤ β.coord 1 p ∧ β.coord 2 p = 0 := by
    intro p
    constructor
    · intro hp
      rw [segment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 0) (β 1) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 0) (β 1) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 0) (β 1) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      exact ⟨by rw [h0]; linarith [ht.2], by rw [h1]; exact ht.1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      rw [segment_eq_image_lineMap]
      refine ⟨β.coord 1 p, ⟨h1, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
        · simp [AffineMap.apply_lineMap, h2]
  have hseg12 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ segment ℝ (β 1) (β 2) ↔
        β.coord 0 p = 0 ∧ 0 ≤ β.coord 1 p ∧ 0 ≤ β.coord 2 p := by
    intro p
    constructor
    · intro hp
      rw [segment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 1) (β 2) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 1) (β 2) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 1) (β 2) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      exact ⟨h0, by rw [h1]; linarith [ht.2], by rw [h2]; exact ht.1⟩
    · rintro ⟨h0, h1, h2⟩
      rw [segment_eq_image_lineMap]
      refine ⟨β.coord 2 p, ⟨h2, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, h0]
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hseg20 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ segment ℝ (β 2) (β 0) ↔
        0 ≤ β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 ≤ β.coord 2 p := by
    intro p
    constructor
    · intro hp
      rw [segment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 2) (β 0) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 2) (β 0) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 2) (β 0) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      exact ⟨by rw [h0]; exact ht.1, h1, by rw [h2]; linarith [ht.2]⟩
    · rintro ⟨h0, h1, h2⟩
      rw [segment_eq_image_lineMap]
      refine ⟨β.coord 0 p, ⟨h0, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
        · simp [AffineMap.apply_lineMap, h1]
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
  have hopen01 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ openSegment ℝ (β 0) (β 1) ↔
        0 < β.coord 0 p ∧ 0 < β.coord 1 p ∧ β.coord 2 p = 0 := by
    intro p
    constructor
    · intro hp
      rw [openSegment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 0) (β 1) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 0) (β 1) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 0) (β 1) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      exact ⟨by rw [h0]; linarith [ht.2], by rw [h1]; exact ht.1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨β.coord 1 p, ⟨h1, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
        · simp [AffineMap.apply_lineMap, h2]
  have hopen12 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ openSegment ℝ (β 1) (β 2) ↔
        β.coord 0 p = 0 ∧ 0 < β.coord 1 p ∧ 0 < β.coord 2 p := by
    intro p
    constructor
    · intro hp
      rw [openSegment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 1) (β 2) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 1) (β 2) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 1) (β 2) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      exact ⟨h0, by rw [h1]; linarith [ht.2], by rw [h2]; exact ht.1⟩
    · rintro ⟨h0, h1, h2⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨β.coord 2 p, ⟨h2, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, h0]
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hopen20 : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ openSegment ℝ (β 2) (β 0) ↔
        0 < β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 < β.coord 2 p := by
    intro p
    constructor
    · intro hp
      rw [openSegment_eq_image_lineMap] at hp
      rcases hp with ⟨t, ht, rfl⟩
      have h0 :
          β.coord 0 (AffineMap.lineMap (β 2) (β 0) t) = t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      have h1 :
          β.coord 1 (AffineMap.lineMap (β 2) (β 0) t) = 0 := by
        simp [AffineMap.apply_lineMap]
      have h2 :
          β.coord 2 (AffineMap.lineMap (β 2) (β 0) t) = 1 - t := by
        simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
      exact ⟨by rw [h0]; exact ht.1, h1, by rw [h2]; linarith [ht.2]⟩
    · rintro ⟨h0, h1, h2⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨β.coord 0 p, ⟨h0, ?_⟩, ?_⟩
      · have hsum := β.sum_coord_apply_eq_one p
        rw [Fin.sum_univ_three] at hsum
        linarith
      · apply β.ext_elem
        intro i
        fin_cases i
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
        · simp [AffineMap.apply_lineMap, h1]
        · simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
          have hsum := β.sum_coord_apply_eq_one p
          rw [Fin.sum_univ_three] at hsum
          linarith
  refine ⟨?_, hopen01, hopen12, hopen20⟩
  intro p
  constructor
  · rintro ⟨hpconv, hpnot⟩
    have hnonneg := (hconv p).1 hpconv
    have hc0_ne : β.coord 0 p ≠ 0 := by
      intro hc0
      exact hpnot (by
        left
        right
        exact (hseg12 p).2 ⟨hc0, hnonneg.2.1, hnonneg.2.2⟩)
    have hc1_ne : β.coord 1 p ≠ 0 := by
      intro hc1
      exact hpnot (by
        right
        exact (hseg20 p).2 ⟨hnonneg.1, hc1, hnonneg.2.2⟩)
    have hc2_ne : β.coord 2 p ≠ 0 := by
      intro hc2
      exact hpnot (by
        left
        left
        exact (hseg01 p).2 ⟨hnonneg.1, hnonneg.2.1, hc2⟩)
    exact ⟨lt_of_le_of_ne hnonneg.1 hc0_ne.symm,
      lt_of_le_of_ne hnonneg.2.1 hc1_ne.symm,
      lt_of_le_of_ne hnonneg.2.2 hc2_ne.symm⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨(hconv p).2 ⟨h0.le, h1.le, h2.le⟩, ?_⟩
    rintro ((hp01 | hp12) | hp20)
    · exact h2.ne' ((hseg01 p).1 hp01).2.2
    · exact h0.ne' ((hseg12 p).1 hp12).1
    · exact h1.ne' ((hseg20 p).1 hp20).2.1
