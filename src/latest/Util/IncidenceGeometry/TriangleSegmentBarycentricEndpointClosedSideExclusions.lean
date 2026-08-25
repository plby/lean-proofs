import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma TriangleSegmentBarycentricEndpointClosedSideExclusions
    (β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2))
    (hpOff :
      p ∉ segment ℝ (β 0) (β 1) ∧
        p ∉ segment ℝ (β 1) (β 2) ∧
          p ∉ segment ℝ (β 2) (β 0)) :
    ¬ (β.coord 2 p = 0 ∧ 0 ≤ β.coord 0 p ∧ 0 ≤ β.coord 1 p) ∧
      ¬ (β.coord 0 p = 0 ∧ 0 ≤ β.coord 1 p ∧ 0 ≤ β.coord 2 p) ∧
        ¬ (β.coord 1 p = 0 ∧ 0 ≤ β.coord 0 p ∧ 0 ≤ β.coord 2 p) := by
  have hseg01 :
      p ∈ segment ℝ (β 0) (β 1) ↔
        0 ≤ β.coord 0 p ∧ 0 ≤ β.coord 1 p ∧ β.coord 2 p = 0 := by
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
  have hseg12 :
      p ∈ segment ℝ (β 1) (β 2) ↔
        β.coord 0 p = 0 ∧ 0 ≤ β.coord 1 p ∧ 0 ≤ β.coord 2 p := by
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
  have hseg20 :
      p ∈ segment ℝ (β 2) (β 0) ↔
        0 ≤ β.coord 0 p ∧ β.coord 1 p = 0 ∧ 0 ≤ β.coord 2 p := by
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
  constructor
  · rintro ⟨h2, h0, h1⟩
    exact hpOff.1 ((hseg01).2 ⟨h0, h1, h2⟩)
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact hpOff.2.1 ((hseg12).2 ⟨h0, h1, h2⟩)
  · rintro ⟨h1, h0, h2⟩
    exact hpOff.2.2 ((hseg20).2 ⟨h0, h1, h2⟩)
