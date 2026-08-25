import Mathlib.Tactic
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma SegmentSameRayInitialSubsegment
    (x d : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hd : d ≠ 0) (ha : 0 < a) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      x ≠ q ∧
        segment ℝ x q ⊆
          segment ℝ x (x + d) ∩ segment ℝ x (x + a • d) := by
  let c : ℝ := min 1 a / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    exact half_pos (lt_min zero_lt_one ha)
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hmin_le : min 1 a ≤ 1 := min_le_left 1 a
    nlinarith [lt_min zero_lt_one ha]
  have hc_le_a : c ≤ a := by
    dsimp [c]
    have hmin_le : min 1 a ≤ a := min_le_right 1 a
    nlinarith [lt_min zero_lt_one ha]
  let q : EuclideanSpace ℝ (Fin 2) := x + c • d
  have hq_ne : x ≠ q := by
    intro h
    have hzero : c • d = 0 := by
      have hsub := congrArg (fun y => y - x) h
      dsimp [q] at hsub
      have hzero' : (0 : EuclideanSpace ℝ (Fin 2)) = c • d := by
        simpa only [sub_self, add_sub_cancel_left] using hsub
      exact hzero'.symm
    exact (smul_ne_zero (ne_of_gt hc_pos) hd) hzero
  have hq1 : q ∈ segment ℝ x (x + d) := by
    rw [segment_eq_image_lineMap]
    refine ⟨c, ⟨hc_nonneg, hc_le_one⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    dsimp [q]
    module
  have hq2 : q ∈ segment ℝ x (x + a • d) := by
    rw [segment_eq_image_lineMap]
    refine ⟨c / a, ⟨div_nonneg hc_nonneg (le_of_lt ha), ?_⟩, ?_⟩
    · exact (div_le_one ha).2 hc_le_a
    · rw [AffineMap.lineMap_apply_module]
      dsimp [q]
      rw [smul_add]
      rw [← add_assoc]
      rw [← add_smul]
      have hcoeff : (1 - c / a + c / a : ℝ) = 1 := by ring
      have hcoeff2 : (c / a) * a = c := by
        field_simp [ne_of_gt ha]
      rw [hcoeff, one_smul]
      rw [← mul_smul, hcoeff2]
  refine ⟨q, hq_ne, ?_⟩
  intro y hy
  exact
    ⟨(convex_segment x (x + d)).segment_subset
        (left_mem_segment ℝ x (x + d)) hq1 hy,
      (convex_segment x (x + a • d)).segment_subset
        (left_mem_segment ℝ x (x + a • d)) hq2 hy⟩
