import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: StraightSegmentClosedBallGateCut]
lemma StraightSegmentClosedBallGateCut
    (p g v : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (hradiusPos : 0 < radius)
    (hgOpen : g ∈ openSegment ℝ p v)
    (hgSphere : g ∈ Metric.sphere p radius) :
    Metric.closedBall p radius ∩ segment ℝ p v = segment ℝ p g := by
-- BODY
  have hgOpenOriginal := hgOpen
  rw [openSegment_eq_image_lineMap] at hgOpen
  rcases hgOpen with ⟨t, ht, htg⟩
  have hdistPV : 0 < dist p v := by
    have hpv : p ≠ v := by
      intro hpv
      have : p = g := by
        rw [← htg, hpv]
        simp
      rw [← this, Metric.mem_sphere, dist_self] at hgSphere
      linarith
    exact dist_pos.mpr hpv
  have hradius : radius = t * dist p v := by
    rw [Metric.mem_sphere] at hgSphere
    calc
      radius = dist g p := hgSphere.symm
      _ = dist (AffineMap.lineMap p v t) p := by rw [htg]
      _ = t * dist p v := by
        rw [dist_lineMap_left, Real.norm_of_nonneg ht.1.le]
  apply Set.Subset.antisymm
  · rintro z ⟨hzBall, hzSeg⟩
    rw [segment_eq_image_lineMap] at hzSeg ⊢
    rcases hzSeg with ⟨s, hs, hsz⟩
    have hszdist : dist z p = s * dist p v := by
      rw [← hsz, dist_lineMap_left, Real.norm_of_nonneg hs.1]
    have hst : s ≤ t := by
      rw [Metric.mem_closedBall, hszdist, hradius] at hzBall
      nlinarith
    refine ⟨s / t, ⟨div_nonneg hs.1 ht.1.le,
      (div_le_one ht.1).mpr hst⟩, ?_⟩
    rw [← hsz, ← htg, AffineMap.lineMap_lineMap_right]
    congr 1
    exact div_mul_cancel₀ s ht.1.ne'
  · intro z hz
    refine ⟨?_, ?_⟩
    · exact (convex_closedBall p radius).segment_subset
        (by simpa [Metric.mem_closedBall] using hradiusPos.le)
        (Metric.sphere_subset_closedBall hgSphere) hz
    · exact (convex_segment p v).segment_subset
        (left_mem_segment ℝ p v)
        (openSegment_subset_segment ℝ p v hgOpenOriginal) hz
