import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskChordEndpointParameters]
lemma EndpointUnitDiskChordEndpointParameters
    {A B z u v : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hz : z = AffineMap.lineMap A B t) (ht0 : 0 < t) (ht1 : t < 1)
    (hu : u ∈ openSegment ℝ A z) (hv : v ∈ openSegment ℝ z B) :
    (∃ s : ℝ, 0 < s ∧ s < t ∧ u = AffineMap.lineMap A B s) ∧
      (∃ s : ℝ, t < s ∧ s < 1 ∧ v = AffineMap.lineMap A B s) := by
-- BODY
  constructor
  · rw [openSegment_eq_image_lineMap] at hu
    rcases hu with ⟨θ, hθ, hθu⟩
    refine ⟨θ * t, mul_pos hθ.1 ht0, ?_, ?_⟩
    · nlinarith [hθ.2, ht0]
    · rw [← hθu, hz]
      ext k
      simp [AffineMap.lineMap_apply_module]
      ring
  · rw [openSegment_eq_image_lineMap] at hv
    rcases hv with ⟨θ, hθ, hθv⟩
    refine ⟨t + θ * (1 - t), ?_, ?_, ?_⟩
    · nlinarith [hθ.1, ht1]
    · nlinarith [hθ.2, ht1]
    · rw [← hθv, hz]
      ext k
      simp [AffineMap.lineMap_apply_module]
      ring
