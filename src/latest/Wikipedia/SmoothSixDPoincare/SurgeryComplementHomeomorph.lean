import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces

/-!
# The full attaching-core / belt-sphere complement homeomorphism

The radial exchange preserves exactly the incidences with the common
exterior. Gluing the two actual closed embedded covers therefore compares
the entire deleted complements, without a compactness assumption on them.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

theorem exchange_preserves_incidence (r : R) (p : UnitSphere E × PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      d.newExteriorMap r = d.newPuncturedMap (exchange E F p) := by
  rw [d.oldPunctured_overlap, d.newPunctured_overlap]
  constructor
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, exchange_boundary q.1 q.2⟩
  · rintro ⟨q, hr, hq⟩
    refine ⟨q, hr, (exchange E F).injective ?_⟩
    exact hq.trans (exchange_boundary q.1 q.2).symm

/-- The whole belt-sphere complement is homeomorphic to the old attaching-core complement. -/
def complementHomeomorph : d.OldComplement ≃ₜ d.NewComplement :=
  ClosedCover.homeomorphOfClosedPieces d.oldExteriorMap d.newExteriorMap
    d.oldPuncturedMap d.newPuncturedMap d.isClosedEmbedding_oldExteriorMap
    d.isClosedEmbedding_newExteriorMap d.isClosedEmbedding_oldPuncturedMap
    d.isClosedEmbedding_newPuncturedMap d.oldComplement_cover d.newComplement_cover
    (exchange E F) d.exchange_preserves_incidence

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
