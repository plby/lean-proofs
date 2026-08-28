import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyHomotopy
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusMaps

/-!
# Radius naturality of actual source rotations and their homotopies

The compensated rotation uses radius-independent toric representatives.
The genuine central radius homeomorphism therefore commutes with each
rotation and with every point of its constructed homotopy, without any
small-drift assumption at either radius.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open CuspRetraction SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ : 0 < δ)

/-- Every actual source rotation commutes with the representative-preserving
central radius homeomorphism. -/
@[simp] theorem centralRadiusHomeomorph_sourceRotation (a : ℝ) (q : SourceModel (C 0)) :
    centralRadiusHomeomorph C r δ hδr hC hδ (sourceRotation C δ hδ a q) =
      sourceRotation C r (hδ.trans_le hδr) a q := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, centralRadiusHomeomorph_centralProject,
    sourceRotation_projection]

@[simp] theorem centralRadiusHomeomorph_symm_sourceRotation
    (a : ℝ) (q : SourceModel (C 0)) :
    (centralRadiusHomeomorph C r δ hδr hC hδ).symm
      (sourceRotation C r (hδ.trans_le hδr) a q) = sourceRotation C δ hδ a q := by
  apply (centralRadiusHomeomorph C r δ hδr hC hδ).injective
  rw [Homeomorph.apply_symm_apply, centralRadiusHomeomorph_sourceRotation]

theorem centralRadiusHomeomorph_comp_sourceRotation (a : ℝ) :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        (sourceRotation C δ hδ a) = sourceRotation C r (hδ.trans_le hδr) a := by
  apply ContinuousMap.ext
  intro q
  exact centralRadiusHomeomorph_sourceRotation C r δ hδr hC hδ a q

/-- The same equality holds jointly along the actual compensated-rotation homotopy. -/
@[simp] theorem centralRadiusHomeomorph_sourceRotationHomotopy
    (a : ℝ) (s : unitInterval) (q : SourceModel (C 0)) :
    centralRadiusHomeomorph C r δ hδr hC hδ (sourceRotationHomotopy C δ hδ a (s, q)) =
      sourceRotationHomotopy C r (hδ.trans_le hδr) a (s, q) :=
  centralRadiusHomeomorph_sourceRotation C r δ hδr hC hδ ((s : ℝ) * a) q

theorem centralRadiusHomeomorph_comp_sourceRotationHomotopy (a : ℝ) :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r)).comp
        (sourceRotationHomotopy C δ hδ a).toContinuousMap =
      (sourceRotationHomotopy C r (hδ.trans_le hδr) a).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, q⟩
  exact centralRadiusHomeomorph_sourceRotationHomotopy C r δ hδr hC hδ a s q

end Wikipedia.HopfProblem.CuspCentralHomology
