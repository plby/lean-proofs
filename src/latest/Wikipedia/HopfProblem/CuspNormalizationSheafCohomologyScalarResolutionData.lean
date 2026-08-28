import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionMorphisms
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionCusp
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Actual scalar endomorphisms of the augmented normalization resolution
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The pointwise scalar endomorphism of the actual normalization short complex. -/
def scalarBoundaryComplexMap (c : ℂ) :
    boundaryComplex C ε hε hε1 hC hR ⟶ boundaryComplex C ε hε hε1 hC hR where
  τ₁ := normalizationScalarEnd C ε hε c
  τ₂ := boundaryScalarEnd C ε hε hε1 hC hR c
  τ₃ := tripleScalarEnd C ε hε c
  comm₁₂ := deltaZero_scalar C ε hε hε1 hC hR c
  comm₂₃ := deltaOne_scalar C ε hε hε1 hC hR c

/-- Actual pointwise multiplication is a morphism of the whole augmented resolution. -/
def scalarResolutionHom (c : ℂ) :
    (normalizationAugmentedResolution C ε hε hε1 hC hR).Hom
      (normalizationAugmentedResolution C ε hε hε1 hC hR) where
  augmentation := reducedSheafScalarEnd C ε hε hε1 hC hR c
  complex := scalarBoundaryComplexMap C ε hε hε1 hC hR c
  comm := normalizationPullback_scalar C ε hε hε1 hC hR c

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
