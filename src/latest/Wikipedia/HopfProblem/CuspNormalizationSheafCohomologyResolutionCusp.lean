import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData
import Wikipedia.HopfProblem.CuspNormalizationSheafExactHolomorphic

/-!
# The actual cusp normalization resolution as augmented-resolution data

This package uses only the previously proved exact analytic stalk
sequence. It supplies no vanishing assumptions and changes none of the
sheaves or arrows.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace SheafCohomologyResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The genuine length-two exact normalization resolution of the
actual reduced holomorphic-function sheaf on the actual cusp fibre. -/
def normalizationAugmentedResolution :
    AugmentedResolution (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  F := reducedSheaf C ε hε hε1 hC hR
  complex := boundaryComplex C ε hε hε1 hC hR
  ι := normalizationPullback C ε hε hε1 hC hR
  zero := normalizationPullback_deltaZero C ε hε hε1 hC hR
  initial_exact := normalizationComplex_exact C ε hε hε1 hC hR
  exact := boundaryComplex_exact C ε hε hε1 hC hR
  mono_ι := normalizationPullback_mono C ε hε hε1 hC hR
  epi_g := deltaOne_epi C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
