import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionCusp
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionExact

/-!
# The actual constant-to-holomorphic map of augmented resolutions

These are the independently constructed constant resolution and the
literal inclusions into the holomorphic resolution. No acyclicity of
the constant normalization terms is asserted.
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

/-- The actual exact normalization resolution of the actual constant
complex sheaf on the actual cusp fibre. -/
def constantAugmentedResolution :
    AugmentedResolution (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  F := constantSheaf C ε
  complex := constantBoundaryComplex C ε hε hε1 hC hR
  ι := normalizationConstantPullback C ε hε
  zero := normalizationConstantPullback_constantDeltaZero C ε hε hε1 hC hR
  initial_exact := constantNormalizationComplex_exact C ε hε hε1 hC hR
  exact := constantBoundaryComplex_exact C ε hε hε1 hC hR
  mono_ι := normalizationConstantPullback_mono C ε hε
  epi_g := constantDeltaOne_epi C ε hε hε1 hC hR

/-- The genuine constants inclusion, as a commuting map of the two
actual augmented resolutions. Its last component is the identity. -/
def constantsAugmentedResolutionComparison :
    (constantAugmentedResolution C ε hε hε1 hC hR).Hom
      (normalizationAugmentedResolution C ε hε hε1 hC hR) where
  augmentation := reducedConstantsMap C ε hε hε1 hC hR
  complex := constantBoundaryComplexComparison C ε hε hε1 hC hR
  comm := normalization_constants_naturality C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
