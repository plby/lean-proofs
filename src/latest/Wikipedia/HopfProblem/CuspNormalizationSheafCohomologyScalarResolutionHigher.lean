import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionActions
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionComparison

/-!
# Linear resolution comparisons for the actual reduced cusp sheaf

Degree zero is unconditional. The degree-one and degree-two comparisons
are helper theorems with explicit acyclicity inputs on the actual terms.
They do not assert those analytic vanishing results or conditional cusp
cohomology dimensions as a completed computation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution SheafCohomologyResolution SheafCohomologyGlobalSections
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The frozen degree-zero comparison is linear for the actual pointwise scalar action. -/
def reducedH0KernelLinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0 ≃ₗ[ℂ]
      ↥(kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f) :=
  h0ResolutionLinearEquiv (normalizationAugmentedResolution C ε hε hε1 hC hR)
    (reducedSheafScalarEnd C ε hε hε1 hC hR) (scalarResolutionHom C ε hε hε1 hC hR)
    (fun _ => rfl) (globalKernelScalar_apply C ε hε hε1 hC hR)

/-- The genuine H¹/global-homology comparison is complex linear when the
actual normalization direct image has vanishing H¹. -/
def reducedH1GlobalLinearEquiv
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 1)] :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 ≃ₗ[ℂ]
      (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology := by
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 1))
  exact h1ResolutionLinearEquiv R (reducedSheafScalarEnd C ε hε hε1 hC hR)
    (scalarResolutionHom C ε hε hε1 hC hR) (fun _ => rfl)
    (globalHomologyScalar_apply C ε hε hε1 hC hR)

/-- The genuine H²/global-cokernel comparison is complex linear under its
explicit vanishing inputs on the actual normalization and boundary terms. -/
def reducedH2GlobalLinearEquiv
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (boundarySheaf C ε hε hε1 hC hR) 1)] :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 ≃ₗ[ℂ]
      ↥(cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g) := by
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 1))
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) 2))
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1) :=
    inferInstanceAs
      (Subsingleton (CategoryTheory.Sheaf.H.{0} (boundarySheaf C ε hε hε1 hC hR) 1))
  exact h2ResolutionLinearEquiv R (reducedSheafScalarEnd C ε hε hε1 hC hR)
    (scalarResolutionHom C ε hε hε1 hC hR) (fun _ => rfl)
    (globalCokernelScalar_apply C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
