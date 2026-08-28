import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsForget

/-!
# Canonical complex modules on the original abelian-group global homology

These scalar structures are transported only across the forgetful
kernel/homology/cokernel comparisons, before using the dimension
calculation. Thus they retain the pointwise scalar structure of the
actual section complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

/-- Express a forgetful isomorphism with its original module as codomain. -/
def moduleForgetAddEquiv {A : AddCommGrpCat.{0}} {M : ModuleCat.{0} ℂ}
    (e : A ≅ (forget₂ (ModuleCat ℂ) AddCommGrpCat).obj M) : A ≃+ M :=
  e.addCommGroupIsoToAddEquiv

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The complex module on the literal first global kernel. -/
instance actualGlobalKernel_module :
    Module ℂ ↥(kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f) :=
  (moduleForgetAddEquiv (globalKernelForgetIso C ε hε hε1 hC hR)).module ℂ

/-- The complex module on the literal middle global homology. -/
instance actualGlobalHomology_module :
    Module ℂ (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology :=
  (moduleForgetAddEquiv (globalHomologyForgetIso C ε hε hε1 hC hR)).module ℂ

/-- The complex module on the literal last global cokernel. -/
instance actualGlobalCokernel_module :
    Module ℂ ↥(cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g) :=
  (moduleForgetAddEquiv (globalCokernelForgetIso C ε hε hε1 hC hR)).module ℂ

/-- The canonical first kernel comparison retains complex scalars. -/
def globalKernelForgetLinearEquiv :
    ↥(kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f) ≃ₗ[ℂ]
      ↥(kernel (globalLinearComplex C ε hε hε1 hC hR).f) :=
  (moduleForgetAddEquiv (globalKernelForgetIso C ε hε hε1 hC hR)).linearEquiv ℂ

/-- The canonical homology comparison retains complex scalars. -/
def globalHomologyForgetLinearEquiv :
    (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology ≃ₗ[ℂ]
      (globalLinearComplex C ε hε hε1 hC hR).homology :=
  (moduleForgetAddEquiv (globalHomologyForgetIso C ε hε hε1 hC hR)).linearEquiv ℂ

/-- The canonical final cokernel comparison retains complex scalars. -/
def globalCokernelForgetLinearEquiv :
    ↥(cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g) ≃ₗ[ℂ]
      ↥(cokernel (globalLinearComplex C ε hε hε1 hC hR).g) :=
  (moduleForgetAddEquiv (globalCokernelForgetIso C ε hε hε1 hC hR)).linearEquiv ℂ

/-- Dimension one for the kernel of the literal global section arrow. -/
theorem actualGlobalKernel_finrank :
    Module.finrank ℂ
      ↥(kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f) = 1 :=
  (globalKernelForgetLinearEquiv C ε hε hε1 hC hR).finrank_eq.trans
    (globalKernel_finrank C ε hε hε1 hC hR)

/-- Dimension two for the homology of the literal global section complex. -/
theorem actualGlobalHomology_finrank :
    Module.finrank ℂ
      (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology = 2 :=
  (globalHomologyForgetLinearEquiv C ε hε hε1 hC hR).finrank_eq.trans
    (globalHomology_finrank C ε hε hε1 hC hR)

/-- Dimension one for the cokernel of the literal final global section arrow. -/
theorem actualGlobalCokernel_finrank :
    Module.finrank ℂ
      ↥(cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g) = 1 :=
  (globalCokernelForgetLinearEquiv C ε hε hε1 hC hR).finrank_eq.trans
    (globalCokernel_finrank C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
