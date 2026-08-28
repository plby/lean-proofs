import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsRanks

/-!
# Comparison with the literal abelian-group global complex

The forgetful functor preserves the actual kernels, cokernels, and homology.
Consequently the complex-linear calculation applies to the very global
complex used by the Ext-defined normalization resolution comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Canonical comparison of the actual global kernel with the underlying
abelian group of the complex-linear kernel. -/
def globalKernelForgetIso :
    kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f ≅
      (forget₂ (ModuleCat ℂ) AddCommGrpCat).obj
        (kernel (globalLinearComplex C ε hε hε1 hC hR).f) :=
  (PreservesKernel.iso (forget₂ (ModuleCat ℂ) AddCommGrpCat)
    (globalLinearComplex C ε hε hε1 hC hR).f).symm

/-- Canonical comparison of actual global homology with the underlying
abelian group of its complex-linear homology. -/
def globalHomologyForgetIso :
    (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology ≅
      (forget₂ (ModuleCat ℂ) AddCommGrpCat).obj
        (globalLinearComplex C ε hε hε1 hC hR).homology :=
  (globalLinearComplex C ε hε hε1 hC hR).mapHomologyIso
    (forget₂ (ModuleCat ℂ) AddCommGrpCat)

/-- Canonical comparison of the actual final global cokernel with its
complex-linear cokernel. -/
def globalCokernelForgetIso :
    cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g ≅
      (forget₂ (ModuleCat ℂ) AddCommGrpCat).obj
        (cokernel (globalLinearComplex C ε hε hε1 hC hR).g) :=
  (PreservesCokernel.iso (forget₂ (ModuleCat ℂ) AddCommGrpCat)
    (globalLinearComplex C ε hε hε1 hC hR).g).symm

/-- The literal abelian-group global kernel, ready for the Ext comparison. -/
def globalKernelAddIso :
    kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f ≅
      AddCommGrpCat.of ℂ :=
  globalKernelForgetIso C ε hε hε1 hC hR ≪≫
    (forget₂ (ModuleCat ℂ) AddCommGrpCat).mapIso (globalKernelIso C ε hε hε1 hC hR)

/-- The literal abelian-group global homology, ready for the Ext comparison. -/
def globalHomologyAddIso :
    (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology ≅
      AddCommGrpCat.of (Fin 2 → ℂ) :=
  globalHomologyForgetIso C ε hε hε1 hC hR ≪≫
    (forget₂ (ModuleCat ℂ) AddCommGrpCat).mapIso (globalHomologyIso C ε hε hε1 hC hR)

/-- The literal abelian-group final global cokernel, ready for the Ext comparison. -/
def globalCokernelAddIso :
    cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g ≅
      AddCommGrpCat.of ℂ :=
  globalCokernelForgetIso C ε hε hε1 hC hR ≪≫
    (forget₂ (ModuleCat ℂ) AddCommGrpCat).mapIso (globalCokernelIso C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
