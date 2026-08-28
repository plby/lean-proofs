import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionGlobal

/-!
# Actual scalar actions on the normalization global kernel, homology, and cokernel

The module structures are the frozen canonical forgetful structures,
not modules transported through the dimension isomorphisms.
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

theorem globalKernelScalar_apply (c : ℂ)
    (a : ↥(kernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.f)) :
    (scalarResolutionHom C ε hε hε1 hC hR c).globalKernelMap a = c • a := by
  apply (globalKernelForgetLinearEquiv C ε hε hε1 hC hR).injective
  rw [map_smul]
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  let S := globalLinearComplex C ε hε hε1 hC hR
  have hm : (scalarResolutionHom C ε hε hε1 hC hR c).globalKernelMap =
      forgottenKernelScalarMap S c :=
    congrArg (fun φ : R.globalComplex ⟶ R.globalComplex =>
      kernel.map R.globalComplex.f R.globalComplex.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm)
      (globalScalarMap_eq C ε hε hε1 hC hR c)
  exact Eq.trans (congrArg (kernelForgetAddEquiv S) (ConcreteCategory.congr_hom hm a))
    (kernelForget_scalar S c a)

theorem globalHomologyScalar_apply (c : ℂ)
    (a : (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.homology) :
    ShortComplex.homologyMap (scalarResolutionHom C ε hε hε1 hC hR c).globalMap a =
      c • a := by
  apply (globalHomologyForgetLinearEquiv C ε hε hε1 hC hR).injective
  rw [map_smul]
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  let S := globalLinearComplex C ε hε hε1 hC hR
  have hm : ShortComplex.homologyMap (scalarResolutionHom C ε hε hε1 hC hR c).globalMap =
      ShortComplex.homologyMap (forgottenScalarMap S c) :=
    congrArg (fun φ : R.globalComplex ⟶ R.globalComplex => ShortComplex.homologyMap φ)
      (globalScalarMap_eq C ε hε hε1 hC hR c)
  exact Eq.trans (congrArg (homologyForgetAddEquiv S) (ConcreteCategory.congr_hom hm a))
    (homologyForget_scalar S c a)

theorem globalCokernelScalar_apply (c : ℂ)
    (a : ↥(cokernel (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex.g)) :
    (scalarResolutionHom C ε hε hε1 hC hR c).globalCokernelMap a = c • a := by
  apply (globalCokernelForgetLinearEquiv C ε hε hε1 hC hR).injective
  rw [map_smul]
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  let S := globalLinearComplex C ε hε hε1 hC hR
  have hm : (scalarResolutionHom C ε hε hε1 hC hR c).globalCokernelMap =
      forgottenCokernelScalarMap S c :=
    congrArg (fun φ : R.globalComplex ⟶ R.globalComplex =>
      cokernel.map R.globalComplex.g R.globalComplex.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm)
      (globalScalarMap_eq C ε hε hε1 hC hR c)
  exact Eq.trans (congrArg (cokernelForgetAddEquiv S) (ConcreteCategory.congr_hom hm a))
    (cokernelForget_scalar S c a)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
