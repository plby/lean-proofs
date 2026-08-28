import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionZeroLinear
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSections
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionZero

/-!
# Unconditional complex-linear computation of the actual reduced sheaf H⁰

The scalar module on H⁰ is the one induced by the original pointwise
endomorphisms of the reduced sheaf, not a module transported from ℂ.
No vanishing of positive-degree cohomology is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution SheafCohomologyResolution SheafCohomologyGlobalSections
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The existing pointwise complex module on actual reduced global sections. -/
instance reducedGlobal_module : Module ℂ (Sections (reducedSheaf C ε hε hε1 hC hR)) :=
  inferInstanceAs (Module ℂ (ReducedSections C ε hε hε1 hC hR ⊤))

/-- The actual Ext-zero/global-section comparison respects the pointwise scalar action. -/
def reducedH0GlobalLinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0 ≃ₗ[ℂ]
      Sections (reducedSheaf C ε hε hε1 hC hR) :=
  h0PointwiseLinearEquiv (reducedSheaf C ε hε hε1 hC hR)
    (reducedSheafScalarEnd C ε hε hε1 hC hR) (fun _ _ => rfl)

/-- Actual normalization pullback on global sections is complex linear. -/
def reducedGlobalPullbackLinearMap :
    Sections (reducedSheaf C ε hε hε1 hC hR) →ₗ[ℂ]
      Sections (normalizationSheaf C ε hε) where
  toFun := (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
    (normalizationPullback C ε hε hε1 hC hR)
  map_add' a b := map_add _ a b
  map_smul' c s := by
    let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    apply ContMDiffMap.ext
    intro x
    rfl

/-- Since the actual first global differential is zero, actual normalization pullback
identifies reduced global sections with normalization global sections. -/
def reducedNormalizationGlobalIso :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).obj
        (reducedSheaf C ε hε hε1 hC hR) ≅
      (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).obj
        (normalizationSheaf C ε hε) := by
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  have hz : R.globalComplex.f = 0 := deltaZero_global_eq_zero C ε hε hε1 hC hR
  letI : IsIso (kernel.ι R.globalComplex.f) := by
    rw [hz]
    infer_instance
  let hi : IsIso ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map R.ι) := by
    rw [← R.globalKernelIso_hom_ι]
    exact IsIso.comp_isIso' R.globalKernelIso.isIso_hom
      (show IsIso (kernel.ι R.globalComplex.f) from inferInstance)
  exact @asIso AddCommGrpCat _
    ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).obj R.F)
    ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).obj R.complex.X₁)
    ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map R.ι) hi

/-- The preceding isomorphism uses the original pointwise modules on both section groups. -/
def reducedNormalizationGlobalLinearEquiv :
    Sections (reducedSheaf C ε hε hε1 hC hR) ≃ₗ[ℂ]
      Sections (normalizationSheaf C ε hε) where
  __ := (reducedNormalizationGlobalIso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv
  map_smul' c s := (reducedGlobalPullbackLinearMap C ε hε hε1 hC hR).map_smul c s

/-- The actual reduced structure sheaf has H⁰ complex-linearly equal to ℂ,
unconditionally with respect to all positive-degree cohomology. -/
def reducedH0LinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0 ≃ₗ[ℂ] ℂ :=
  (reducedH0GlobalLinearEquiv C ε hε hε1 hC hR).trans
    ((reducedNormalizationGlobalLinearEquiv C ε hε hε1 hC hR).trans
      (normalizationGlobalLinearEquiv C ε hε))

/-- The H⁰ coefficient is actual evaluation after actual normalization pullback. -/
@[simp] theorem reducedH0LinearEquiv_apply
    (a : CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0) :
    reducedH0LinearEquiv C ε hε hε1 hC hR a =
      normalizationGlobalLinearEquiv C ε hε
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (normalizationPullback C ε hε hε1 hC hR)
          ((h0GlobalIso (reducedSheaf C ε hε hε1 hC hR)).hom a)) := rfl

/-- The actual scalar module on genuine H⁰ has dimension one. -/
theorem reducedH0_finrank :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0) = 1 :=
  (reducedH0LinearEquiv C ε hε hε1 hC hR).finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
