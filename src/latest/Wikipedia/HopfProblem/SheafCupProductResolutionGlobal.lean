import Wikipedia.HopfProblem.SheafCupProductResolutionMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual global cocycles of a partial sheaf resolution

Global sections preserve the actual kernel of the last differential.
This gives genuine left-homology data for the original degree-two
global complex, with the actual truncated global cokernel as its homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} (R : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The literal degree-one complex of original global sections. -/
abbrev globalOneComplex : ShortComplex AddCommGrpCat :=
  R.oneComplex.map (globalSectionsFunctor X)

/-- The literal degree-two complex of original global sections. -/
abbrev globalTwoComplex : ShortComplex AddCommGrpCat :=
  R.twoComplex.map (globalSectionsFunctor X)

/-- The actual Γ comparison from the kernel-truncated complex to the original terms. -/
def globalTruncationInclusion : R.toAugmented.globalComplex ⟶ R.globalOneComplex :=
  (globalSectionsFunctor X).mapShortComplex.map R.truncationInclusion

/-- The right comparison is monomorphic and the first two are identities,
so the actual degree-one homology is unchanged by kernel truncation. -/
instance globalTruncationInclusion_homology_isIso :
    IsIso (ShortComplex.homologyMap R.globalTruncationInclusion) := by
  have : Epi R.globalTruncationInclusion.τ₁ := by
    change Epi ((globalSectionsFunctor X).map (𝟙 R.I₀))
    infer_instance
  have : IsIso R.globalTruncationInclusion.τ₂ := by
    change IsIso ((globalSectionsFunctor X).map (𝟙 R.I₁))
    infer_instance
  have : Mono R.globalTruncationInclusion.τ₃ := by
    change Mono ((globalSectionsFunctor X).map (kernel.ι R.d₂))
    infer_instance
  infer_instance

/-- Genuine global sections of the actual cycle sheaf equal the actual
kernel of the original global differential. -/
def globalKernelIso : (globalSectionsFunctor X).obj R.Z₂ ≅
    kernel R.globalTwoComplex.g :=
  PreservesKernel.iso (globalSectionsFunctor X) R.d₂

@[reassoc (attr := simp)] theorem globalKernelIso_hom_ι :
    R.globalKernelIso.hom ≫ kernel.ι R.globalTwoComplex.g =
      (globalSectionsFunctor X).map (kernel.ι R.d₂) := by
  change (PreservesKernel.iso (globalSectionsFunctor X) R.d₂).hom ≫
    kernel.ι ((globalSectionsFunctor X).map R.d₂) = _
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι R.d₂ (globalSectionsFunctor X)

/-- The global differential factors through this kernel by the literal comparison. -/
theorem globalToCyclesTwo_kernelIso :
    (globalSectionsFunctor X).map R.toCyclesTwo ≫ R.globalKernelIso.hom =
      kernel.lift R.globalTwoComplex.g R.globalTwoComplex.f R.globalTwoComplex.zero := by
  apply (cancel_mono (kernel.ι R.globalTwoComplex.g)).mp
  have hm : (globalSectionsFunctor X).map R.toCyclesTwo ≫
      (globalSectionsFunctor X).map (kernel.ι R.d₂) =
        (globalSectionsFunctor X).map R.d₁ :=
    ((globalSectionsFunctor X).map_comp R.toCyclesTwo (kernel.ι R.d₂)).symm.trans
      (congrArg (fun f => (globalSectionsFunctor X).map f) R.toCyclesTwo_ι)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (globalSectionsFunctor X).map R.toCyclesTwo ≫ f)
      R.globalKernelIso_hom_ι).trans
        (hm.trans (kernel.lift_ι R.globalTwoComplex.g R.globalTwoComplex.f
          R.globalTwoComplex.zero).symm))

/-- Actual left homology data for the original degree-two global complex. -/
def globalTwoHomologyData : R.globalTwoComplex.LeftHomologyData := by
  let G := globalSectionsFunctor X
  let i := G.map (kernel.ι R.d₂)
  let a := G.map R.toCyclesTwo
  have wi : i ≫ R.globalTwoComplex.g = 0 := by
    change G.map (kernel.ι R.d₂) ≫ G.map R.d₂ = 0
    rw [← G.map_comp, kernel.condition, G.map_zero]
  have wa : a ≫ i = R.globalTwoComplex.f := by
    change G.map R.toCyclesTwo ≫ G.map (kernel.ι R.d₂) = G.map R.d₁
    rw [← G.map_comp, toCyclesTwo_ι]
  have hi : (ShortComplex.mk i R.globalTwoComplex.g wi).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (isLimitOfHasKernelOfPreservesLimit G R.d₂)
  have hiMono : Mono i := by dsimp [i]; infer_instance
  have hpEpi : Epi (cokernel.π a) := inferInstance
  exact @leftHomologyDataOfExact AddCommGrpCat _ _ R.globalTwoComplex
    (G.obj R.Z₂) (cokernel a) i a (cokernel.π a)
    wi wa (cokernel.condition a) hi (ShortComplex.cokernelSequence_exact a) hiMono hpEpi

/-- The boundary in these actual homology data is the original global differential. -/
theorem globalTwoHomologyData_f' : R.globalTwoHomologyData.f' =
    (globalSectionsFunctor X).map R.toCyclesTwo := by
  apply (cancel_mono ((globalSectionsFunctor X).map (kernel.ι R.d₂))).mp
  exact R.globalTwoHomologyData.f'_i.trans
    (((globalSectionsFunctor X).map_comp R.toCyclesTwo (kernel.ι R.d₂)).symm.trans
      (congrArg (fun f => (globalSectionsFunctor X).map f) R.toCyclesTwo_ι)).symm

/-- The genuine truncated global cokernel is the homology of the original terms. -/
def globalTwoCokernelIso : cokernel R.toAugmented.globalComplex.g ≅
    R.globalTwoComplex.homology := R.globalTwoHomologyData.homologyIso.symm

/-- The comparison sends an actual cycle's cokernel class to that same actual cycle class. -/
theorem globalTwoCokernelIso_π :
    cokernel.π R.toAugmented.globalComplex.g ≫ R.globalTwoCokernelIso.hom =
      R.globalTwoHomologyData.cyclesIso.inv ≫ R.globalTwoComplex.homologyπ :=
  R.globalTwoHomologyData.π_comp_homologyIso_inv

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
