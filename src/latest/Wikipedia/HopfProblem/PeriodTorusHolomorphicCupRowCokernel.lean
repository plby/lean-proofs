import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowGlobal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionGlobalMaps

/-!
# Canonical kernel-zero and cokernel comparisons for the original row

The top sheaf is not replaced by coordinates. The actual kernel of its
zero outgoing map is identified with that same sheaf, and the induced
cokernel map sends each original top coefficient to its ordinary class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- Global sections of the genuine kernel-zero isomorphism. -/
def globalTopKernelIso :
    (globalSectionsFunctor (TopCat.of p.Torus)).obj (partialResolution p).Z₂ ≅
      (globalSectionsFunctor (TopCat.of p.Torus)).obj (Dolbeault.smoothSheaf p) :=
  (globalSectionsFunctor (TopCat.of p.Torus)).mapIso (topKernelIso p)

@[simp] theorem globalTopKernelIso_hom :
    (globalTopKernelIso p).hom =
      (globalSectionsFunctor (TopCat.of p.Torus)).map
        (kernel.ι (partialResolution p).d₂) := rfl

/-- The actual cokernel comparison induced by identity on pairs and the kernel inclusion. -/
def truncatedCokernelIso :
    cokernel (partialResolution p).toAugmented.globalComplex.g ≅
      cokernel (Dolbeault.resolution p).globalComplex.g := by
  refine cokernel.mapIso _ _ (Iso.refl _) (globalTopKernelIso p) ?_
  change (globalSectionsFunctor (TopCat.of p.Torus)).map (partialResolution p).toCyclesTwo ≫
      (globalSectionsFunctor (TopCat.of p.Torus)).map (kernel.ι (partialResolution p).d₂) =
    𝟙 _ ≫ (globalSectionsFunctor (TopCat.of p.Torus)).map (partialResolution p).d₁
  rw [Category.id_comp, ← Functor.map_comp, (partialResolution p).toCyclesTwo_ι]

@[reassoc] theorem truncatedCokernelIso_π :
    cokernel.π (partialResolution p).toAugmented.globalComplex.g ≫
        (truncatedCokernelIso p).hom =
      (globalTopKernelIso p).hom ≫ cokernel.π (Dolbeault.resolution p).globalComplex.g :=
  cokernel.π_desc _ _ _

/-- This is the very cokernel map induced by the original augmented-resolution morphism. -/
theorem truncatedCokernelIso_hom :
    (truncatedCokernelIso p).hom = (toOriginal p).globalCokernelMap := by
  apply (cancel_epi (cokernel.π (partialResolution p).toAugmented.globalComplex.g)).mp
  exact (truncatedCokernelIso_π p).trans (toOriginal p).globalCokernelMap_π.symm

/-- Canonical actual degree-two row homology as the original global Dolbeault cokernel. -/
def twoOriginalCokernelIso : (twoComplex p).homology ≅
    cokernel (Dolbeault.resolution p).globalComplex.g :=
  (partialResolution p).globalTwoCokernelIso.symm ≪≫ truncatedCokernelIso p

/-- The truncation's homology projection retains the literal included top coefficient. -/
theorem twoClass_of_kernel
    (k : (globalSectionsFunctor (TopCat.of p.Torus)).obj (partialResolution p).Z₂) :
    (partialResolution p).globalTwoCokernelIso.hom
        (cokernel.π (partialResolution p).toAugmented.globalComplex.g k) =
      twoClass p ((globalTopKernelIso p).hom k) := by
  have hc : (partialResolution p).globalTwoHomologyData.cyclesIso.inv k =
      twoCycle p ((globalTopKernelIso p).hom k) := by
    apply AddCommGrpCat.injective_of_mono (twoComplex p).iCycles
    exact (ConcreteCategory.congr_hom
      (partialResolution p).globalTwoHomologyData.cyclesIso_inv_comp_iCycles k).trans
        (twoCycle_i p ((globalTopKernelIso p).hom k)).symm
  exact (ConcreteCategory.congr_hom (partialResolution p).globalTwoCokernelIso_π k).trans
    (congrArg (twoComplex p).homologyπ hc)

/-- The canonical row-to-cokernel comparison has positive literal coefficient representatives. -/
theorem twoOriginalCokernelIso_class (s : Dolbeault.SmoothSection p ⊤) :
    (twoOriginalCokernelIso p).hom (twoClass p s) =
      cokernel.π (Dolbeault.resolution p).globalComplex.g s := by
  obtain ⟨k, rfl⟩ := (globalTopKernelIso p).addCommGroupIsoToAddEquiv.surjective s
  have hi := ConcreteCategory.congr_hom (partialResolution p).globalTwoCokernelIso.hom_inv_id
    (cokernel.π (partialResolution p).toAugmented.globalComplex.g k)
  change (truncatedCokernelIso p).hom
    ((partialResolution p).globalTwoCokernelIso.inv
      (twoClass p ((globalTopKernelIso p).hom k))) = _
  exact (congrArg (fun y => (truncatedCokernelIso p).hom
      ((partialResolution p).globalTwoCokernelIso.inv y)) (twoClass_of_kernel p k).symm).trans
    ((congrArg (truncatedCokernelIso p).hom hi).trans
      (ConcreteCategory.congr_hom (truncatedCokernelIso_π p) k))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
