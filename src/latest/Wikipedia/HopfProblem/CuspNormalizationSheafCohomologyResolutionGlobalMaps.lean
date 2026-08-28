import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionRepresentatives
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Maps of the literal global-section complexes

All section maps below come from the given sheaf maps. The comparison
with degree-zero Ext is the canonical one, including its naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace AugmentedResolution.Hom

variable {X : TopCat.{0}}
  {R S : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : Hom R S)

/-- The actual map of the literal global-section complexes. -/
def globalMap : R.globalComplex ⟶ S.globalComplex :=
  (globalSectionsFunctor X).mapShortComplex.map φ.complex

/-- The actual map of kernels of the first global differential. -/
def globalKernelMap : kernel R.globalComplex.f ⟶ kernel S.globalComplex.f :=
  kernel.map R.globalComplex.f S.globalComplex.f
    φ.globalMap.τ₁ φ.globalMap.τ₂ φ.globalMap.comm₁₂.symm

@[reassoc (attr := simp)] theorem globalKernelMap_ι :
    φ.globalKernelMap ≫ kernel.ι S.globalComplex.f =
      kernel.ι R.globalComplex.f ≫ (globalSectionsFunctor X).map φ.complex.τ₁ :=
  kernel.lift_ι _ _ _

/-- The actual map of cokernels of the last global differential. -/
def globalCokernelMap : cokernel R.globalComplex.g ⟶ cokernel S.globalComplex.g :=
  cokernel.map R.globalComplex.g S.globalComplex.g
    φ.globalMap.τ₂ φ.globalMap.τ₃ φ.globalMap.comm₂₃.symm

@[reassoc (attr := simp)] theorem globalCokernelMap_π :
    cokernel.π R.globalComplex.g ≫ φ.globalCokernelMap =
      (globalSectionsFunctor X).map φ.complex.τ₃ ≫ cokernel.π S.globalComplex.g :=
  cokernel.π_desc _ _ _

/-- The actual degree-zero Ext/global-section comparison is natural
as an isomorphism of the three-term complexes. -/
theorem extZeroGlobalIso_naturality :
    φ.extZeroMap (unitSheaf X) ≫ S.extZeroGlobalIso.hom =
      R.extZeroGlobalIso.hom ≫ φ.globalMap := by
  apply ShortComplex.hom_ext
  · exact h0GlobalIso_naturality φ.complex.τ₁
  · exact h0GlobalIso_naturality φ.complex.τ₂
  · exact h0GlobalIso_naturality φ.complex.τ₃

/-- The degree-zero comparison with the actual kernel commutes with
the genuine sheaf-cohomology map. -/
theorem h0Iso_naturality :
    (extFunctorObj (unitSheaf X) 0).map φ.augmentation ≫ S.h0Iso.hom =
      R.h0Iso.hom ≫ φ.globalKernelMap := by
  apply (cancel_mono (kernel.ι S.globalComplex.f)).mp
  have hleft : ((extFunctorObj (unitSheaf X) 0).map φ.augmentation ≫ S.h0Iso.hom) ≫
        kernel.ι S.globalComplex.f =
      (h0GlobalIso R.F).hom ≫ (globalSectionsFunctor X).map φ.augmentation ≫
        (globalSectionsFunctor X).map S.ι := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (extFunctorObj (unitSheaf X) 0).map φ.augmentation ≫ k)
        S.h0Iso_hom_ι).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ (globalSectionsFunctor X).map S.ι)
              (h0GlobalIso_naturality φ.augmentation)).trans (Category.assoc _ _ _))))
  have hright : (R.h0Iso.hom ≫ φ.globalKernelMap) ≫ kernel.ι S.globalComplex.f =
      (h0GlobalIso R.F).hom ≫ (globalSectionsFunctor X).map R.ι ≫
        (globalSectionsFunctor X).map φ.complex.τ₁ := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => R.h0Iso.hom ≫ k) φ.globalKernelMap_ι).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ (globalSectionsFunctor X).map φ.complex.τ₁)
            R.h0Iso_hom_ι).trans (Category.assoc _ _ _))))
  have hcomm : (globalSectionsFunctor X).map φ.augmentation ≫
        (globalSectionsFunctor X).map S.ι =
      (globalSectionsFunctor X).map R.ι ≫ (globalSectionsFunctor X).map φ.complex.τ₁ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm]
  exact hleft.trans ((congrArg (fun k => (h0GlobalIso R.F).hom ≫ k) hcomm).trans hright.symm)

end AugmentedResolution.Hom

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
