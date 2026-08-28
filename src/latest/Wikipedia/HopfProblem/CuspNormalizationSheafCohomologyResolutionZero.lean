import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Degree-zero comparison for an actual augmented resolution

The degree-zero group is identified with the actual kernel of the
first global differential, using left exactness of global sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace AugmentedResolution

variable {X : TopCat.{0}} (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The augmentation followed by the first differential, on literal
global sections. -/
abbrev globalInitialComplex : ShortComplex AddCommGrpCat :=
  (ShortComplex.mk R.ι R.complex.f R.zero).map (globalSectionsFunctor X)

theorem globalInitialComplex_exact : R.globalInitialComplex.Exact :=
  R.initial_exact.map_of_mono_of_preservesKernel (globalSectionsFunctor X)
    R.mono_ι inferInstance

/-- Actual global sections of the augmented sheaf are the kernel of
the first actual global differential. -/
def globalKernelIso : (globalSectionsFunctor X).obj R.F ≅ kernel R.globalComplex.f := by
  have : Mono ((globalSectionsFunctor X).map R.ι) := inferInstance
  have : Mono R.globalInitialComplex.f := ‹Mono ((globalSectionsFunctor X).map R.ι)›
  exact IsLimit.conePointUniqueUpToIso R.globalInitialComplex_exact.fIsKernel
    (limit.isLimit (parallelPair R.globalComplex.f 0))

theorem globalKernelIso_hom_ι :
    R.globalKernelIso.hom ≫ kernel.ι R.globalComplex.f =
      (globalSectionsFunctor X).map R.ι := by
  have : Mono ((globalSectionsFunctor X).map R.ι) := inferInstance
  have : Mono R.globalInitialComplex.f := ‹Mono ((globalSectionsFunctor X).map R.ι)›
  exact IsLimit.conePointUniqueUpToIso_hom_comp R.globalInitialComplex_exact.fIsKernel
    (limit.isLimit (parallelPair R.globalComplex.f 0)) WalkingParallelPair.zero

/-- Genuine degree-zero sheaf cohomology is the actual kernel of
the global-sections differential. -/
def h0Iso : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 0) ≅
    kernel R.globalComplex.f := h0GlobalIso R.F ≪≫ R.globalKernelIso

/-- The degree-zero comparison is induced by the actual augmentation. -/
theorem h0Iso_hom_ι : R.h0Iso.hom ≫ kernel.ι R.globalComplex.f =
    (h0GlobalIso R.F).hom ≫ (globalSectionsFunctor X).map R.ι := by
  change ((h0GlobalIso R.F).hom ≫ R.globalKernelIso.hom) ≫
    kernel.ι R.globalComplex.f = _
  rw [Category.assoc, R.globalKernelIso_hom_ι]
  rfl

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
