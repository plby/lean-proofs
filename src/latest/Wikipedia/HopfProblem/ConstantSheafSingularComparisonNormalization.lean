import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteSpaces
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteSpacesCusp
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsNormalization
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardCusp

/-!
# The actual normalization and its genuine degree-two kernel

The canonical constant-sheaf comparison intertwines the manuscript's
original normalization map on native Ext cohomology with the literal
pullback on original singular cohomology. Consequently it identifies
their actual categorical kernels, retaining the original inclusions.
Only the original cusp construction's geometric hypotheses occur.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspQuotient ToricSpace CuspNormalization.SheafResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The genuine normalization direct-image H¹ has the original singular
H¹ of the actual normalization component as its canonical target. -/
def normalizationH1TargetIso :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 1).obj (normalizationConstantSheaf C ε hε) ≅
      (singularCochainComplex (rayDivisor 0) (AddCommGrpCat.of ℂ)).homology 1 :=
  (normalizationConstantCohomologyEquiv C ε hε hε1 hC hR 1).toAddCommGrpIso ≪≫
    normalizationComplexSheafH1Iso

/-- The actual direct-image cohomology comparison and actual singular
comparison give the original normalization target in degree two. -/
def normalizationH2TargetIso :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 2).obj (normalizationConstantSheaf C ε hε) ≅
      (singularCochainComplex (rayDivisor 0) (AddCommGrpCat.of ℂ)).homology 2 :=
  (normalizationConstantCohomologyEquiv C ε hε hε1 hC hR 2).toAddCommGrpIso ≪≫
    normalizationComplexSheafH2Iso

/-- The canonical H¹ comparison is natural for the literal original
normalization constant-sheaf map and literal singular pullback. -/
@[reassoc]
theorem normalizationH1_naturality :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 1).map (normalizationConstantPullback C ε hε) ≫
        (normalizationH1TargetIso C ε hε hε1 hC hR).hom =
      (cuspComplexSheafH1Iso C ε hε hε1 hC hR).hom ≫
        HomologicalComplex.homologyMap
          (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 1 := by
  let := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  let := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ξ
  exact ConcreteCategory.congr_hom
    (PullbackExt.complex_h1_naturality (normalizationMap C ε hε)
      (normalization_isClosedMap C ε hε) (normalization_fibre_finite C ε hε hε1 hC hR)
      LocalContractibility.normalization_locallyContractibleSpace
      (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)) ξ

/-- The same square in degree two, with exactly the normalization map
appearing in the manuscript's native constant-sheaf resolution. -/
@[reassoc]
theorem normalizationH2_naturality :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 2).map (normalizationConstantPullback C ε hε) ≫
        (normalizationH2TargetIso C ε hε hε1 hC hR).hom =
      (cuspComplexSheafH2Iso C ε hε hε1 hC hR).hom ≫
        HomologicalComplex.homologyMap
          (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2 := by
  let := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  let := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ξ
  exact ConcreteCategory.congr_hom
    (PullbackExt.complex_h2_naturality (normalizationMap C ε hε)
      (normalization_isClosedMap C ε hε) (normalization_fibre_finite C ε hε hε1 hC hR)
      LocalContractibility.normalization_locallyContractibleSpace
      (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)) ξ

/-- The literal kernel of the original Ext normalization map is the
literal kernel of the original singular normalization pullback. -/
def normalizationH2KernelIso :
    kernel ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 2).map (normalizationConstantPullback C ε hε)) ≅
    kernel (HomologicalComplex.homologyMap
      (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2) :=
  kernel.mapIso _ _ (cuspComplexSheafH2Iso C ε hε hε1 hC hR)
    (normalizationH2TargetIso C ε hε hε1 hC hR)
    (normalizationH2_naturality C ε hε hε1 hC hR)

/-- The kernel comparison retains the actual cohomology inclusion and
the actual canonical constant-sheaf/singular comparison on the cusp. -/
@[reassoc]
theorem normalizationH2KernelIso_ι :
    (normalizationH2KernelIso C ε hε hε1 hC hR).hom ≫
      kernel.ι (HomologicalComplex.homologyMap
        (singularPullback (AddCommGrpCat.of ℂ) (normalizationMap C ε hε).hom) 2) =
    kernel.ι ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of (CentralSpace C ε))) 2).map (normalizationConstantPullback C ε hε)) ≫
      (cuspComplexSheafH2Iso C ε hε hε1 hC hR).hom :=
  kernel.lift_ι _ _ _

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
