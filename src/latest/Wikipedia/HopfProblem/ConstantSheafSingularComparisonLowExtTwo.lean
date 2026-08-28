import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernel

/-!
# Native degree-two sheaf cohomology from the actual cochain resolution
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

namespace CochainResolution

variable {X : TopCat.{0}} (R : CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- Global sections preserve the actual degree-two kernel, identifying
the final truncated cokernel with the full complex's native homology. -/
def globalSecondHomologyIso : cokernel R.truncation.globalComplex.g ≅
    R.globalCochainComplex.homology 2 :=
  CycleCokernel.cokernelIsoHomology₂ (globalSectionsFunctor X) R.K

/-- Genuine native degree-two sheaf cohomology is the actual
degree-two homology of global sections of the cochain resolution. -/
def h2Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ≅
      R.globalCochainComplex.homology 2 := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)›
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)›
  exact R.truncation.h2Iso ≪≫ R.globalSecondHomologyIso

end CochainResolution

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
