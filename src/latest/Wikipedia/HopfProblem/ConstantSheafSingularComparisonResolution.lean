import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalExact
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonFineCochains
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExt

/-!
# The original constant sheaf resolved by the genuine cochain sheaves

Local contractibility proves exactness of the actual augmented singular
cochain sheaf complex. Its degree-zero and degree-one terms have genuine
vanishing higher Ext cohomology on compact Hausdorff spaces. These are
proved properties of the original objects, not supplied cohomological
comparison hypotheses.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The actual augmented singular cochain sheaf resolution in the
native low-degree resolution interface. -/
def singularSheafResolution (hLC : LocallyContractibleSpace X) :
    LowExt.CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := ConstantSheafFirstCohomology.Constant.sheaf X A
  K := cochainSheafComplex X A
  ι := sheafAugmentation X A
  zero := sheafAugmentation_d X A
  initial_exact := LocalExact.initialSheafComplex_exact X A hLC
  exact_one := LocalExact.cochainSheafComplex_exactAt X A hLC 0
  exact_two := LocalExact.cochainSheafComplex_exactAt X A hLC 1
  mono_ι := LocalExact.sheafAugmentation_mono X A

/-- Genuine sheaf cohomology of the original constant sheaf is the
native degree-one cohomology of literal global cochain sheaf sections. -/
def constantSheafGlobalH1Iso [CompactSpace X] [T2Space X]
    (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 1) ≅
      (singularSheafResolution X A hLC).globalCochainComplex.homology 1 := by
  let R := singularSheafResolution X A hLC
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  exact R.h1Iso

/-- Genuine degree-two Ext cohomology of the original constant sheaf is
the actual degree-two cohomology of the original global section complex. -/
def constantSheafGlobalH2Iso [CompactSpace X] [T2Space X]
    (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 2) ≅
      (singularSheafResolution X A hLC).globalCochainComplex.homology 2 := by
  let R := singularSheafResolution X A hLC
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 1
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 1 0
  exact R.h2Iso

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
