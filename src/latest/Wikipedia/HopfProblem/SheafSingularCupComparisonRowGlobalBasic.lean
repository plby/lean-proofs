import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingGlobal
import Wikipedia.HopfProblem.SheafCupProductResolutionCofaceNaturality
import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularCup

/-!
# Actual global row cochains and their original coface quotients

Global sections of the forgotten ring-cochain row have exactly the
literal alternating ring-coface differentials. The canonical homology
comparisons therefore preserve the original cocycle quotient classes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open CuspNormalization.SheafCohomologyResolution
open ResolutionRow RingCochains

variable (X : TopCat.{0})

/-- Literal global sections of the original first row window. -/
abbrev oneComplex : ShortComplex AddCommGrpCat.{0} :=
  (rowOneComplex X).map (globalSectionsFunctor X)

/-- Literal global sections of the original second row window. -/
abbrev twoComplex : ShortComplex AddCommGrpCat.{0} :=
  (rowTwoComplex X).map (globalSectionsFunctor X)

/-- The first global row differential is definitionally the original ring-coface differential. -/
def oneCofaceIso : oneComplex X ≅
    SheafCupProductResolution.Coface.oneComplex (globalData X) := Iso.refl _

/-- The second global row differential is definitionally the original ring-coface differential. -/
def twoCofaceIso : twoComplex X ≅
    SheafCupProductResolution.Coface.twoComplex (globalData X) := Iso.refl _

/-- Canonical global row H¹ identifies with the original global coface quotient. -/
def oneHomologyIso : (oneComplex X).homology ≅
    AddCommGrpCat.of (globalData X).CohomologyOne :=
  SheafCupProductResolution.Coface.oneHomologyIso (globalData X)

/-- Canonical global row H² identifies with the original global coface quotient. -/
def twoHomologyIso : (twoComplex X).homology ≅
    AddCommGrpCat.of (globalData X).CohomologyTwo :=
  SheafCupProductResolution.Coface.twoHomologyIso (globalData X)

def oneHomologyEquiv : (oneComplex X).homology ≃+ (globalData X).CohomologyOne :=
  (oneHomologyIso X).addCommGroupIsoToAddEquiv

def twoHomologyEquiv : (twoComplex X).homology ≃+ (globalData X).CohomologyTwo :=
  (twoHomologyIso X).addCommGroupIsoToAddEquiv

/-- Canonical first row classes retain their actual global section representative. -/
theorem oneHomologyIso_class :
    (oneComplex X).abCyclesIso.inv ≫ (oneComplex X).homologyπ ≫
        (oneHomologyIso X).hom = AddCommGrpCat.ofHom (globalData X).classOne :=
  SheafCupProductResolution.Coface.oneHomologyIso_class (globalData X)

/-- Canonical second row classes retain their actual global section representative. -/
theorem twoHomologyIso_class :
    (twoComplex X).abCyclesIso.inv ≫ (twoComplex X).homologyπ ≫
        (twoHomologyIso X).hom = AddCommGrpCat.ofHom (globalData X).classTwo :=
  SheafCupProductResolution.Coface.twoHomologyIso_class (globalData X)

theorem oneHomologyEquiv_class (a : (globalData X).CocycleOne) :
    oneHomologyEquiv X (Singular.shortClass (oneComplex X) a) =
      (globalData X).classOne a :=
  ConcreteCategory.congr_hom (oneHomologyIso_class X) a

theorem twoHomologyEquiv_class (a : (globalData X).CocycleTwo) :
    twoHomologyEquiv X (Singular.shortClass (twoComplex X) a) =
      (globalData X).classTwo a :=
  ConcreteCategory.congr_hom (twoHomologyIso_class X) a

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
