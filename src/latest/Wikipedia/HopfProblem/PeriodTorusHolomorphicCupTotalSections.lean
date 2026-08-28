import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalOperators
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraHomology
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryHomology

/-!
# The original section rings of the Godement--Dolbeault total diagram

The actual sheaf derivations and original ring cofaces supply the
proved signed total algebra on every open set. Global sections retain
the literal coefficient pairs and the genuine zero group in degree
three; the comparison uses the original biproduct projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.RingOperators

open SheafCupProduct CuspNormalization.SheafCohomologyResolution

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {X : TopCat.{0}} {F : GodementRing.RingSheaf X} (D : RingOperators F)

/-- Actual section operators, with their proved Leibniz and coface identities. -/
def sectionData (U : Opens X) : Algebra.Data
    ((GodementRing.term0 F).obj.obj (op U))
    ((GodementRing.term1 F).obj.obj (op U))
    ((GodementRing.term2 F).obj.obj (op U))
    ((GodementRing.term3 F).obj.obj (op U)) where
  cofaces := GodementRing.cofaceData F (GodementExact.sections (op U))
  deriv0 i := (D.deriv0 i).sectionMap U
  deriv1 i := (D.deriv1 i).sectionMap U
  deriv2 i := (D.deriv2 i).sectionMap U
  leibniz0 i := (D.deriv0 i).leibniz U
  leibniz1 i := (D.deriv1 i).leibniz U
  leibniz2 i := (D.deriv2 i).leibniz U
  commute0 s := congrArg (fun f => Derivation.sectionMap f U s) D.commute0
  commute1 s := congrArg (fun f => Derivation.sectionMap f U s) D.commute1
  coface0 i j s := (congrArg (fun f => Derivation.sectionMap f U s)
    (D.coface0 i j)).symm
  coface1 i j s := (congrArg (fun f => Derivation.sectionMap f U s)
    (D.coface1 i j)).symm

/-- The original global signed total algebra. -/
abbrev globalData := D.sectionData ⊤

/-- Global sections of the actual sheaf diagram are the literal algebraic diagram. -/
theorem global_mapData :
    D.categoryData.mapData (globalSectionsFunctor X) = D.globalData.complexData := rfl

/-- The original global degree-one terms with their actual two projections. -/
def globalOneEquiv :
    (globalSectionsFunctor X).obj D.categoryData.oneTerm ≃+ D.globalData.One :=
  D.categoryData.oneEquiv (globalSectionsFunctor X)

/-- The original global degree-two terms with their actual three projections. -/
def globalTwoEquiv :
    (globalSectionsFunctor X).obj D.categoryData.twoTerm ≃+ D.globalData.Two :=
  D.categoryData.twoEquiv (globalSectionsFunctor X)

/-- The actual first global short complex, with the original signed differential. -/
def globalOneIso : D.categoryData.oneComplex.map (globalSectionsFunctor X) ≅
    D.globalData.complexData.oneComplex :=
  D.categoryData.mapOneIso (globalSectionsFunctor X)

/-- The actual second global short complex, with the original signed differential. -/
def globalTwoIso : D.categoryData.twoComplex.map (globalSectionsFunctor X) ≅
    D.globalData.complexData.twoComplex :=
  D.categoryData.mapTwoIso (globalSectionsFunctor X)

/-- The canonical first homology-to-kernel/range comparison. -/
def globalOneQuotientIso :
    (D.categoryData.oneComplex.map (globalSectionsFunctor X)).homology ≅
      AddCommGrpCat.of D.globalData.CohomologyOne :=
  ShortComplex.homologyMapIso D.globalOneIso ≪≫ D.globalData.oneHomologyIso

/-- The canonical second homology-to-kernel/range comparison. -/
def globalTwoQuotientIso :
    (D.categoryData.twoComplex.map (globalSectionsFunctor X)).homology ≅
      AddCommGrpCat.of D.globalData.CohomologyTwo :=
  ShortComplex.homologyMapIso D.globalTwoIso ≪≫ D.globalData.twoHomologyIso

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.RingOperators
