import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafTerms
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryHomology
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalHomology
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Actual global total cohomology and its literal coface quotients

Global sections of the original total sheaves have the original signed
group differential. The comparison below is induced by the genuine
biproduct projections and the canonical abelian-group homology maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open CuspNormalization.SheafCohomologyResolution

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (X : TopCat.{0})

/-- The actual global additive diagram is literally the coface diagram. -/
theorem global_mapData :
    (categoryData X).mapData (globalSectionsFunctor X) =
      (globalData X).complexData := rfl

/-- The actual degree-one total global sections as their two original components. -/
def globalOneEquiv : (globalSectionsFunctor X).obj (I1 X) ≃+ (globalData X).One :=
  (categoryData X).oneEquiv (globalSectionsFunctor X)

/-- The actual degree-two total global sections as their three original components. -/
def globalTwoEquiv : (globalSectionsFunctor X).obj (I2 X) ≃+ (globalData X).Two :=
  (categoryData X).twoEquiv (globalSectionsFunctor X)

/-- The degree-one global short complex with its genuine component maps. -/
def globalOneIso : (oneComplex X).map (globalSectionsFunctor X) ≅
    (globalData X).complexData.oneComplex :=
  (categoryData X).mapOneIso (globalSectionsFunctor X)

/-- The degree-two global short complex with its genuine component maps. -/
def globalTwoIso : (twoComplex X).map (globalSectionsFunctor X) ≅
    (globalData X).complexData.twoComplex :=
  (categoryData X).mapTwoIso (globalSectionsFunctor X)

/-- Actual global degree-one homology as the original total cocycles modulo boundaries. -/
def globalOneQuotientIso : ((oneComplex X).map (globalSectionsFunctor X)).homology ≅
    AddCommGrpCat.of (globalData X).CohomologyOne :=
  ShortComplex.homologyMapIso (globalOneIso X) ≪≫ (globalData X).oneHomologyIso

/-- Actual global degree-two homology as the original total cocycles modulo boundaries. -/
def globalTwoQuotientIso : ((twoComplex X).map (globalSectionsFunctor X)).homology ≅
    AddCommGrpCat.of (globalData X).CohomologyTwo :=
  ShortComplex.homologyMapIso (globalTwoIso X) ≪≫ (globalData X).twoHomologyIso

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
