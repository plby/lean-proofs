import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMapsAlgebra
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobalMaps
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsFunctor

/-!
# The original row maps on actual global sections

The canonical biproduct projections send the last-row injections to
the literal last coordinates. These are the actual section maps of
the genuine partial-resolution morphism.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open PeriodTorusHolomorphicCohomology SheafSingularCupComparison
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- The actual first row short complex maps into the literal total section complex. -/
def oneComplexMap : Row.oneComplex p ⟶ (totalData p).complexData.oneComplex :=
  (toTotal p).globalOneMap ≫ (totalOperators p).ringOperators.globalOneIso.hom

/-- The actual second row short complex maps into the literal total section complex. -/
def twoComplexMap : Row.twoComplex p ⟶ (totalData p).complexData.twoComplex :=
  (toTotal p).globalTwoMap ≫ (totalOperators p).ringOperators.globalTwoIso.hom

/-- The original pair unit has exactly the last two global coefficients. -/
theorem map1_global (s : Dolbeault.PairSection p ⊤) :
    (totalOperators p).ringOperators.globalOneEquiv
        ((globalSectionsFunctor (TopCat.of p.Torus)).map (map1 p) s) =
      (lastAlgebra p).mapOne s :=
  TotalMaps.oneEquiv_last (totalOperators p).categoryData
    (globalSectionsFunctor (TopCat.of p.Torus)) (Total.columnUnit1 p) s

/-- The original top coefficient unit is the unchanged final global coordinate. -/
theorem map2_global (s : Dolbeault.SmoothSection p ⊤) :
    (totalOperators p).ringOperators.globalTwoEquiv
        ((globalSectionsFunctor (TopCat.of p.Torus)).map (map2 p) s) =
      (lastAlgebra p).mapTwo s :=
  TotalMaps.twoEquiv_last (totalOperators p).categoryData
    (globalSectionsFunctor (TopCat.of p.Torus)) (Total.columnUnit2 p) s

theorem oneComplexMap_apply (s : Dolbeault.PairSection p ⊤) :
    (oneComplexMap p).τ₂ s = (lastAlgebra p).mapOne s :=
  map1_global p s

theorem twoComplexMap_apply (s : Dolbeault.SmoothSection p ⊤) :
    (twoComplexMap p).τ₂ s = (lastAlgebra p).mapTwo s :=
  map2_global p s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps
