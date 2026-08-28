import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsSheaf
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsFunctor
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobalMaps

/-!
# The first-column algebra maps are the original global sheaf maps

The original biproduct comparison evaluates the genuine first injection
to its literal first component. These identities identify the actual
maps of short complexes, retaining the original differentials.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct SheafSingularCupComparison
open CuspNormalization.SheafCohomologyResolution

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (p : PeriodDomain)

theorem firstOneComplexMap_eq :
    (firstAlgebra p).oneComplexMap = (firstToTotal p).globalOneMap ≫
      (totalOperators p).ringOperators.globalOneIso.hom := by
  apply ShortComplex.hom_ext
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun _ => rfl
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun a =>
      (TotalMaps.oneEquiv_first (totalOperators p).categoryData
        (globalSectionsFunctor (TopCat.of p.Torus))
        (GodementExact.I1Map (Derivation.inclusionRing p)) a).symm
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun a =>
      (TotalMaps.twoEquiv_first (totalOperators p).categoryData
        (globalSectionsFunctor (TopCat.of p.Torus))
        (GodementExact.I2Map (Derivation.inclusionRing p)) a).symm

theorem firstTwoComplexMap_eq :
    (firstAlgebra p).twoComplexMap = (firstToTotal p).globalTwoMap ≫
      (totalOperators p).ringOperators.globalTwoIso.hom := by
  apply ShortComplex.hom_ext
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun a =>
      (TotalMaps.oneEquiv_first (totalOperators p).categoryData
        (globalSectionsFunctor (TopCat.of p.Torus))
        (GodementExact.I1Map (Derivation.inclusionRing p)) a).symm
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun a =>
      (TotalMaps.twoEquiv_first (totalOperators p).categoryData
        (globalSectionsFunctor (TopCat.of p.Torus))
        (GodementExact.I2Map (Derivation.inclusionRing p)) a).symm
  · apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun a =>
      (TotalMaps.threeEquiv_first (totalOperators p).categoryData
        (globalSectionsFunctor (TopCat.of p.Torus))
        (GodementExact.I3Map (Derivation.inclusionRing p)) a).symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
