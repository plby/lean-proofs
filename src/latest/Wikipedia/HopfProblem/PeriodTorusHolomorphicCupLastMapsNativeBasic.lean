import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMapsHomology
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionNaturality
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMapsComposition

/-!
# The actual last-row map preserves the original native comparisons

The row has its proved Dolbeault acyclicity and the total complex has
its proved injective terms. Naturality of the original partial-resolution
comparison, with identity augmentation, identifies their actual maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open PeriodTorusHolomorphicCohomology SheafSingularCupComparison
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

local instance rowI0H1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Row.partialResolution p).I₀ 1) :=
  Row.I0_higher_subsingleton p 0

local instance rowI0H2 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Row.partialResolution p).I₀ 2) :=
  Row.I0_higher_subsingleton p 1

local instance rowI1H1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Row.partialResolution p).I₁ 1) :=
  Row.I1_higher_subsingleton p 0

local instance totalI0 : Injective (totalPartialResolution p).I₀ :=
  (totalOperators p).I0_injective

local instance totalI1 : Injective (totalPartialResolution p).I₁ :=
  (totalOperators p).I1_injective

local instance totalI0H1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (totalPartialResolution p).I₀ 1) :=
  injective_higher_subsingleton (totalPartialResolution p).I₀ 0

local instance totalI0H2 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (totalPartialResolution p).I₀ 2) :=
  injective_higher_subsingleton (totalPartialResolution p).I₀ 1

local instance totalI1H1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (totalPartialResolution p).I₁ 1) :=
  injective_higher_subsingleton (totalPartialResolution p).I₁ 0

/-- The actual first row homology map is the original native comparison square. -/
theorem one_homology :
    (Row.h1Iso p).hom ≫ ShortComplex.homologyMap (toTotal p).globalOneMap =
      (totalPartialResolution p).h1Iso.hom := by
  have h := (toTotal p).h1IsoAcyclic_naturality
  exact h.symm.trans (TotalNativeMaps.map_identity_comp
    (CategoryTheory.Sheaf.functorH _ 1) (holomorphicSheaf p)
    (totalPartialResolution p).h1Iso.hom)

/-- The actual second row homology map is the original native comparison square. -/
theorem two_homology :
    (Row.h2Iso p).hom ≫ ShortComplex.homologyMap (toTotal p).globalTwoMap =
      (totalPartialResolution p).h2Iso.hom := by
  have h := (toTotal p).h2IsoAcyclic_naturality
  exact h.symm.trans (TotalNativeMaps.map_identity_comp
    (CategoryTheory.Sheaf.functorH _ 2) (holomorphicSheaf p)
    (totalPartialResolution p).h2Iso.hom)

/-- The same genuine degree-one square after the canonical total quotient map. -/
theorem h1Iso_hom_comp : (Row.h1Iso p).hom ≫ oneHomologyMap p =
    (totalOperators p).nativeOneIso.hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : AddCommGrpCat.of (H p 1) ⟶
        (totalPartialResolution p).globalOneComplex.homology =>
      f ≫ (totalOperators p).ringOperators.globalOneQuotientIso.hom) (one_homology p))

/-- The same genuine degree-two square after the canonical total quotient map. -/
theorem h2Iso_hom_comp : (Row.h2Iso p).hom ≫ twoHomologyMap p =
    (totalOperators p).nativeTwoIso.hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : AddCommGrpCat.of (H p 2) ⟶
        (totalPartialResolution p).globalTwoComplex.homology =>
      f ≫ (totalOperators p).ringOperators.globalTwoQuotientIso.hom) (two_homology p))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps
