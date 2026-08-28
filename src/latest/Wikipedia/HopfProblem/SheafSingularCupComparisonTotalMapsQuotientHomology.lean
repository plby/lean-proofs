import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsQuotientBasic

/-!
# Quotient maps are the original native total homology maps

The canonical source and target quotient comparisons intertwine the
original global partial-resolution maps. These are equalities of the
original categorical homology maps, not comparison hypotheses.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open CuspNormalization.SheafCohomologyResolution

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

theorem firstH1_homology :
    (SheafCupProductResolution.Coface.oneHomologyIso (constantData X)).hom ≫
        AddCommGrpCat.ofHom (firstH1 X) =
      ShortComplex.homologyMap (firstToTotal X hLC).globalOneMap ≫
        (TotalSheaf.globalOneQuotientIso X).hom :=
  abQuotientMap_homology_comp
    ((globalSectionsFunctor X).mapShortComplex.map (firstOneSheafMap X))
    (TotalSheaf.globalOneIso X)

theorem firstH2_homology :
    (SheafCupProductResolution.Coface.twoHomologyIso (constantData X)).hom ≫
        AddCommGrpCat.ofHom (firstH2 X) =
      ShortComplex.homologyMap (firstToTotal X hLC).globalTwoMap ≫
        (TotalSheaf.globalTwoQuotientIso X).hom :=
  abQuotientMap_homology_comp
    ((globalSectionsFunctor X).mapShortComplex.map (firstTwoSheafMap X))
    (TotalSheaf.globalTwoIso X)

theorem lastH1_homology :
    (SheafCupProductResolution.Coface.oneHomologyIso (RingCochains.globalData X)).hom ≫
        AddCommGrpCat.ofHom (lastH1 X) =
      ShortComplex.homologyMap (lastToTotal X hLC).globalOneMap ≫
        (TotalSheaf.globalOneQuotientIso X).hom :=
  abQuotientMap_homology_comp
    ((globalSectionsFunctor X).mapShortComplex.map (lastOneSheafMap X))
    (TotalSheaf.globalOneIso X)

theorem lastH2_homology :
    (SheafCupProductResolution.Coface.twoHomologyIso (RingCochains.globalData X)).hom ≫
        AddCommGrpCat.ofHom (lastH2 X) =
      ShortComplex.homologyMap (lastToTotal X hLC).globalTwoMap ≫
        (TotalSheaf.globalTwoQuotientIso X).hom :=
  abQuotientMap_homology_comp
    ((globalSectionsFunctor X).mapShortComplex.map (lastTwoSheafMap X))
    (TotalSheaf.globalTwoIso X)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
