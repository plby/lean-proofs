import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsGlobal

/-!
# The first-column quotient maps commute with the canonical homology comparisons

The actual algebraic homology maps agree with the original global
resolution maps followed by the original total biproduct comparison.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

private theorem homology_factor {S T U : ShortComplex AddCommGrpCat.{0}}
    (f : S ⟶ T) (e : T ≅ U) (m : S ⟶ U) (hm : m = f ≫ e.hom)
    {V : AddCommGrpCat.{0}} (k : U.homology ⟶ V) (v : S.homology ⟶ V)
    (h : ShortComplex.homologyMap m ≫ k = v) :
    v = ShortComplex.homologyMap f ≫ ShortComplex.homologyMap e.hom ≫ k :=
  h.symm.trans
    ((congrArg (fun n => ShortComplex.homologyMap n ≫ k) hm).trans
      ((congrArg (fun n => n ≫ k) (ShortComplex.homologyMap_comp f e.hom)).trans
        (Category.assoc _ _ _)))

variable (p : PeriodDomain)

theorem firstH1_homology :
    (SheafCupProductResolution.Coface.oneHomologyIso (sourceData p)).hom ≫
        AddCommGrpCat.ofHom (firstH1 p) =
      ShortComplex.homologyMap (firstToTotal p).globalOneMap ≫
        (totalOperators p).ringOperators.globalOneQuotientIso.hom :=
  homology_factor (firstToTotal p).globalOneMap
    (totalOperators p).ringOperators.globalOneIso (firstAlgebra p).oneComplexMap
    (firstOneComplexMap_eq p) _ _ (firstAlgebra p).oneHomologyIso_naturality

theorem firstH2_homology :
    (SheafCupProductResolution.Coface.twoHomologyIso (sourceData p)).hom ≫
        AddCommGrpCat.ofHom (firstH2 p) =
      ShortComplex.homologyMap (firstToTotal p).globalTwoMap ≫
        (totalOperators p).ringOperators.globalTwoQuotientIso.hom :=
  homology_factor (firstToTotal p).globalTwoMap
    (totalOperators p).ringOperators.globalTwoIso (firstAlgebra p).twoComplexMap
    (firstTwoComplexMap_eq p) _ _ (firstAlgebra p).twoHomologyIso_naturality

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
