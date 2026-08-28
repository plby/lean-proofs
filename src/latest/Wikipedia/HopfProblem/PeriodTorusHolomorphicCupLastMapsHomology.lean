import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMapsGlobal

/-!
# Original Dolbeault row classes in the actual total quotient

The maps are induced by the genuine global short-complex maps. The
canonical kernel and quotient comparisons preserve the original pair
and top-coefficient representatives, including the positive top sign.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open PeriodTorusHolomorphicCohomology SheafSingularCupComparison

variable (p : PeriodDomain)

/-- Actual first row homology followed by the original total quotient comparison. -/
def oneHomologyMap : (Row.oneComplex p).homology ⟶
    AddCommGrpCat.of (totalData p).CohomologyOne :=
  ShortComplex.homologyMap (toTotal p).globalOneMap ≫
    (totalOperators p).ringOperators.globalOneQuotientIso.hom

/-- Actual second row homology followed by the original total quotient comparison. -/
def twoHomologyMap : (Row.twoComplex p).homology ⟶
    AddCommGrpCat.of (totalData p).CohomologyTwo :=
  ShortComplex.homologyMap (toTotal p).globalTwoMap ≫
    (totalOperators p).ringOperators.globalTwoQuotientIso.hom

theorem oneHomologyMap_eq : oneHomologyMap p =
    ShortComplex.homologyMap (oneComplexMap p) ≫ (totalData p).oneHomologyIso.hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : (Row.oneComplex p).homology ⟶
        (totalData p).complexData.oneComplex.homology =>
      f ≫ (totalData p).oneHomologyIso.hom)
      (ShortComplex.homologyMap_comp (toTotal p).globalOneMap
        (totalOperators p).ringOperators.globalOneIso.hom).symm)

theorem twoHomologyMap_eq : twoHomologyMap p =
    ShortComplex.homologyMap (twoComplexMap p) ≫ (totalData p).twoHomologyIso.hom :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : (Row.twoComplex p).homology ⟶
        (totalData p).complexData.twoComplex.homology =>
      f ≫ (totalData p).twoHomologyIso.hom)
      (ShortComplex.homologyMap_comp (toTotal p).globalTwoMap
        (totalOperators p).ringOperators.globalTwoIso.hom).symm)

/-- The original top coefficient in the literal kernel of the actual last differential. -/
def twoKernelSection (s : Dolbeault.SmoothSection p ⊤) : (Row.twoComplex p).g.hom.ker :=
  ⟨s, congrArg
    (fun f : (Row.twoComplex p).X₂ ⟶ (Row.twoComplex p).X₃ => f.hom s)
    (Row.twoComplex_g_zero p)⟩

/-- The canonical zero-kernel cycle is the same original kernel representative. -/
theorem twoCycle_eq_ab (s : Dolbeault.SmoothSection p ⊤) :
    Row.twoCycle p s = (Row.twoComplex p).abCyclesIso.inv (twoKernelSection p s) := by
  apply AddCommGrpCat.injective_of_mono (Row.twoComplex p).iCycles
  exact (Row.twoCycle_i p s).trans
    ((Row.twoComplex p).abCyclesIso_inv_apply_iCycles (twoKernelSection p s)).symm

/-- The genuine first homology map preserves the original closed-pair class. -/
theorem oneHomologyMap_class (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    oneHomologyMap p (Row.oneClass p s hs) = (lastAlgebra p).oneClass s hs := by
  have hx := LastAlgebra.abHomologyMap_class (oneComplexMap p) ⟨s, hs⟩
  have hc : TotalMaps.abCycleMap (oneComplexMap p) ⟨s, hs⟩ =
      (lastAlgebra p).oneCocycle s hs :=
    Subtype.ext (oneComplexMap_apply p s)
  have hq := congrArg (totalData p).classOne hc
  exact (congrArg (fun f : (Row.oneComplex p).homology ⟶
      AddCommGrpCat.of (totalData p).CohomologyOne =>
    f.hom (Row.oneClass p s hs)) (oneHomologyMap_eq p)).trans (hx.trans hq)

/-- The genuine second homology map preserves the original positive top class. -/
theorem twoHomologyMap_class (s : Dolbeault.SmoothSection p ⊤) :
    twoHomologyMap p (Row.twoClass p s) = (lastAlgebra p).twoClass s := by
  have hx := LastAlgebra.abHomologyMap_class (twoComplexMap p) (twoKernelSection p s)
  have hc : TotalMaps.abCycleMap (twoComplexMap p) (twoKernelSection p s) =
      (lastAlgebra p).twoCocycle s :=
    Subtype.ext (twoComplexMap_apply p s)
  have hr : Row.twoClass p s = (Row.twoComplex p).homologyπ
      ((Row.twoComplex p).abCyclesIso.inv (twoKernelSection p s)) :=
    congrArg (fun x : (Row.twoComplex p).cycles => (Row.twoComplex p).homologyπ x)
      (twoCycle_eq_ab p s)
  have hq := congrArg (totalData p).classTwo hc
  exact (congrArg (fun x : (Row.twoComplex p).homology => twoHomologyMap p x) hr).trans
    ((congrArg (fun f : (Row.twoComplex p).homology ⟶
        AddCommGrpCat.of (totalData p).CohomologyTwo =>
      f.hom ((Row.twoComplex p).homologyπ
        ((Row.twoComplex p).abCyclesIso.inv (twoKernelSection p s))))
      (twoHomologyMap_eq p)).trans (hx.trans hq))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps
