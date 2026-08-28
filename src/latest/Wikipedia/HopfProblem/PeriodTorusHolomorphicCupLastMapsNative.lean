import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMapsNativeBasic

/-!
# The original native Dolbeault classes in the actual total quotient

Both maps use the original native cohomology comparison and the original
Dolbeault markings. In degree two the original positive double-connecting
class maps to the positive literal last-row top coefficient.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

theorem nativeOne_apply (a : H p 1) :
    totalNativeOneEquiv p a = oneHomologyMap p ((Row.h1Iso p).hom a) :=
  congrArg (fun f : AddCommGrpCat.of (H p 1) ⟶
    AddCommGrpCat.of (totalData p).CohomologyOne => f.hom a) (h1Iso_hom_comp p).symm

theorem nativeTwo_apply (a : H p 2) :
    totalNativeTwoEquiv p a = twoHomologyMap p ((Row.h2Iso p).hom a) :=
  congrArg (fun f : AddCommGrpCat.of (H p 2) ⟶
    AddCommGrpCat.of (totalData p).CohomologyTwo => f.hom a) (h2Iso_hom_comp p).symm

/-- Every original native closed-pair class maps to its literal last-row total class. -/
theorem nativeOne_nativeH1Class (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    totalNativeOneEquiv p (nativeH1Class p s hs) = (lastAlgebra p).oneClass s hs :=
  (nativeOne_apply p (nativeH1Class p s hs)).trans
    ((congrArg (fun a : (Row.oneComplex p).homology => oneHomologyMap p a)
      (Row.h1Iso_nativeClass p s hs)).trans (oneHomologyMap_class p s hs))

/-- Every original native top class maps to its literal last-row class with positive sign. -/
theorem nativeTwo_nativeH2Class (s : Dolbeault.SmoothSection p ⊤) :
    totalNativeTwoEquiv p (nativeH2Class p s) = (lastAlgebra p).twoClass s :=
  (nativeTwo_apply p (nativeH2Class p s)).trans
    ((congrArg (fun a : (Row.twoComplex p).homology => twoHomologyMap p a)
      (Row.h2Iso_nativeClass p s)).trans (twoHomologyMap_class p s))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps
