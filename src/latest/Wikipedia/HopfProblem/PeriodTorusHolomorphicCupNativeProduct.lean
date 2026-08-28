import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMaps
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMaps
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupBasic

/-!
# The native cup is the actual Dolbeault coefficient wedge

The first-column comparison preserves the existing native Godement
cup. The last-row comparison preserves the original marked Dolbeault
classes. Their genuine total-cochain product therefore identifies the
native cup with the literal coefficient wedge, with positive sign.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

/-- Actual native Dolbeault representatives multiply in their original coordinate order. -/
theorem cup_nativeH1Class (p : PeriodDomain) (s t : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) (ht : Dolbeault.topSection p ⊤ t = 0) :
    cup p (nativeH1Class p s hs) (nativeH1Class p t ht) =
      nativeH2Class p (s.1 * t.2 - s.2 * t.1) := by
  apply (totalNativeTwoEquiv p).injective
  calc
    totalNativeTwoEquiv p (cup p (nativeH1Class p s hs) (nativeH1Class p t ht)) =
        (totalData p).cup (totalNativeOneEquiv p (nativeH1Class p s hs))
          (totalNativeOneEquiv p (nativeH1Class p t ht)) :=
      FirstMaps.native_cup p (nativeH1Class p s hs) (nativeH1Class p t ht)
    _ = (totalData p).cup ((LastMaps.lastAlgebra p).oneClass s hs)
        ((LastMaps.lastAlgebra p).oneClass t ht) :=
      congrArg₂ (fun a b => (totalData p).cup a b)
        (LastMaps.nativeOne_nativeH1Class p s hs) (LastMaps.nativeOne_nativeH1Class p t ht)
    _ = (LastMaps.lastAlgebra p).twoClass (s.1 * t.2 - s.2 * t.1) :=
      (LastMaps.lastAlgebra p).cup_oneClass s t hs ht
    _ = totalNativeTwoEquiv p (nativeH2Class p (s.1 * t.2 - s.2 * t.1)) :=
      (LastMaps.nativeTwo_nativeH2Class p (s.1 * t.2 - s.2 * t.1)).symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
