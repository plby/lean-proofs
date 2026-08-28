import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingKernelGlobal
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingKernelLocal

/-!
# Čech connecting classes from literal native differential equations

The actual closed coefficient pair supplies its original kernel section.
Cancellation of the actual kernel inclusion converts the literal local
Dolbeault equations to the required kernel-valued lift equations. Thus
the original Čech class and its marked coordinates are computed directly
from the given native pair of smooth functions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open PeriodTorusHolomorphicCohomology

/-- The original local differential equation implies equality with the
restriction of the actual global kernel section. -/
theorem nativeKernelLift_toK (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) (V : Opens p.Torus)
    (t : Dolbeault.SmoothSection p V)
    (ht : (Dolbeault.differential p).hom.app (op V) t =
      res (Dolbeault.pairSheaf p) le_top s) :
    (Dolbeault.resolution p).toK.hom.app (op V) t =
      res (Dolbeault.resolution p).K le_top (nativeKernelLift p s hs) :=
  toK_section_eq_of_differential (Dolbeault.resolution p) (nativeKernelLift p s hs) V t
    (ht.trans (congrArg (res (Dolbeault.pairSheaf p) le_top)
      (nativeKernelSection_nativeKernelLift p s hs)).symm)

variable (p : PeriodDomain) {ι : Type} {U : ι → Opens p.Torus}
  (c : CechOneCocycle (holomorphicSheaf p) U)
  (hU : ∀ x : p.Torus, ∃ j : ι, x ∈ U j)
  (s : Dolbeault.PairSection p ⊤) (hs : Dolbeault.topSection p ⊤ s = 0)
  (t : ∀ j : ι, Dolbeault.SmoothSection p (U j))
  (hp : ∀ j : ι, (Dolbeault.differential p).hom.app (op (U j)) (t j) =
    res (Dolbeault.pairSheaf p) le_top s)
  (hdiff : ∀ j l : ι,
    res (Dolbeault.smoothSheaf p) inf_le_right (t l) -
        res (Dolbeault.smoothSheaf p) inf_le_left (t j) =
      (Dolbeault.inclusion p).hom.app (op (U j ⊓ U l)) (c.value j l))

include t hp hdiff in
/-- The original class is the native class of the actual closed pair,
using only the proved literal differential and overlap equations. -/
theorem classOf_eq_nativeH1Class_of_differential :
    classOf c hU = nativeH1Class p s hs := by
  have h := classOf_eq_nativeH1Class p c hU (nativeKernelLift p s hs) t
    (fun j => nativeKernelLift_toK p s hs (U j) (t j) (hp j)) hdiff
  simpa only [nativeKernelSection_nativeKernelLift] using h

include hs t hp hdiff in
/-- The marked coordinates of the original Čech class are the literal
native Haar means of the actual closed pair supplied in the differential equations. -/
theorem h1Equiv_classOf_of_differential :
    h1Equiv p (classOf c hU) = GlobalFourier.pairMean p s :=
  (h1Equiv_classOf p c hU (nativeKernelLift p s hs) t
    (fun j => nativeKernelLift_toK p s hs (U j) (t j) (hp j)) hdiff).trans
      (congrArg (GlobalFourier.pairMean p) (nativeKernelSection_nativeKernelLift p s hs))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
