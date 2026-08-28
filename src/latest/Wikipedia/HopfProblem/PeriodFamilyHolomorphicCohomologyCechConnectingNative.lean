import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingGlobal
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyNativeConnecting

/-!
# Original Čech lifts and native period-torus Dolbeault markings

Literal local smooth lifts of an actual global kernel section identify
the original holomorphic Čech class with the genuine native Dolbeault
connecting class. The existing comparison then computes its coordinates
as the marked Haar means of its original native coefficient functions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain) {ι : Type} {U : ι → Opens p.Torus}
  (c : CechOneCocycle (holomorphicSheaf p) U)
  (hU : ∀ x : p.Torus, ∃ j : ι, x ∈ U j)
  (k : GlobalKernelSections p) (t : ∀ j : ι, Dolbeault.SmoothSection p (U j))
  (hp : ∀ j : ι, (Dolbeault.resolution p).toK.hom.app (op (U j)) (t j) =
    res (Dolbeault.resolution p).K le_top k)
  (hdiff : ∀ j l : ι,
    res (Dolbeault.smoothSheaf p) inf_le_right (t l) -
        res (Dolbeault.smoothSheaf p) inf_le_left (t j) =
      (Dolbeault.inclusion p).hom.app (op (U j ⊓ U l)) (c.value j l))

include t hp hdiff

/-- The original holomorphic Čech class is the actual first native
Dolbeault connecting class, with the original positive sign. -/
theorem classOf_eq_nativeConnectingOne :
    classOf c hU = (Dolbeault.resolution p).globalConnectingOne k :=
  classOf_eq_globalConnectingOne (Dolbeault.resolution p) c hU k t hp hdiff

/-- The class is the original native representative, not a class
chosen through a dimension comparison. -/
theorem classOf_eq_nativeH1Class :
    classOf c hU = nativeH1Class p (nativeKernelSection p k) (nativeKernelSection_closed p k) :=
  (classOf_eq_nativeConnectingOne p c hU k t hp hdiff).trans
    (nativeH1Class_eq_globalConnectingOne p k).symm

/-- The original marked coordinates are the literal Haar means of
the actual globally included native coefficient functions. -/
theorem h1Equiv_classOf :
    h1Equiv p (classOf c hU) = GlobalFourier.pairMean p (nativeKernelSection p k) :=
  (congrArg (h1Equiv p) (classOf_eq_nativeConnectingOne p c hU k t hp hdiff)).trans
    (h1Equiv_globalConnectingOne p k)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
