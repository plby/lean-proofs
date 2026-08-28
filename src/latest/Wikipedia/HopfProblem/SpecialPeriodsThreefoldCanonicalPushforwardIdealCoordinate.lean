import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealFrames
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspCoordinates

/-!
# The genuine vanishing ideal in the fixed reciprocal sphere coordinate

Division of an actual ideal section by the reciprocal coordinate is
holomorphic even at infinity. This is the inverse of the previously
proved ideal-sheaf frame isomorphism, with its pointwise value identified
with the unchanged reciprocal coordinate used in the actual cusp patch.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.IdealCoordinate

open HolomorphicFunctionSheaf.SphereH1
open CanonicalGlobal.BaseTwist

/-- The actual ideal frame and the actual cusp reciprocal coordinate
are the same on their original infinity-chart domain. -/
theorem idealFrameValue_eq_reciprocal {p : RiemannSphere}
    (hp : p ∈ NegativeOneFrames.infinityChart) :
    idealFrameValue true p = GlobalCusp.reciprocalCoordinate p := by
  induction p using OnePoint.rec with
  | infty => exact GlobalCusp.reciprocalCoordinate_infty.symm
  | coe z =>
    exact (GlobalCusp.reciprocalCoordinate_coe
      ((NegativeOneFrames.coe_mem_infinityChart_iff z).mp hp)).symm

/-- The actual holomorphic quotient by the vanishing ideal frame. -/
def divide (U : Opens RiemannSphere) (hU : U ≤ NegativeOneFrames.infinityChart)
    (f : NegativeOneSection U) : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
  (NegativeOneFrames.chartTrivialization true U hU).symm f

/-- This multiplication identity holds at every point of the original
open set, including infinity. -/
theorem divide_mul_reciprocal (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.infinityChart) (f : NegativeOneSection U) (p : U) :
    divide U hU f p * GlobalCusp.reciprocalCoordinate p.val = f.val p := by
  calc
    divide U hU f p * GlobalCusp.reciprocalCoordinate p.val =
        divide U hU f p * idealFrameValue true p :=
      congrArg (fun c : ℂ => divide U hU f p * c)
        (idealFrameValue_eq_reciprocal (hU p.property)).symm
    _ = (NegativeOneFrames.chartTrivialization true U hU
        ((NegativeOneFrames.chartTrivialization true U hU).symm f)).val p :=
      (chartTrivialization_value true U hU _ p).symm
    _ = f.val p := congrArg (fun q : NegativeOneSection U => q.val p)
      ((NegativeOneFrames.chartTrivialization true U hU).apply_symm_apply f)

/-- Away from infinity this is literal division by the fixed coordinate,
not a freely chosen extension coefficient. -/
theorem divide_eq_div (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.infinityChart) (f : NegativeOneSection U) (p : U)
    (hp : GlobalCusp.reciprocalCoordinate p.val ≠ 0) :
    divide U hU f p = f.val p / GlobalCusp.reciprocalCoordinate p.val :=
  (eq_div_iff hp).mpr (divide_mul_reciprocal U hU f p)

/-- Actual division commutes with literal restriction to every smaller
infinity-chart open set. -/
theorem divide_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.infinityChart) (f : NegativeOneSection V) :
    divide U (h.trans hV) (negativeOneRestriction h f) =
      ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h (divide V hV f) := by
  apply (NegativeOneFrames.chartTrivialization true U (h.trans hV)).injective
  change NegativeOneFrames.chartTrivialization true U (h.trans hV)
      ((NegativeOneFrames.chartTrivialization true U (h.trans hV)).symm
        (negativeOneRestriction h f)) = _
  rw [LinearEquiv.apply_symm_apply, ← NegativeOneFrames.chartTrivialization_restrict]
  change negativeOneRestriction h f = negativeOneRestriction h
    (NegativeOneFrames.chartTrivialization true V hV
      ((NegativeOneFrames.chartTrivialization true V hV).symm f))
  rw [LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.IdealCoordinate
