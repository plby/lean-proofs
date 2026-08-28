import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingLoops
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupMarking
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticRetractionFundamentalGroupAt

/-!
# The actual elliptic attaching meridian in the small-piece fundamental group

The small piece retracts onto its genuine central surface at every
basepoint.  At the displayed logarithmic basepoint, the retraction's
basepoint is exactly the affine-cover image of the displayed real lift.
The resulting isomorphism sends the actual clockwise attaching loop to
the inverse affine generator; no basepoint path or marking is assumed.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticFilling CuspUniformization

/-- The exact real lift of the logarithmic attaching basepoint. -/
abbrev attachingFlatBase (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) : RealCoordinates :=
  logMeridianFlat (specialLocalData j) j.twist s₀ hs₀ 0

/-- Actual retraction identifies the basepoint without introducing a tail. -/
theorem pieceSurfaceRetraction_attachingBasepoint (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    pieceSurfaceRetraction j (attachingBasepoint j s₀ hs₀ hr) =
      affineCoverProjection j (specialLocalData j).centralPeriod j.twist
        (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀) :=
  fillingSurfaceRetraction_quotient_flat (specialLocalData j) j.twist
    (mainTwist_admissible j) (logMeridianRoot j s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀)

/-- The actual small-piece group isomorphism, with only an equality cast
between its retracted basepoint and the displayed affine-cover point. -/
def attachingDeckEquiv (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    FundamentalGroup (LocalSpace j) (attachingBasepoint j s₀ hs₀ hr) ≃*
      AffineDeckGroup j j.twist :=
  (pieceSurfaceRetractionFundamentalGroupEquiv j (attachingBasepoint j s₀ hs₀ hr)).trans
    ((MulEquiv.cast (M := FundamentalGroup (SpecialCentralSurface j))
      (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)).trans
        (surfaceFundamentalGroupDeckEquiv j (specialLocalData j).centralPeriod j.twist
          (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)))

/-- The literal retraction of the small-piece attaching loop. -/
def attachingRetractionLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path (affineCoverProjection j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀))
      (affineCoverProjection j (specialLocalData j).centralPeriod j.twist
        (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)) :=
  ((attachingLoop j s₀ hs₀ hr).map (pieceSurfaceRetraction j).continuous).cast
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm
    (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr).symm

/-- Restriction to the small piece leaves the retracted path unchanged. -/
theorem attachingRetractionLoop_eq (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    attachingRetractionLoop j s₀ hs₀ hr =
      logMeridianSurfaceLoop (specialLocalData j) j.twist (mainTwist_admissible j) s₀ hs₀ := by
  ext t
  rfl

/-- The actual inclusion/retraction marking has the clockwise inverse sign. -/
theorem attachingDeckEquiv_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    attachingDeckEquiv j s₀ hs₀ hr (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧) =
      (deckGenerator j j.twist)⁻¹ := by
  change surfaceFundamentalGroupDeckEquiv j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
      (MulEquiv.cast (M := FundamentalGroup (SpecialCentralSurface j))
        (pieceSurfaceRetraction_attachingBasepoint j s₀ hs₀ hr)
        (FundamentalGroup.fromPath
          ⟦(attachingLoop j s₀ hs₀ hr).map (pieceSurfaceRetraction j).continuous⟧)) = _
  rw [fundamentalGroup_cast_loop]
  change surfaceFundamentalGroupDeckEquiv j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j) (attachingFlatBase j s₀ hs₀)
      (FundamentalGroup.fromPath ⟦attachingRetractionLoop j s₀ hs₀ hr⟧) = _
  rw [attachingRetractionLoop_eq]
  exact surfaceFundamentalGroupDeckEquiv_logMeridian (specialLocalData j) j.twist
    (mainTwist_admissible j) s₀ hs₀

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
