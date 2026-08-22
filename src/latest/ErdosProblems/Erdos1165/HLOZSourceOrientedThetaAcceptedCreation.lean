/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalProduct
import ErdosProblems.Erdos1165.TilingOrientedAllRepresentedExternalFiber

/-!
# Honest accepted-creation screen for the absolute oriented Theta product

Stopping acceptance is not independent of the away coordinates.  In
particular, replacing it by `True` after projecting the distinguished
coordinates is false.  The acceptor below records exactly the needed
invariance: every selected distinguished assignment and every away
assignment with the displayed domino totals must reconstruct the same
accepted external creation atom.  Intersecting this honest acceptor with the
absolute Theta union has an exact stopped-fibre factorization, while its
finite-product mass is bounded by the unconditional Theta screen.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaAcceptedCreation

open FiniteDominoProductLaw HLOZSourceOrientedThetaExternalProduct
open HLOZFiniteProductCoordinateUnion
open LazyDecomposition TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

private abbrev Fiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) := allRepresentedFiber eta

private theorem screenMass_mono_explicit
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    (baseDec : DecidablePred base) (screenedDec : DecidablePred screened)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, screened ell → base ell) :
    @screenMass Domino _ _ pointMass upper screened screenedDec ≤
      @screenMass Domino _ _ pointMass upper base baseDec := by
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hscreened : screened ell
  · rw [if_pos hscreened, if_pos (hsub ell hscreened)]
  · rw [if_neg hscreened]
    by_cases hbase : base ell
    · rw [if_pos hbase]
      exact normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg hbase]

/-- Accepted-creation is stable throughout one away-total class.  The
quantifiers over `d` and `a` are intentional: the screen is a function only
of the total vector, as required by finite-product marginalization. -/
def acceptedCreationAtTotals
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (cap : ℕ)
    (ell : TruncatedTotals ((Fiber eta).upper cap)) : Prop :=
  ∀ q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap),
    (Fiber eta).selected cap
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).1) →
    (∀ b, tilingAwayTotal t eta.1.start eta.1.retained
      (supportComplementDistinguished t eta.1.start eta.1.retained
        (tilingExternalDominoBases t eta.1.start eta.1.retained))
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).2) b =
        ell b) →
    (Fiber eta).atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted ((Fiber eta).stoppingTime cap)
        eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1

/-- Honest accepted creation intersected with the absolute coordinate Theta
union. -/
def acceptedThetaAtTotals
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals ((Fiber eta).upper cap)) : Prop :=
  acceptedCreationAtTotals eta cap ell ∧
    externalThetaAccepts (Fiber eta) w externalLow externalHigh cap ell = true

/-- Coordinate predicate on one capped stopped fibre. -/
def acceptedThetaPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap)) : Prop :=
  (Fiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t eta.1.start eta.1.retained
      (supportComplementDistinguished t eta.1.start eta.1.retained
        (tilingExternalDominoBases t eta.1.start eta.1.retained))
      ((Fiber eta).upper cap)
      (acceptedThetaAtTotals eta w externalLow externalHigh cap)
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).2)

/-- Exact stopped-fibre factorization of the honest accepted Theta screen. -/
theorem acceptedThetaPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap)) :
    acceptedThetaPredicate eta w externalLow externalHigh cap q ∧
        PrefixedTilingStoppingAccepted ((Fiber eta).stoppingTime cap)
          eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.tail.1 ↔
      (Fiber eta).selected cap
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
            (supportComplementDistinguished t eta.1.start eta.1.retained
              (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).1) ∧
        TilingAwayTotalsScreen t eta.1.start eta.1.retained
          (supportComplementDistinguished t eta.1.start eta.1.retained
            (tilingExternalDominoBases t eta.1.start eta.1.retained))
          ((Fiber eta).upper cap)
          (acceptedThetaAtTotals eta w externalLow externalHigh cap)
          ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
            (supportComplementDistinguished t eta.1.start eta.1.retained
              (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).2) := by
  constructor
  · rintro ⟨⟨hatom, hscreen⟩, haccepted⟩
    refine ⟨?_, hscreen⟩
    let e : TilingCappedCoordinates eta.1.retainedCount
        ((Fiber eta).coordinateCap cap) ≃
        TilingDistinguishedCoordinates
            (cap := (Fiber eta).coordinateCap cap) t eta.1.start eta.1.retained
              (supportComplementDistinguished t eta.1.start eta.1.retained
                (tilingExternalDominoBases t eta.1.start eta.1.retained)) ×
          TilingAwayCoordinates
            (cap := (Fiber eta).coordinateCap cap) t eta.1.start eta.1.retained
              (supportComplementDistinguished t eta.1.start eta.1.retained
                (tilingExternalDominoBases t eta.1.start eta.1.retained)) :=
      splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained))
    change (Fiber eta).selected cap (e q).1
    refine ⟨(e q).2, ?_⟩
    dsimp only
    have hq : e.symm ((e q).1, (e q).2) = q := by
      rw [Prod.eta, Equiv.symm_apply_apply]
    change (Fiber eta).atomPredicate cap
        (e.symm ((e q).1, (e q).2)) ∧
      PrefixedTilingStoppingAccepted ((Fiber eta).stoppingTime cap)
        eta.1.initial.1 t eta.1.start eta.1.retained
          (fun j ↦ ((e.symm ((e q).1, (e q).2)) j : ℕ)) eta.1.tail.1
    rw [hq]
    exact ⟨hatom, haccepted⟩
  · rintro ⟨hselected, hscreen⟩
    rcases hscreen with ⟨ell, hell, htotal⟩
    have hrecover := hell.1 q hselected htotal
    refine ⟨⟨hrecover.1, ?_⟩, hrecover.2⟩
    exact ⟨ell, hell, htotal⟩

/-- Normalized finite-product mass of the honest accepted Theta screen. -/
noncomputable def acceptedThetaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ) : ℝ := by
  classical
  let indexed := toSupportedIndex eta
  exact @screenMass
      (TilingAwayDomino t indexed.1.1.start indexed.1.1.retained
        (supportComplementDistinguished t indexed.1.1.start
          indexed.1.1.retained indexed.1.2))
      (instFintypeTilingAwayDomino t indexed.1.1.start indexed.1.1.retained
        (supportComplementDistinguished t indexed.1.1.start
          indexed.1.1.retained indexed.1.2))
      (fun a b ↦ Subtype.instDecidableEq a b)
      (tilingAwayPointMass (cap := (Fiber eta).coordinateCap cap) t
        indexed.1.1.start indexed.1.1.retained
        (supportComplementDistinguished t indexed.1.1.start
          indexed.1.1.retained indexed.1.2))
      ((Fiber eta).upper cap)
      (acceptedThetaAtTotals eta w externalLow externalHigh cap)
      (Classical.decPred _)

/-- Dropping accepted-creation can only enlarge the absolute Theta screen. -/
theorem acceptedThetaScreenMass_le_externalThetaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ) :
    acceptedThetaScreenMass eta w externalLow externalHigh cap ≤
      externalThetaScreenMass (Fiber eta) w externalLow externalHigh cap := by
  classical
  unfold acceptedThetaScreenMass externalThetaScreenMass
  dsimp only
  refine @screenMass_mono_explicit
    (TilingAwayDomino t (toSupportedIndex eta).1.1.start
      (toSupportedIndex eta).1.1.retained
      (supportComplementDistinguished t (toSupportedIndex eta).1.1.start
        (toSupportedIndex eta).1.1.retained (toSupportedIndex eta).1.2))
    (instFintypeTilingAwayDomino t (toSupportedIndex eta).1.1.start
      (toSupportedIndex eta).1.1.retained
      (supportComplementDistinguished t (toSupportedIndex eta).1.1.start
        (toSupportedIndex eta).1.1.retained (toSupportedIndex eta).1.2))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := (Fiber eta).coordinateCap cap) t
      (toSupportedIndex eta).1.1.start (toSupportedIndex eta).1.1.retained
      (supportComplementDistinguished t (toSupportedIndex eta).1.1.start
        (toSupportedIndex eta).1.1.retained (toSupportedIndex eta).1.2))
    ((Fiber eta).upper cap)
    (fun ell ↦ externalThetaAccepts (Fiber eta) w externalLow
      externalHigh cap ell = true)
    (acceptedThetaAtTotals eta w externalLow externalHigh cap)
    (fun ell ↦ instDecidableEqBool
      (externalThetaAccepts (Fiber eta) w externalLow externalHigh cap ell) true)
    (Classical.decPred
      (acceptedThetaAtTotals eta w externalLow externalHigh cap)) ?_ ?_
  · intro b v
    exact tilingAwayExactTotalMass_nonneg _ _ _ _ b v
  · intro ell hell
    exact hell.2

/-- Source-scale bound for the honest accepted screen on one external atom. -/
theorem acceptedThetaScreenMass_le_of_scale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (cap : ℕ)
    (scale : HLOZSourceOrientedThetaProduct.OrientedThetaScaleArithmetic m) :
    acceptedThetaScreenMass eta
        (HLOZProposition48Candidates.shellWidth48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
        (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m) cap ≤
      2 * (((externalThetaHighCoordinates (Fiber eta) cap).card : ℝ) *
          Real.exp (-17 * ScreeningInstantiation.balanceRateScale m) +
        ((tilingExternalDominoBases t eta.1.start eta.1.retained).card : ℝ) *
          Real.exp (-17 * HLOZSourceOrientedThetaBalance.thetaLowRateScale m)) := by
  exact (acceptedThetaScreenMass_le_externalThetaScreenMass eta _ _ _ cap).trans
    (externalConcreteFiber_theta_le_of_scale
      (allRepresentedSupportData t o m k) (toSupportedIndex eta) cap scale)

end

end Erdos1165.HLOZSourceOrientedThetaAcceptedCreation
