/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaAcceptedCreation
import ErdosProblems.Erdos1165.TilingPrefixedConditionalCappedMarginalization

set_option linter.style.haveILetI false

/-!
# Path mass of the honest accepted oriented Theta screen

On a fixed oriented external-word atom the accepted Theta predicate has an
exact finite-product factorization.  This file keeps the common external
cylinder mass visible: the screened stopped mass is bounded by the literal
two-scale Theta cost times that carrier mass.  Consequently later countable
summation weights every atom by its actual retained-word mass rather than
summing bare per-atom costs.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaAcceptedCreationMass

open FiniteDominoProductLaw HLOZSourceOrientedThetaAcceptedCreation
open HLOZSourceOrientedThetaExternalProduct LazyDecomposition
open PathInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

private abbrev Fiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) := allRepresentedFiber eta

private abbrev Indexed
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) := toSupportedIndex eta

private abbrev Code
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) := (Indexed eta).1.1

private abbrev Distinguished
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :=
  supportComplementDistinguished t (Code eta).start (Code eta).retained
    (Indexed eta).1.2

private theorem sum_distinguishedAwayMass_nonneg
    {Domino Delta : Type*} [Fintype Domino] [DecidableEq Domino]
    [Fintype Delta] (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (distinguishedMass : Delta → ℝ)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hdistinguished : ∀ d, 0 ≤ distinguishedMass d) :
    0 ≤ ∑ ell : TruncatedTotals upper,
      distinguishedAwayMass pointMass upper distinguishedMass ell := by
  unfold distinguishedAwayMass
  exact Finset.sum_nonneg fun ell _ ↦ Finset.sum_nonneg fun d _ ↦
    mul_nonneg (Finset.prod_nonneg fun b _ ↦ hpoint b (ell b))
      (hdistinguished d)

/-- The common retained-word carrier left after marginalizing all represented
domino totals.  It is independent of the Theta screen. -/
noncomputable def acceptedThetaCarrierGeometricMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (cap : ℕ) : ℝ := by
  letI : Fintype (TilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  letI : Fintype (TilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  exact ∑ ell : TruncatedTotals ((Fiber eta).upper cap),
    distinguishedAwayMass
      (tilingAwayPointMass (cap := (Fiber eta).coordinateCap cap) t
        (Code eta).start (Code eta).retained (Distinguished eta))
      ((Fiber eta).upper cap)
      (fun d ↦ if (Fiber eta).selected cap d then
        ∏ b, ∏ j, geometricGapMass (d b j : ℕ)
        else 0) ell

theorem acceptedThetaCarrierGeometricMass_nonneg
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (cap : ℕ) :
    0 ≤ acceptedThetaCarrierGeometricMass eta cap := by
  letI : Fintype (TilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  letI : Fintype (TilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  unfold acceptedThetaCarrierGeometricMass
  apply sum_distinguishedAwayMass_nonneg
  · intro b v
    exact tilingAwayExactTotalMass_nonneg t (Code eta).start
      (Code eta).retained (Distinguished eta) b v
  · intro d
    by_cases hselected : (Fiber eta).selected cap d
    · rw [if_pos hselected]
      exact Finset.prod_nonneg fun b _ ↦
        Finset.prod_nonneg fun j _ ↦ geometricGapMass_nonneg _
    · rw [if_neg hselected]

/-- Exact finite-cap factorization of the screened stopped geometric mass. -/
theorem acceptedThetaStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (w externalLow externalHigh cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass
        ((Fiber eta).stoppingTime cap) (Code eta).initial.1 t (Code eta).start
        (Code eta).retained ((Fiber eta).coordinateCap cap) (Code eta).tail.1
        (acceptedThetaPredicate eta w externalLow externalHigh cap) =
      acceptedThetaScreenMass eta w externalLow externalHigh cap *
      acceptedThetaCarrierGeometricMass eta cap := by
  classical
  letI : Fintype (TilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingAwayDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  letI : Fintype (TilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)) :=
    instFintypeTilingDistinguishedDomino t (Code eta).start
      (Code eta).retained (Distinguished eta)
  have h := @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    ((Fiber eta).stoppingTime cap) (Code eta).initial.1
    (Code eta).retainedCount ((Fiber eta).coordinateCap cap) t
    (Code eta).start (Code eta).retained (Code eta).tail.1
    (acceptedThetaPredicate eta w externalLow externalHigh cap)
    (Classical.decPred _)
    (Distinguished eta) ((Fiber eta).selected cap) (Classical.decPred _)
    ((Fiber eta).upper cap)
    (acceptedThetaAtTotals eta w externalLow externalHigh cap)
    (Classical.decPred _)
    (acceptedThetaPredicate_factorization eta w externalLow externalHigh cap)
    (by
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro ell _hell
        exact Finset.prod_nonneg fun b _ ↦
          tilingAwayExactTotalMass_nonneg t (Code eta).start
            (Code eta).retained (Distinguished eta) b (ell b)
      · let zero : TruncatedTotals ((Fiber eta).upper cap) :=
          fun b ↦ ⟨0, (Fiber eta).upper_pos cap b⟩
        refine ⟨zero, Finset.mem_univ _, ?_⟩
        unfold jointMass
        apply Finset.prod_pos
        intro b _hb
        exact tilingAwayExactTotalMass_zero_pos t (Code eta).start
          (Code eta).retained (Distinguished eta) b)
  simpa only [acceptedThetaScreenMass, acceptedThetaCarrierGeometricMass,
    tilingDistinguishedAssignmentMass, Fiber, Code, Indexed,
    Distinguished] using h

/-- Literal source-scale bound on the stopped mass of one capped external
atom. -/
theorem acceptedThetaStoppedGeometricMass_le_of_scale
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (cap : ℕ)
    (scale : HLOZSourceOrientedThetaProduct.OrientedThetaScaleArithmetic m) :
    prefixedTilingStoppedAcceptedGeometricMass
        ((Fiber eta).stoppingTime cap) (Code eta).initial.1 t (Code eta).start
        (Code eta).retained ((Fiber eta).coordinateCap cap) (Code eta).tail.1
        (acceptedThetaPredicate eta
          (HLOZProposition48Candidates.shellWidth48 m)
          (HLOZShellZeroExternalWindow.shellZeroExternalLow48 m)
          (HLOZShellZeroExternalWindow.shellZeroExternalHigh48 m) cap) ≤
      (2 * (((externalThetaHighCoordinates (Fiber eta) cap).card : ℝ) *
          Real.exp (-17 * ScreeningInstantiation.balanceRateScale m) +
        ((tilingExternalDominoBases t eta.1.start eta.1.retained).card : ℝ) *
          Real.exp (-17 *
            HLOZSourceOrientedThetaBalance.thetaLowRateScale m))) *
        acceptedThetaCarrierGeometricMass eta cap := by
  rw [acceptedThetaStoppedGeometricMass_eq]
  exact mul_le_mul_of_nonneg_right
    (acceptedThetaScreenMass_le_of_scale eta cap scale)
    (acceptedThetaCarrierGeometricMass_nonneg eta cap)

end

end Erdos1165.HLOZSourceOrientedThetaAcceptedCreationMass
