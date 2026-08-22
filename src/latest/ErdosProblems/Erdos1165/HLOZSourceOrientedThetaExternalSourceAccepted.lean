/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalAccepted
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceWindowProduct

set_option linter.style.haveILetI false

/-!
# Accepted rank-stable source-window Theta screens

The physical restricted Theta screen is the union of a below-level source
window and an above-level replacement window.  Only the first is stable at
the original creation rank.  This file gives that source window its own
honest accepted-creation product and keeps the distinguished carrier in the
mass identity.  The source screen is then dominated by the already checked
union-window product, without identifying the two events.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaExternalSourceAccepted

open FiniteDominoProductLaw HLOZFiniteProductCoordinateUnion
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceWindowProduct
open LazyDecomposition TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The unconditional Boolean union of below-level source-window failures. -/
def externalSourceThetaAccepts
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Bool :=
  decide (∃ b, sourceThetaCoordinateBad m w externalLow externalHigh
    (Fintype.card (TilingCoordinatesAt t z.start z.retained b.1)) (ell b))

def externalAcceptedSourceThetaAtTotals
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Prop :=
  externalAcceptedCreationAtTotals data cap ell ∧
    externalSourceThetaAccepts data w externalLow externalHigh cap ell = true

def externalAcceptedSourceThetaPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  data.atomPredicate cap q ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap)
      (externalAcceptedSourceThetaAtTotals data w externalLow externalHigh cap)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

theorem externalSourceThetaAccepts_imp_externalThetaAccepts
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap))
    (h : externalSourceThetaAccepts data w externalLow externalHigh cap ell =
      true) :
    externalThetaAccepts data w externalLow externalHigh cap ell = true := by
  rw [externalSourceThetaAccepts, decide_eq_true_eq] at h
  rw [externalThetaAccepts, decide_eq_true_eq]
  rcases h with ⟨b, hb⟩
  exact ⟨b, sourceThetaCoordinateBad_subset_thetaCoordinateBad hb⟩

/-- Exact product factorization.  The reverse direction invokes the complete
accepted-creation base screen, rather than an unconditional denominator. -/
theorem externalAcceptedSourceThetaPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (hforward : ∀ q : TilingCappedCoordinates z.retainedCount
        (data.coordinateCap cap),
      data.atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 →
        data.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1))
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    externalAcceptedSourceThetaPredicate data w externalLow externalHigh cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
          z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      data.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) ∧
        TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap)
          (externalAcceptedSourceThetaAtTotals data w externalLow externalHigh cap)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) := by
  constructor
  · rintro ⟨⟨hatom, hscreen⟩, haccepted⟩
    exact ⟨hforward q ⟨hatom, haccepted⟩, hscreen⟩
  · rintro ⟨hselected, hscreen⟩
    rcases hscreen with ⟨ell, hell, htotal⟩
    have hrecover := hell.1 q hselected htotal
    exact ⟨⟨hrecover.1, ⟨ell, hell, htotal⟩⟩, hrecover.2⟩

noncomputable def externalAcceptedSourceThetaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) : ℝ :=
  @screenMass
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (externalAcceptedSourceThetaAtTotals data w externalLow externalHigh cap)
    (Classical.decPred _)

private theorem screenMass_mono
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (large small : TruncatedTotals upper → Prop)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, small ell → large ell) :
    @screenMass Domino _ _ pointMass upper small (Classical.decPred _) ≤
      @screenMass Domino _ _ pointMass upper large (Classical.decPred _) := by
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : small ell
  · rw [if_pos hs, if_pos (hsub ell hs)]
  · rw [if_neg hs]
    by_cases hl : large ell
    · rw [if_pos hl]
      exact normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg hl]

theorem externalAcceptedSourceThetaScreenMass_le_externalThetaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) :
    externalAcceptedSourceThetaScreenMass data w externalLow externalHigh cap ≤
      externalThetaScreenMass data w externalLow externalHigh cap := by
  classical
  unfold externalAcceptedSourceThetaScreenMass externalThetaScreenMass
  have h := @screenMass_mono
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (fun ell ↦ externalThetaAccepts data w externalLow externalHigh cap ell =
      true)
    (externalAcceptedSourceThetaAtTotals data w externalLow externalHigh cap)
    (externalTheta_pointMass_nonneg data cap)
    (fun ell hell ↦
      externalSourceThetaAccepts_imp_externalThetaAccepts data w
        externalLow externalHigh cap ell hell.2)
  convert h using 1
  apply congrArg
  exact Subsingleton.elim _ _

/-- Exact distinguished-carrier identity on one capped external atom. -/
theorem externalAcceptedSourceThetaStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (hforward : ∀ q : TilingCappedCoordinates z.retainedCount
        (data.coordinateCap cap),
      data.atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 →
        data.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1)) :
    prefixedTilingStoppedAcceptedGeometricMass
        (data.stoppingTime cap) z.initial.1 t z.start z.retained
        (data.coordinateCap cap) z.tail.1
        (externalAcceptedSourceThetaPredicate data w externalLow externalHigh cap) =
      externalAcceptedSourceThetaScreenMass data w externalLow externalHigh cap *
        externalAcceptedThetaCarrier data cap := by
  classical
  letI : Fintype (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  letI : Fintype (TilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  have h := @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (data.stoppingTime cap) z.initial.1 z.retainedCount (data.coordinateCap cap)
    t z.start z.retained z.tail.1
    (externalAcceptedSourceThetaPredicate data w externalLow externalHigh cap)
    (Classical.decPred _)
    (supportComplementDistinguished t z.start z.retained S)
    (data.selected cap) (Classical.decPred _) (data.upper cap)
    (externalAcceptedSourceThetaAtTotals data w externalLow externalHigh cap)
    (Classical.decPred _)
    (externalAcceptedSourceThetaPredicate_factorization data w externalLow
      externalHigh cap hforward)
    (by
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro ell _hell
        exact Finset.prod_nonneg fun b _ ↦
          tilingAwayExactTotalMass_nonneg t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) b (ell b)
      · let zero : TruncatedTotals (data.upper cap) :=
          fun b ↦ ⟨0, data.upper_pos cap b⟩
        refine ⟨zero, Finset.mem_univ _, ?_⟩
        unfold jointMass
        apply Finset.prod_pos
        intro b _hb
        exact tilingAwayExactTotalMass_zero_pos t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S) b)
  simpa only [externalAcceptedSourceThetaScreenMass,
    externalAcceptedThetaCarrier, tilingDistinguishedAssignmentMass] using h

/-- Carrier-weighted atomwise estimate for the source part of restricted
Theta.  The larger union-window cost is used only by measure monotonicity. -/
theorem externalAcceptedSourceThetaStoppedGeometricMass_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (hforward : ∀ q : TilingCappedCoordinates z.retainedCount
        (data.coordinateCap cap),
      data.atomPredicate cap q ∧
          PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 →
        data.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1))
    (arith : ExternalThetaProductArithmetic data w externalLow externalHigh cap) :
    prefixedTilingStoppedAcceptedGeometricMass
        (data.stoppingTime cap) z.initial.1 t z.start z.retained
        (data.coordinateCap cap) z.tail.1
        (externalAcceptedSourceThetaPredicate data w externalLow externalHigh cap) ≤
      (2 * ∑ b, externalThetaCost data cap b) *
        externalAcceptedThetaCarrier data cap := by
  rw [externalAcceptedSourceThetaStoppedGeometricMass_eq data w externalLow
    externalHigh cap hforward]
  exact mul_le_mul_of_nonneg_right
    ((externalAcceptedSourceThetaScreenMass_le_externalThetaScreenMass
      data w externalLow externalHigh cap).trans
      (externalThetaScreenMass_le data w externalLow externalHigh cap arith))
    (externalAcceptedThetaCarrier_nonneg data cap)

end

end Erdos1165.HLOZSourceOrientedThetaExternalSourceAccepted
