/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalProduct
import ErdosProblems.Erdos1165.TilingPrefixedConditionalCappedMarginalization

set_option linter.style.haveILetI false

/-!
# Honest accepted Theta screens on an external support atom

This is the support-generic form of the accepted-creation construction.  It
is particularly used when the support is the singleton selected by one
retained-word Theta slot.  The base acceptor records the complete creation
condition; the exceptional screen is then bounded by the unconditional
one-coordinate Theta mass, while the distinguished carrier remains visible.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaExternalAccepted

open FiniteDominoProductLaw HLOZFiniteProductCoordinateUnion
open HLOZSourceOrientedThetaExternalProduct
open LazyDecomposition PathInsertion TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Accepted creation is stable throughout this away-total class. -/
def externalAcceptedCreationAtTotals
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Prop :=
  ∀ q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap),
    data.selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) →
    (∀ b, tilingAwayTotal t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2) b =
          ell b) →
    data.atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
        z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1

def externalAcceptedThetaAtTotals
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Prop :=
  externalAcceptedCreationAtTotals data cap ell ∧
    externalThetaAccepts data w externalLow externalHigh cap ell = true

def externalAcceptedThetaPredicate
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
      (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

/-- Exact factorization; the reverse direction uses the complete accepted
base screen rather than an unconditional denominator. -/
theorem externalAcceptedThetaPredicate_factorization
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
    externalAcceptedThetaPredicate data w externalLow externalHigh cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
          z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      data.selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) ∧
        TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap)
          (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) := by
  constructor
  · rintro ⟨⟨hatom, hscreen⟩, haccepted⟩
    exact ⟨hforward q ⟨hatom, haccepted⟩, hscreen⟩
  · rintro ⟨hselected, hscreen⟩
    rcases hscreen with ⟨ell, hell, htotal⟩
    have hrecover := hell.1 q hselected htotal
    exact ⟨⟨hrecover.1, ⟨ell, hell, htotal⟩⟩, hrecover.2⟩

noncomputable def externalAcceptedThetaScreenMass
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
    (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
    (Classical.decPred _)

private theorem screenMass_mono
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (base screened : TruncatedTotals upper → Prop)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, screened ell → base ell) :
    @screenMass Domino _ _ pointMass upper screened (Classical.decPred _) ≤
      @screenMass Domino _ _ pointMass upper base (Classical.decPred _) := by
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : screened ell
  · rw [if_pos hs, if_pos (hsub ell hs)]
  · rw [if_neg hs]
    by_cases hb : base ell
    · rw [if_pos hb]
      exact normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg hb]

private theorem screenMass_decidable_irrel
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (screen : TruncatedTotals upper → Prop)
    (d₁ d₂ : DecidablePred screen) :
    @screenMass Domino _ _ pointMass upper screen d₁ =
      @screenMass Domino _ _ pointMass upper screen d₂ := by
  rw [Subsingleton.elim d₁ d₂]

theorem externalAcceptedThetaScreenMass_le_externalThetaScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (w externalLow externalHigh cap : ℕ) :
    externalAcceptedThetaScreenMass data w externalLow externalHigh cap ≤
      externalThetaScreenMass data w externalLow externalHigh cap := by
  classical
  unfold externalAcceptedThetaScreenMass
  have h := @screenMass_mono
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (fun ell ↦ externalThetaAccepts data w externalLow externalHigh cap ell = true)
    (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
    (externalTheta_pointMass_nonneg data cap)
    (fun _ h ↦ h.2)
  calc
    @screenMass
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (data.upper cap)
        (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
        (Classical.decPred _) ≤
      @screenMass
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (data.upper cap)
        (fun ell ↦ externalThetaAccepts data w externalLow externalHigh cap ell = true)
        (Classical.decPred _) := h
    _ = externalThetaScreenMass data w externalLow externalHigh cap := by
      unfold externalThetaScreenMass
      exact @screenMass_decidable_irrel
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (data.upper cap)
        (fun ell ↦ externalThetaAccepts data w externalLow externalHigh cap ell = true)
        (Classical.decPred _) _

/-- The distinguished mass retained after marginalizing the accepted away
screen. -/
noncomputable def externalAcceptedThetaCarrier
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ) : ℝ :=
  by
    letI : Fintype (TilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) :=
      instFintypeTilingAwayDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)
    letI : Fintype (TilingDistinguishedDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) :=
      instFintypeTilingDistinguishedDomino t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)
    exact ∑ ell : TruncatedTotals (data.upper cap),
      distinguishedAwayMass
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (data.upper cap)
        (fun d ↦ if data.selected cap d then
          ∏ b, ∏ j, geometricGapMass (d b j : ℕ) else 0) ell

theorem externalAcceptedThetaCarrier_nonneg
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ) :
    0 ≤ externalAcceptedThetaCarrier data cap := by
  classical
  letI : Fintype (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  letI : Fintype (TilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) :=
    instFintypeTilingDistinguishedDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
  unfold externalAcceptedThetaCarrier distinguishedAwayMass
  exact Finset.sum_nonneg fun ell _ ↦ Finset.sum_nonneg fun d _ ↦
    mul_nonneg
      (Finset.prod_nonneg fun b _ ↦
        tilingAwayExactTotalMass_nonneg t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S) b (ell b))
      (by
        by_cases hs : data.selected cap d
        · simp only [hs, if_true]
          exact Finset.prod_nonneg fun b _ ↦
            Finset.prod_nonneg fun j _ ↦ geometricGapMass_nonneg _
        · simp only [hs, if_false]
          exact le_rfl)

/-- Exact carrier-weighted stopped mass on one external support atom. -/
theorem externalAcceptedThetaStoppedGeometricMass_eq
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
        (externalAcceptedThetaPredicate data w externalLow externalHigh cap) =
        externalAcceptedThetaScreenMass data w externalLow externalHigh cap *
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
    (externalAcceptedThetaPredicate data w externalLow externalHigh cap)
    (Classical.decPred _)
    (supportComplementDistinguished t z.start z.retained S)
    (data.selected cap) (Classical.decPred _) (data.upper cap)
    (externalAcceptedThetaAtTotals data w externalLow externalHigh cap)
    (Classical.decPred _)
    (externalAcceptedThetaPredicate_factorization data w externalLow
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
  simpa only [externalAcceptedThetaScreenMass,
    externalAcceptedThetaCarrier, tilingDistinguishedAssignmentMass] using h

theorem externalAcceptedThetaStoppedGeometricMass_le
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
        (externalAcceptedThetaPredicate data w externalLow externalHigh cap) ≤
      (2 * ∑ b, externalThetaCost data cap b) *
        externalAcceptedThetaCarrier data cap := by
  rw [externalAcceptedThetaStoppedGeometricMass_eq data w externalLow
    externalHigh cap hforward]
  exact mul_le_mul_of_nonneg_right
    ((externalAcceptedThetaScreenMass_le_externalThetaScreenMass
      data w externalLow externalHigh cap).trans
      (externalThetaScreenMass_le data w externalLow externalHigh cap arith))
    (externalAcceptedThetaCarrier_nonneg data cap)

end

end Erdos1165.HLOZSourceOrientedThetaExternalAccepted
