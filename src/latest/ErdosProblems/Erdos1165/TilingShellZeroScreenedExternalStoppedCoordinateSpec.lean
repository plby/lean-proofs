/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedCrossClockSelectorComparison
import ErdosProblems.Erdos1165.TilingShellZeroExternalStoppedCoordinateSpec

/-!
# Screen-complete external shell-zero stopped coordinates

The coarse external creation predicate is not constant on a pure `I₁` or
fixed-central total screen.  The honest factorization therefore keeps the
complete accepted-creation condition in each away screen.  This record is the
minimal cross-clock interface for those full screens: its only quantitative
input is an explicit finite-screen inequality, not a path-space probability
premise.
-/

open Set

namespace Erdos1165.TilingShellZeroScreenedExternalStoppedCoordinateSpec

open FiniteDominoProductLaw HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroReplacementWindows
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedShellExternalTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedCrossClockSelectorComparison
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Two honest stopped factorizations on one external word and one independent
static distinguished set.  Source/replacement shell conditions, `D_eta`, and
accepted creation all belong to `sourceScreen`/`replacementScreen`. -/
structure LiteralShellZeroScreenedExternalStoppedCoordinateSpec
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) where
  coordinateCap : ℕ → ℕ
  capStart : ℕ
  coordinateCap_eq : ∀ cap, coordinateCap cap = capStart + cap
  sourceStoppingTime : ℕ → StepPath → ℕ
  replacementStoppingTime : ℕ → StepPath → ℕ
  sourceIsStoppingTime : ∀ cap, IsFiniteStoppingTime (sourceStoppingTime cap)
  replacementIsStoppingTime : ∀ cap,
    IsFiniteStoppingTime (replacementStoppingTime cap)
  sourcePredicate : ∀ cap,
    TilingCappedCoordinates z.retainedCount (coordinateCap cap) → Prop
  replacementPredicate : ∀ cap,
    TilingCappedCoordinates z.retainedCount (coordinateCap cap) → Prop
  distinguished : Finset Point
  sourceSelected : ∀ cap,
    TilingDistinguishedCoordinates (cap := coordinateCap cap)
      t z.start z.retained distinguished → Prop
  replacementSelected : ∀ cap,
    TilingDistinguishedCoordinates (cap := coordinateCap cap)
      t z.start z.retained distinguished → Prop
  upper : ∀ cap, TilingAwayDomino t z.start z.retained distinguished → ℕ
  upper_pos : ∀ cap b, 0 < upper cap b
  sourceScreen : ∀ cap, TruncatedTotals (upper cap) → Prop
  replacementScreen : ∀ cap, TruncatedTotals (upper cap) → Prop
  source_factorization : ∀ cap q,
    sourcePredicate cap q ∧ PrefixedTilingStoppingAccepted
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
          (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      sourceSelected cap ((splitTilingCoordinatesEquiv t z.start z.retained
        distinguished q).1) ∧
      TilingAwayTotalsScreen t z.start z.retained distinguished (upper cap)
        (sourceScreen cap)
        ((splitTilingCoordinatesEquiv t z.start z.retained distinguished q).2)
  replacement_factorization : ∀ cap q,
    replacementPredicate cap q ∧ PrefixedTilingStoppingAccepted
        (replacementStoppingTime cap) z.initial.1 t z.start z.retained
          (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      replacementSelected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            distinguished q).1) ∧
      TilingAwayTotalsScreen t z.start z.retained distinguished (upper cap)
        (replacementScreen cap)
        ((splitTilingCoordinatesEquiv t z.start z.retained distinguished q).2)
  source_selected_subset : ∀ cap d,
    sourceSelected cap d → replacementSelected cap d
  /-- The deterministic finite-screen comparison supplied by the literal
  source-to-replacement coordinate transformation. -/
  screen_bound : ∀ cap,
    @screenMass
        (TilingAwayDomino t z.start z.retained distinguished)
        (instFintypeTilingAwayDomino t z.start z.retained distinguished)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := coordinateCap cap) t z.start z.retained
          distinguished) (upper cap) (sourceScreen cap)
        (Classical.decPred (sourceScreen cap)) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        @screenMass
          (TilingAwayDomino t z.start z.retained distinguished)
          (instFintypeTilingAwayDomino t z.start z.retained distinguished)
          (fun a b ↦ Subtype.instDecidableEq a b)
          (tilingAwayPointMass (cap := coordinateCap cap) t z.start z.retained
            distinguished) (upper cap) (replacementScreen cap)
          (Classical.decPred (replacementScreen cap))
  source_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (sourcePredicate cap)) ⊆
      orientedValidShellZeroExactSourceExternalTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z
  replacement_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (replacementStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (replacementPredicate cap)) ⊆
      orientedValidShellZeroReplacementExternalTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total) z
  source_complete :
    orientedValidShellZeroExactSourceExternalTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
        (coordinateCap cap) z.tail.1 (sourcePredicate cap))
  replacement_complete :
    orientedValidShellZeroReplacementExternalTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total) z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (replacementStoppingTime cap) z.initial.1 t z.start z.retained
        (coordinateCap cap) z.tail.1 (replacementPredicate cap))
  source_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (sourcePredicate cap))

/-- Cross-clock bound for full accepted-creation screens.  The generic theorem
is again called with formal source/replacement roles swapped. -/
theorem LiteralShellZeroScreenedExternalStoppedCoordinateSpec.coordinate_bound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : LiteralShellZeroScreenedExternalStoppedCoordinateSpec
      t o m k low externalLow externalHigh total z) (cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass (data.sourceStoppingTime cap)
        z.initial.1 t z.start z.retained (data.coordinateCap cap) z.tail.1
          (data.sourcePredicate cap) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        prefixedTilingStoppedAcceptedGeometricMass
          (data.replacementStoppingTime cap) z.initial.1 t z.start z.retained
          (data.coordinateCap cap) z.tail.1
            (data.replacementPredicate cap) := by
  classical
  have hselector := prefixedTilingDistinguishedSelectorMass_mono
    t z.start z.retained data.distinguished (data.upper cap)
      (data.replacementSelected cap) (data.sourceSelected cap)
      (data.source_selected_subset cap)
  exact prefixedTilingStoppedAcceptedGeometricMass_le_of_crossClock
    (data.replacementStoppingTime cap) (data.sourceStoppingTime cap)
    z.initial.1 t z.start z.retained z.tail.1
    (data.replacementPredicate cap) (data.sourcePredicate cap)
    data.distinguished (data.replacementSelected cap)
    (data.sourceSelected cap) (data.upper cap) (data.replacementScreen cap)
    (data.sourceScreen cap) (data.replacement_factorization cap)
    (data.source_factorization cap)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      t z.start z.retained data.distinguished (data.upper cap)
        (data.upper_pos cap))
    (centralReplacementRatio shellZeroLocalRatioConstant total)
    (HLOZShellZeroCentralTail.centralReplacementRatio_nonneg
      shellZeroLocalRatioConstant_pos.le total)
    (data.screen_bound cap) hselector

end

end Erdos1165.TilingShellZeroScreenedExternalStoppedCoordinateSpec
