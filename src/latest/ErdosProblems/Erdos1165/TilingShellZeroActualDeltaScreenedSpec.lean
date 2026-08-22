/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaPartition
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportScreenedSpec

/-!
# Honest screened stopped coordinates with actual-rank pieces

The finite product comparison still uses a single replacement stopped
event.  Instead of asserting that this event has the false fixed rank
`k + total - central`, it is measurably covered by pieces labelled by the
actual endpoint increment `delta`.  Each piece is sound for the
corresponding external/static-support atom.
-/

open MeasureTheory Set

namespace Erdos1165.TilingShellZeroActualDeltaScreenedSpec

open FiniteDominoProductLaw HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedCrossClockSelectorComparison
open TilingPrefixedStoppedProductDisintegration TilingSpatialInsertionFiber
open TilingShellZeroActualDeltaPartition
open TilingShellZeroExternalStaticSupportPartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Corrected literal stopped-coordinate specification.  The replacement
event is covered by measurable actual-increment pieces; it is not required
to live at a guessed common rank. -/
structure LiteralShellZeroActualDeltaScreenedSpec
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) where
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
      replacementSelected cap ((splitTilingCoordinatesEquiv
        t z.start z.retained distinguished q).1) ∧
      TilingAwayTotalsScreen t z.start z.retained distinguished (upper cap)
        (replacementScreen cap)
        ((splitTilingCoordinatesEquiv t z.start z.retained distinguished q).2)
  source_selected_subset : ∀ cap d,
    sourceSelected cap d → replacementSelected cap d
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
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z S
  source_complete :
    orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z S ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
        (coordinateCap cap) z.tail.1 (sourcePredicate cap))
  replacementPiece : ∀ cap,
    ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) →
      Set WalkPath
  measurable_replacementPiece : ∀ cap delta,
    MeasurableSet (replacementPiece cap delta)
  replacement_cover : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent
      (replacementStoppingTime cap) z.initial.1 t z.start z.retained
      (coordinateCap cap) z.tail.1 (replacementPredicate cap)) ⊆
      ⋃ delta, replacementPiece cap delta
  replacement_piece_sound : ∀ cap delta,
    replacementPiece cap delta ⊆
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
        delta z S
  source_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (sourcePredicate cap))

theorem LiteralShellZeroActualDeltaScreenedSpec.coordinate_bound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTilingTypedExternalWordCode t} {S : Finset Point}
    (data : LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
      externalHigh total z S) (cap : ℕ) :
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
    (centralReplacementRatio_nonneg shellZeroLocalRatioConstant_pos.le total)
    (data.screen_bound cap) hselector

end

end Erdos1165.TilingShellZeroActualDeltaScreenedSpec
