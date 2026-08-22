/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellExternalTracePartition
import ErdosProblems.Erdos1165.TilingPrefixedCrossClockSelectorComparison
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Source-correct external-word shell-zero stopped coordinates

This is the replacement for the same-current-favorite
`LiteralShellZeroStoppedCoordinateSpec`.  It fixes only the physical oriented
external word.  A common static distinguished set `D` is part of the fibre,
but is independent of both the source `V₂(I₁)` support and the replacement
`V₂(I₁∪I₀)` support; those path conditions occur in the two screened
predicates and their coverage theorems.

The two clocks may have different distinguished selectors.  The finite
comparison needs only that the source selector's distinguished mass is at
most the replacement selector's distinguished mass.
-/

open Set

namespace Erdos1165.TilingShellZeroExternalStoppedCoordinateSpec

open FiniteDominoProductLaw HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedShellExternalTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedCrossClockSelectorComparison
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Nonempty valid exact source atoms indexed only by the corrected external
word.  No current-favorite datum and no pathwise support set is an index. -/
abbrev SupportedSourceExternalTraceIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ) :=
  {z : OrientedTilingTypedExternalWordCode t //
    (orientedValidShellZeroExactSourceExternalTraceAtom t o m k
      (shellWidth48 m) low externalLow externalHigh total z).Nonempty}

/-- Literal cross-clock data on one external retained word.

`distinguished` is static and common to the two factorizations.  It must not
be instantiated with either pathwise oriented `V₂` support complement. -/
structure LiteralShellZeroExternalStoppedCoordinateSpec
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
  coordinateSupport : ∀ cap, LiteralShellZeroCoordinateSupportData
    (cap := coordinateCap cap) (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total)
      t z.start z.retained distinguished (upper cap)
  source_factorization : ∀ cap q,
    sourcePredicate cap q ∧ PrefixedTilingStoppingAccepted
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
          (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      sourceSelected cap ((splitTilingCoordinatesEquiv t z.start z.retained
        distinguished q).1) ∧
      TilingAwayTotalsScreen t z.start z.retained distinguished (upper cap)
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
          t z.start z.retained distinguished (upper cap) b v)
        ((splitTilingCoordinatesEquiv t z.start z.retained distinguished q).2)
  replacement_factorization : ∀ cap q,
    replacementPredicate cap q ∧ PrefixedTilingStoppingAccepted
        (replacementStoppingTime cap) z.initial.1 t z.start z.retained
          (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      replacementSelected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            distinguished q).1) ∧
      TilingAwayTotalsScreen t z.start z.retained distinguished (upper cap)
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t z.start z.retained distinguished (upper cap) b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t z.start z.retained distinguished (upper cap) b v)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total))
        ((splitTilingCoordinatesEquiv t z.start z.retained distinguished q).2)
  /-- The source distinguished selector injects into the replacement
  selector.  To prove the desired `actualSourceMass ≤ ratio *
  actualReplacementMass`, the generic cross-clock theorem is invoked with
  its formal `replacement` arguments equal to the actual source data and its
  formal `source` arguments equal to the actual replacement data. -/
  source_selected_subset : ∀ cap d,
    sourceSelected cap d → replacementSelected cap d
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

end

end Erdos1165.TilingShellZeroExternalStoppedCoordinateSpec
