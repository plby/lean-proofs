/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaAcceptedCreation
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportEndpointLocal

/-!
# Actual-delta accepted creation on the complete static support

This is the source-correct replacement of the earlier helper which required
the terminal base to be a represented distinguished domino.  A one-step tail
can be unrepresented.  Here terminal local-time invariance is derived from
the full static carrier and the source terminal `V₁` fact.
-/

namespace Erdos1165.TilingShellZeroDeltaAcceptedCreationEndpoint

open FiniteDominoProductLaw HLOZPathEvents
open HLOZShellZeroReplacementWindows LazyDecomposition
open PreStoppingFiber PreStoppingSpatialLaw SpatialInsertionFiber
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedRaisedRankAcceptedCreationEndpoint
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroStaticSupportEndpointLocal
open TilingShellZeroSourcePartition TilingShellZeroThresholdCountAdd
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The actual endpoint screen raises the rank without assuming that the
physical terminal domino is represented by the retained external word. -/
theorem prefixedTilingStoppingAccepted_at_actualEndpointIncrement_staticSupport
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (S : Finset Point)
    (upper : TilingAwayDomino t x r
      (tilingExternalDominoBases t x r \ S) → ℕ)
    (k delta cutoff central : ℕ) (hm : 0 < m) (hk : 0 < k)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) qSource).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r
        (tilingExternalDominoBases t x r \ S) upper b (ellSource b))
    (hreplacement : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        (tilingExternalDominoBases t x r \ S) upper central delta
          ellReplacement)
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hsourceVTwo :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      ∀ b ∈ S, tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length b)
    (hterminalVOne :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      tilingVOneAt t m sSource vSource.length
        (tilingBase t (sSource vSource.length)))
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length < cutoff)
    (haccepted : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (qSource j : ℕ)) tail.1) :
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta) cutoff)
        initial.1 t x r (fun j ↦ (qReplacement j : ℕ)) tail.1 := by
  have hcount :=
    thresholdCount_prefixedTilingInsertion_add_of_endpointIncrement
      initial t x r tail (tilingExternalDominoBases t x r \ S) upper hm
        qSource qReplacement ellSource ellReplacement central delta hstart
        hdist hbase hdominance hsource hreplacement htotalSource
        htotalReplacement
  have hendpoint :=
    prefixedTilingFinalLocalTime_eq_of_staticSourceSupport
      initial t x r tail S qSource qReplacement hstart hdist hsourceVTwo
        hterminalVOne
  exact
    prefixedTilingStoppingAccepted_of_thresholdCount_add_of_endpointLocal
      initial t x m k delta cutoff hm hk r tail qSource qReplacement hcount
        hendpoint hpos hpos' hlt hlt' haccepted

end

end Erdos1165.TilingShellZeroDeltaAcceptedCreationEndpoint
