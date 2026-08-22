/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroThresholdCountAdd

/-!
# Accepted replacement creation at the actual shell-zero endpoint increment

This is the fixed-`delta` reconstruction theorem.  An all-source accepted
physical prefix and an exact-central replacement vector with endpoint screen
`delta` produce an accepted replacement physical prefix at rank `k + delta`.
-/

namespace Erdos1165.TilingShellZeroDeltaAcceptedCreation

open FiniteDominoProductLaw LazyDecomposition PreStoppingFiber
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedRaisedRankAcceptedCreation
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementScreen TilingShellZeroSourcePartition
open TilingShellZeroThresholdCountAdd TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Exact endpoint-increment screening supplies the honest raised stopping
clock required by the replacement fibre. -/
theorem prefixedTilingStoppingAccepted_at_actualEndpointIncrement
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (k delta cutoff central : ℕ) (hm : 0 < m) (hk : 0 < k)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hbaseFinal :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      tilingBase t
        (trajectory (extendPrefix (directionVectorOfList vSource))
          vSource.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (hreplacement : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        D upper central delta ellReplacement)
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length < cutoff)
    (haccepted :
      PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (qSource j : ℕ)) tail.1) :
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta) cutoff)
        initial.1 t x r (fun j ↦ (qReplacement j : ℕ)) tail.1 := by
  have hcount :=
    thresholdCount_prefixedTilingInsertion_add_of_endpointIncrement
      initial t x r tail D upper hm qSource qReplacement ellSource
        ellReplacement central delta hstart hdist hbase hdominance hsource
        hreplacement htotalSource htotalReplacement
  exact prefixedTilingStoppingAccepted_of_thresholdCount_add
    initial t x m k delta cutoff hm hk r tail D qSource qReplacement hstart
      hbaseFinal hdist hcount hpos hpos' hlt hlt' haccepted

end

end Erdos1165.TilingShellZeroDeltaAcceptedCreation
