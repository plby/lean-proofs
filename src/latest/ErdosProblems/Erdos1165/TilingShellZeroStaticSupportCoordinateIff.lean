/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportLocalTimeTransport

/-!
# Exact coordinate/window correspondence on a prefixed static carrier

The forward implications are the existing local-time reconstruction lemmas.
The reverse implications are the subtraction-safe arithmetic needed to read
the fixed source subset back from the literal replacement path.
-/

namespace Erdos1165.TilingShellZeroStaticSupportCoordinateIff

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingPrefixedInsertedLocalTime
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingShellZeroStaticSupportLocalTimeTransport

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem tilingShellZeroSourceCoordinate_iff_prefixedVTwo
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (q : TilingCappedCoordinates i cap) (ell : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (b : TilingAwayDomino t x r D)
    (hbase : prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) b.1.1 =
      Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) (tilingPartner t b.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) b.1.1)
    (htranslate : Fintype.card (TilingCoordinatesAt t x r b.1) ≤
      m - w + 1)
    (htotal : tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 =
      (ell b : ℕ)) :
    tilingShellZeroSourceCoordinate
        (cap := cap) (m := m) (w := w) t x r D upper b (ell b) ↔
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length b.1.1 := by
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  constructor
  · intro hcoord
    exact tilingVTwoAt_source_of_prefixedSourceCoordinate initial t x r tail
      D upper q ell hstart b hbase hdominance htranslate hcoord htotal
  · intro hV
    have hpath : finitePathList (pathPrefix s v.length) =
        prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal :=
      finitePathList_prefixedTilingInsertionPrefix
        initial t x r (fun j ↦ (q j : ℕ)) tail hstart
    have hbaseLocal : localTime s v.length b.1.1 =
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b.1.1 +
          (ell b : ℕ) := by
      rw [localTime_eq_listLocalTime, hpath,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
            (tilingExternalDomino_isBase t x r b.1), htotal]
    simp only [tilingShellZeroSourceCoordinate,
      mem_shellZeroSourceFailureWindow]
    have hwindow := mem_shellZeroSourceTotalWindow.mp hV.2
    rw [hbaseLocal, hbase] at hwindow
    omega

theorem tilingShellZeroReplacementCoordinate_iff_prefixedVTwo
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (q : TilingCappedCoordinates i cap) (ell : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (b : TilingAwayDomino t x r D)
    (hbase : prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) b.1.1 =
      Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) (tilingPartner t b.1.1) ≤
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (q j : ℕ)) tail) b.1.1)
    (htranslate : Fintype.card (TilingCoordinatesAt t x r b.1) ≤ m + 1)
    (htotal : tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 =
      (ell b : ℕ)) :
    tilingShellZeroReplacementCoordinate
        (cap := cap) (m := m) (w := w) t x r D upper b (ell b) ↔
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t (shellZeroReplacementTotalWindow m w)
        s v.length b.1.1 := by
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  constructor
  · intro hcoord
    exact tilingVTwoAt_replacement_of_prefixedReplacementCoordinate
      initial t x r tail D upper q ell hstart b hbase hdominance hcoord htotal
  · intro hV
    have hpath : finitePathList (pathPrefix s v.length) =
        prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal :=
      finitePathList_prefixedTilingInsertionPrefix
        initial t x r (fun j ↦ (q j : ℕ)) tail hstart
    have hbaseLocal : localTime s v.length b.1.1 =
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b.1.1 +
          (ell b : ℕ) := by
      rw [localTime_eq_listLocalTime, hpath,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
            (tilingExternalDomino_isBase t x r b.1), htotal]
    simp only [tilingShellZeroReplacementCoordinate,
      mem_shellZeroReplacementFailureWindow]
    have hwindow := mem_shellZeroReplacementTotalWindow.mp hV.2
    rw [hbaseLocal, hbase] at hwindow
    omega

end

end Erdos1165.TilingShellZeroStaticSupportCoordinateIff
