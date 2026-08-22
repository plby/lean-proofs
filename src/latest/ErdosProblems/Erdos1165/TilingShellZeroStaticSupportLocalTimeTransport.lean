/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroDeltaAcceptedCreationEndpoint

/-!
# Endpointwise local-time transport on the static shell carrier

Off the moved support, local times are fixed either by the distinguished
projection or because the domino is absent from the retained word.  On a
moved away domino, the literal translated coordinate windows reconstruct
the actual `V₂(I₁)` and `V₂(I₀)` predicates.
-/

namespace Erdos1165.TilingShellZeroStaticSupportLocalTimeTransport

open FiniteDominoProductLaw HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Every endpoint of a base outside the static moved support has unchanged
physical-prefix local time. -/
theorem prefixedTilingLocalTime_eq_of_base_not_staticSupport
    (initial : BoundaryTail) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (S : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q').1)
    (y : Point) (hy : tilingBase t y ∉ S) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    localTime s' v'.length y = localTime s v.length y := by
  classical
  let D := tilingExternalDominoBases t x r \ S
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q' j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  have hterminal' : prefixedTilingInsertionTerminal initial t x r
      (fun j ↦ (q' j : ℕ)) tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail
        hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q j : ℕ)) tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q' j : ℕ)) tail hstart
  change localTime s' v'.length y = localTime s v.length y
  rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime, hpath', hpath]
  by_cases hyExternal : tilingBase t y ∈ tilingExternalDominoBases t x r
  · symm
    apply prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
      initial.1 t x r terminal D q q'
    · simpa only [D] using hdist
    · exact Finset.mem_sdiff.mpr ⟨hyExternal, hy⟩
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial.1 t x r (fun j ↦ (q' j : ℕ)) terminal y hyExternal,
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial.1 t x r (fun j ↦ (q j : ℕ)) terminal y hyExternal]

/-- A translated source coordinate is the literal actual `V₂(I₁)` condition
on the reconstructed physical prefix. -/
theorem tilingVTwoAt_source_of_prefixedSourceCoordinate
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
    (hcoord : tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ell b))
    (htotal : tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 =
      (ell b : ℕ)) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length b.1.1 := by
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q j : ℕ)) tail hstart
  have hbaseLocal : localTime s v.length b.1.1 =
      prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b.1.1 +
        (ell b : ℕ) := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
          (tilingExternalDomino_isBase t x r b.1), htotal]
  have hpartnerLocal : localTime s v.length (tilingPartner t b.1.1) =
      prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal
          (tilingPartner t b.1.1) + (ell b : ℕ) := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1
          (tilingPartner t b.1.1)
          (tilingPartner_ofExternalDomino_has_base t x r b.1), htotal]
  refine ⟨?_, ?_⟩
  · rw [hbaseLocal, hpartnerLocal]
    exact Nat.add_le_add_right hdominance _
  · simp only [tilingShellZeroSourceCoordinate,
      mem_shellZeroSourceFailureWindow] at hcoord
    simp only [mem_shellZeroSourceTotalWindow]
    rw [hbaseLocal, hbase]
    omega

/-- A translated replacement coordinate is the literal actual `V₂(I₀)`
condition on the reconstructed physical prefix. -/
theorem tilingVTwoAt_replacement_of_prefixedReplacementCoordinate
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
    (hcoord : tilingShellZeroReplacementCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ell b))
    (htotal : tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 =
      (ell b : ℕ)) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s v.length
      b.1.1 := by
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q j : ℕ)) tail hstart
  have hbaseLocal : localTime s v.length b.1.1 =
      prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b.1.1 +
        (ell b : ℕ) := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
          (tilingExternalDomino_isBase t x r b.1), htotal]
  have hpartnerLocal : localTime s v.length (tilingPartner t b.1.1) =
      prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal
          (tilingPartner t b.1.1) + (ell b : ℕ) := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r (fun j ↦ (q j : ℕ)) terminal b.1
          (tilingPartner t b.1.1)
          (tilingPartner_ofExternalDomino_has_base t x r b.1), htotal]
  refine ⟨?_, ?_⟩
  · rw [hbaseLocal, hpartnerLocal]
    exact Nat.add_le_add_right hdominance _
  · simp only [tilingShellZeroReplacementCoordinate,
      mem_shellZeroReplacementFailureWindow] at hcoord
    simp only [mem_shellZeroReplacementTotalWindow]
    rw [hbaseLocal, hbase]
    omega

end

end Erdos1165.TilingShellZeroStaticSupportLocalTimeTransport
