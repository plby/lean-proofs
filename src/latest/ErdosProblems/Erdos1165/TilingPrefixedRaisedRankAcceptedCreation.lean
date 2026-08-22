/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedFavoriteTraceSupport

/-!
# Prefix-correct accepted creation at a raised rank

The source and replacement insertion vectors have the same physical prefix,
retained word, tail, and distinguished projection.  Consequently their final
site and its final local time agree.  If their final threshold counts differ
by `delta`, acceptance at rank `k` transfers to acceptance at rank
`k + delta`.  This is the deterministic clock statement required by the
actual-endpoint-increment shell-zero partition.
-/

namespace Erdos1165.TilingPrefixedRaisedRankAcceptedCreation

open HLOZPathEvents LazyDecomposition PreStoppingFiber
open PreStoppingSpatialLaw
open StoppedInsertion VariableStoppedFiber VariableStoppedTracePartition
open TilingCappedMarginalization TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Accepted creation transfers from rank `k` to rank `k + delta` when the
replacement final threshold count is exactly the source count plus `delta`.
No claim about the threshold sets at intermediate times is needed. -/
theorem prefixedTilingStoppingAccepted_of_thresholdCount_add
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (m k delta cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hbase :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      tilingBase t
        (trajectory (extendPrefix (directionVectorOfList v)) v.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hcount :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let v' := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q' j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      let s' := trajectory (extendPrefix (directionVectorOfList v'))
      thresholdCount s' v'.length m = thresholdCount s v.length m + delta)
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff)
    (haccepted :
      PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (q j : ℕ)) tail.1) :
    PrefixedTilingStoppingAccepted (truncatedLevelTime m (k + delta) cutoff)
      initial.1 t x r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  let s := trajectory omega
  let s' := trajectory omega'
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  have hend : s v.length = s' v'.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates
      initial t x r qNat qNat' tail hstart
  have hlocalList := prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
    initial.1 t x r terminal D q q' hdist (s v.length) hbase
  have hlocal : localTime s v.length (s v.length) =
      localTime s' v'.length (s' v'.length) := by
    rw [← hend, localTime_eq_listLocalTime, localTime_eq_listLocalTime,
      hpath, hpath']
    exact hlocalList
  unfold PrefixedTilingStoppingAccepted at haccepted ⊢
  change truncatedLevelTime m k cutoff omega = v.length at haccepted
  change truncatedLevelTime m (k + delta) cutoff omega' = v'.length
  rw [truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v.length omega hlt,
    thresholdCreation_iff_terminal_count_and_new_localTime
      s m k v.length hm hk hpos] at haccepted
  rw [truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + delta) cutoff v'.length omega' hlt',
    thresholdCreation_iff_terminal_count_and_new_localTime
      s' m (k + delta) v'.length hm (by omega) hpos']
  rcases haccepted with ⟨hcountSource, hlocalSource⟩
  constructor
  · simpa only [s, s', v, v', qNat, qNat'] using
      hcount.trans (congrArg (· + delta) hcountSource)
  · exact hlocal ▸ hlocalSource

end

end Erdos1165.TilingPrefixedRaisedRankAcceptedCreation
