/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedRaisedRankAcceptedCreation

/-!
# Raised-rank acceptance with a physical endpoint-local-time hypothesis

The common terminal domino need not be represented by the retained word
(the one-step tail is the important case).  The source-correct clock transfer
therefore asks only for equality of the two final-site local times.  It does
not require the terminal base to belong to the distinguished represented set.
-/

namespace Erdos1165.TilingPrefixedRaisedRankAcceptedCreationEndpoint

open HLOZPathEvents LazyDecomposition PreStoppingFiber
open PreStoppingSpatialLaw StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Accepted creation transfers from rank `k` to rank `k + delta` from the
final threshold-count identity and the literal common-endpoint local-time
identity. -/
theorem prefixedTilingStoppingAccepted_of_thresholdCount_add_of_endpointLocal
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (m k delta cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (q q' : TilingCappedCoordinates i cap)
    (hcount :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let v' := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q' j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      let s' := trajectory (extendPrefix (directionVectorOfList v'))
      thresholdCount s' v'.length m = thresholdCount s v.length m + delta)
    (hendpointLocal :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let v' := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q' j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      let s' := trajectory (extendPrefix (directionVectorOfList v'))
      localTime s v.length (s v.length) =
        localTime s' v'.length (s' v'.length))
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1) :
    PrefixedTilingStoppingAccepted (truncatedLevelTime m (k + delta) cutoff)
      initial.1 t x r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q' j : ℕ)) tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  let s := trajectory omega
  let s' := trajectory omega'
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
  · simpa only [s, s', v, v'] using
      hcount.trans (congrArg (· + delta) hcountSource)
  · simpa only [s, s', v, v'] using hendpointLocal ▸ hlocalSource

end

end Erdos1165.TilingPrefixedRaisedRankAcceptedCreationEndpoint
