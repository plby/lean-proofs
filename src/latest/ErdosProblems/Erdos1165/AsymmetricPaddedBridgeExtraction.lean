/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedEndpointHarnack
import ErdosProblems.Erdos1165.AsymmetricExtractedReturnCompletion
import ErdosProblems.Erdos1165.AnnularRadialOneStepRow
import ErdosProblems.Erdos1165.AnnularErasedParentSpine

/-!
# Extracting the padded return skeleton inside a coarse bridge

A coarse asymmetric bridge first hits the level-`l` boundary.  At the
padded level `p`, delete every completed return from level `p` to level
`p-1`.  The remainder is a genuine timed terminal skeleton: every selected
return finishes before the coarse bridge exits, and reinsertion recovers the
original bridge word exactly.

This is the pathwise half of the padded endpoint normalization.  It is
stated for arbitrary separated regular levels so that the later mass row can
use it one coarse bridge at a time.
-/

open Set

namespace Erdos1165.AsymmetricPaddedBridgeExtraction

open AnnularBoundaryExcursionKernel AnnularOffspringRenewal
open AnnularErasedParentSpine
open AnnularProfileClocks
open AsymmetricExtractedReturnCompletion AsymmetricSplitLevelSplice
open MarkedBridgeFactorization
open PlanarPotential TerminalProfileBoundarySeparation
open TerminalSkeletonFactorization TerminalSpliceProfileGeometry
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint
open TerminalSequentialVisitLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Number of completed level-`p` returns inside one fixed level-`l`
first-exit bridge. -/
def paddedBridgeReturnCount
    (n l p : ℕ) (center start endpoint : Point)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) : ℕ :=
  boundaryExcursionCount
    (profileInnerBoundary n (p - 1) center)
    (profileInnerBoundary n p center) start
    (extendStoppedWord bridge.1) bridge.1.1

/-- The level immediately outside `p` separates every level-`p` entrance
from the coarse level-`l` exit boundary. -/
theorem paddedBoundary_firstHitSeparates
    {n l p : ℕ} {center z : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (hz : z ∈ profileInnerBoundary n p center) :
    FirstHitSeparates
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n l center) z := by
  apply FirstHitSeparates.discBoundaries hz
  · exact scaleRadius_antitone_of_le (by omega : p - 1 ≤ p) hp
  · have hadjacent :
        scaleRadius n (p - 1) + 1 ≤ scaleRadius n (p - 2) :=
      scaleRadius_add_one_le_previous hn (by omega) (by omega)
    exact hadjacent.trans
      (scaleRadius_antitone_of_le (by omega : l ≤ p - 2) (by omega))

/-- Every return selected by the exact padded excursion count finishes
before the coarse bridge's first outer exit. -/
theorem paddedBridgeReturnComplete
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    let middle := profileInnerBoundary n (p - 1) center
    let inner := profileInnerBoundary n p center
    let horizon := bridge.1.1
    let q := paddedBridgeReturnCount n l p center start endpoint bridge
    ∀ j : Fin q,
      excursionStart
          (trajectoryFrom start (extendStoppedWord bridge.1))
          middle inner horizon (j + 1) ≤ horizon := by
  dsimp only
  apply returnExitTime_le_of_boundaryExcursionExitAtom
    bridge.2.1 rfl
  intro z hz
  exact paddedBoundary_firstHitSeparates hn hlp hp hz

/-- The extracted padded skeleton is well formed and reconstructs the
literal coarse bridge word. -/
theorem paddedBridge_extract_returnSkeleton
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    let middle := profileInnerBoundary n (p - 1) center
    let inner := profileInnerBoundary n p center
    let horizon := bridge.1.1
    let omega := extendStoppedWord bridge.1
    let q := paddedBridgeReturnCount n l p center start endpoint bridge
    let t := extractTimedReturnSkeleton omega start middle inner horizon q
    t.WellFormed ∧
      reconstructTerminalPacket (packetOfTimedSkeleton omega t) =
        incrementSlice omega 0 horizon := by
  dsimp only
  have hcomplete := paddedBridgeReturnComplete hn hlp hp bridge
  exact ⟨extractTimedReturnSkeleton_wellFormed hcomplete,
    reconstruct_extractTimedReturnSkeleton hcomplete⟩

/-- A selected padded entrance lies on the level-`p` boundary. -/
theorem paddedBridgeEntrancePoint_mem_inner
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint)
    (j : Fin (paddedBridgeReturnCount n l p center start endpoint bridge)) :
    let middle := profileInnerBoundary n (p - 1) center
    let inner := profileInnerBoundary n p center
    let horizon := bridge.1.1
    let omega := extendStoppedWord bridge.1
    let q := paddedBridgeReturnCount n l p center start endpoint bridge
    (extractTimedReturnSkeleton omega start middle inner horizon q).entrancePoint j
      ∈ inner := by
  dsimp only
  let middle := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := bridge.1.1
  let omega := extendStoppedWord bridge.1
  let q := paddedBridgeReturnCount n l p center start endpoint bridge
  have hcomplete := paddedBridgeReturnComplete hn hlp hp bridge
  have hfinish :
      excursionFinish (trajectoryFrom start omega) middle inner horizon (j : ℕ) ≤
        horizon :=
    (TerminalExcursionPathwise.excursionFinish_le_next_start
      (trajectoryFrom start omega) middle inner horizon (j : ℕ)).trans
      (hcomplete j)
  have hmem := excursionFinish_mem_inner_of_le
    (trajectoryFrom start omega) middle inner horizon (j : ℕ) hfinish
  simpa only [extractTimedReturnSkeleton, returnEntrancePoint,
    returnEntranceTime] using hmem

/-- Replacing the deleted padded returns by arbitrary endpoint-matched
first-return words preserves the coarse bridge's first level-`l` exit. -/
theorem paddedBridgeGlobalFirst
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    let middle := profileInnerBoundary n (p - 1) center
    let inner := profileInnerBoundary n p center
    let horizon := bridge.1.1
    let omega := extendStoppedWord bridge.1
    let q := paddedBridgeReturnCount n l p center start endpoint bridge
    let t := extractTimedReturnSkeleton omega start middle inner horizon q
    let code := compressTimedSkeleton omega t
    ∀ replacements : (j : Fin q) → BoundaryExitWordCode middle
        (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt (profileInnerBoundary n l center) start
        (assembledTerminalPath code
          (fun j ↦ List.ofFn (replacements j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (replacements j).1.2)) := by
  dsimp only
  let middle := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := bridge.1.1
  let omega := extendStoppedWord bridge.1
  let q := paddedBridgeReturnCount n l p center start endpoint bridge
  let t := extractTimedReturnSkeleton omega start middle inner horizon q
  have hcomplete := paddedBridgeReturnComplete hn hlp hp bridge
  have ht : t.WellFormed := extractTimedReturnSkeleton_wellFormed hcomplete
  intro replacements
  apply absoluteBoundaryFirstAt_boundaryExitWords_complementaryPieces_from
    (B := profileInnerBoundary n l center)
    (D := disc center (scaleRadius n (p - 1)))
    ht bridge.2.1 rfl
  · intro z hz houter
    have hadjacent :
        scaleRadius n (p - 1) + 1 ≤ scaleRadius n (p - 2) :=
      scaleRadius_add_one_le_previous hn (by omega) (by omega)
    have hsep : scaleRadius n (p - 1) + 1 ≤ scaleRadius n l :=
      hadjacent.trans
        (scaleRadius_antitone_of_le (by omega : l ≤ p - 2) (by omega))
    exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hz hsep) houter
  · intro j
    have hinner := paddedBridgeEntrancePoint_mem_inner hn hlp hp bridge j
    exact hinner.1.trans
      (scaleRadius_antitone_of_le (by omega : p - 1 ≤ p) hp)
  · intro j
    rfl
  · intro j
    rfl

/-- Completion atom obtained by retaining the remote spine of one coarse
bridge and varying only its padded level-`p` returns. -/
def paddedBridgeCompletionAtom
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :=
  let middle := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := bridge.1.1
  let omega := extendStoppedWord bridge.1
  let q := paddedBridgeReturnCount n l p center start endpoint bridge
  let t := extractTimedReturnSkeleton omega start middle inner horizon q
  boundaryReturnCompletionAtom (start := 0) (compressTimedSkeleton omega t)
    middle (profileInnerBoundary n l center) start
    (paddedBridgeGlobalFirst hn hlp hp bridge)

/-- The original coarse bridge path belongs to its own padded completion
atom. -/
theorem source_mem_paddedBridgeCompletionAtom
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    extendStoppedWord bridge.1 ∈
      (paddedBridgeCompletionAtom hn hlp hp bridge).event := by
  let middle := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := bridge.1.1
  let omega := extendStoppedWord bridge.1
  let q := paddedBridgeReturnCount n l p center start endpoint bridge
  let t := extractTimedReturnSkeleton omega start middle inner horizon q
  let code := compressTimedSkeleton omega t
  have hcomplete := paddedBridgeReturnComplete hn hlp hp bridge
  have ht : t.WellFormed := extractTimedReturnSkeleton_wellFormed hcomplete
  let source := extractedReturnCodes hcomplete
  have hcylinder : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix 0 omega) code
        (fun j ↦ List.ofFn (source j).1.2)) := by
    have hsourceWords : (fun j ↦ List.ofFn (source j).1.2) =
        intervalWords omega t.entrance t.exit := by
      funext j
      exact extractedReturnCodes_toList hcomplete j
    rw [hsourceWords]
    have hshift : shiftSteps 0 omega = omega := by
      funext r
      simp [shiftSteps]
    simpa only [hshift] using
      (mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
        (start := 0) omega t ht)
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix 0 omega, source), ?_⟩
  simpa only [paddedBridgeCompletionAtom, code, t, q, omega, horizon,
    inner, middle, boundaryReturnCompletionAtom] using hcylinder

/-- Exact retained-spine times deleted-return product mass for the padded
bridge completion. -/
theorem fairSteps_paddedBridgeCompletionAtom
    {n l p : ℕ} {center start endpoint : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
      start endpoint) :
    fairSteps (paddedBridgeCompletionAtom hn hlp hp bridge).event =
      (paddedBridgeCompletionAtom hn hlp hp bridge).weight *
        ∏ j, (paddedBridgeCompletionAtom hn hlp hp bridge).kernel j := by
  exact fairSteps_event_eq_weight_mul_prod_kernel _

end

end Erdos1165.AsymmetricPaddedBridgeExtraction
