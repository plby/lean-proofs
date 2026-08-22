/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricBufferedProfileSplice
import ErdosProblems.Erdos1165.AsymmetricCoarseSplitCompletionSource

/-!
# Extracted geometry for coarse completion rows

This file keeps the clock extractor out of the source-dependent candidate
subtype.  Endpoint geometry is built once from an arbitrary timed skeleton;
the coarse signature theorem then supplies complete left-scanner
compatibility coordinatewise.
-/

namespace Erdos1165.AsymmetricCoarseCompletionSourceGeometry

open AnnularBoundaryExcursionKernel AnnularProfileClocks AppendixPair
open AsymmetricCoarseScanSignature
open AsymmetricBufferedProfileSplice BufferedSuccessfulProfile
open AsymmetricPostSeparationReturnSignature TerminalSpliceProfileGeometry
open AsymmetricCoarseSplitCompletion AsymmetricCoarseSplitCompletionSource
open AsymmetricExtractedReturnClockRecovery
open AsymmetricReturnPrefixRecovery
open AsymmetricSplitCompletionSource
open AsymmetricSplitCompletionPreservation AsymmetricSplitLevelSplice
open MarkedBridgeFactorization Proposition13Assembly
open PlanarPotential
open TerminalProfileClockEquivalence TerminalSkeletonInvariance
open TerminalGlobalExitSplice TerminalSkeletonWords ThickPoint
open TerminalRetainedHitSplice TerminalVisitSpliceInvariance

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The compressed extracted skeleton supplies endpoint geometry for any two
coarse-compatible return tuples. -/
theorem extracted_profile_eq_of_coarseReturnCodes_of_separation_le
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 2 ≤ n) (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n)
    (data : CoarseSplitCompletionData start n k)
    (t : TimedTerminalSkeleton data.returnCount) (ht : t.WellFormed)
    (hskeleton : data.skeleton = compressTimedSkeleton omega t)
    (hentrance : ∀ j, t.entrancePoint j = trajectory omega (t.entrance j))
    (hexit : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j) :
    ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 3) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (left j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (left j).1.1.2)) x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (right j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (right j).1.1.2)) x scale := by
  let leftCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(left j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (left j).1.2⟩
  let rightCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(right j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (right j).1.2⟩
  let geometry :=
    extracted_endpointGeometry_between_boundaryExitWordCodes
      omega t ht (profileInnerBoundary n k y) leftCodes rightCodes
  have hstart (j : Fin data.returnCount) :
      trajectory omega (t.entrance j) ∈ disc y (scaleRadius n k) := by
    have hs := hstarts j
    rw [hskeleton] at hs
    simpa only [compressTimedSkeleton_entrancePoint, hentrance] using hs
  have hdisc : disc y (scaleRadius n k) ⊆
      disc y (scaleRadius n (separationLevel n x y)) := by
    intro z hz
    exact hz.trans (scaleRadius_antitone_of_le hseparation hlevel)
  have hleft : ∀ j q, q ≤ (List.ofFn (leftCodes j).1.2).length →
      wordWalk (geometry.wordStart j) (List.ofFn (leftCodes j).1.2) q ∈
        disc y (scaleRadius n (separationLevel n x y)) := by
    intro j q hq
    rw [extracted_endpointGeometry_between_wordStart]
    apply hdisc
    exact wordWalk_mem_of_wordWithin
      (boundaryExitWordCode_wordWithin_and_endpoint
        (hstart j) (leftCodes j)).1 q hq
  have hright : ∀ j q, q ≤ (List.ofFn (rightCodes j).1.2).length →
      wordWalk (geometry.wordStart j) (List.ofFn (rightCodes j).1.2) q ∈
        disc y (scaleRadius n (separationLevel n x y)) := by
    intro j q hq
    rw [extracted_endpointGeometry_between_wordStart]
    apply hdisc
    exact wordWalk_mem_of_wordWithin
      (boundaryExitWordCode_wordWithin_and_endpoint
        (hstart j) (rightCodes j)).1 q hq
  have hword :=
    excursionProfile_alternatingConcat_eq_outside_three_coordinate_buffer_all
      hn (show separationLevel n x y = separationLevel n x y by rfl)
      (hseparation.trans hlevel) geometry hleft hright
  let leftWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (left j).1.1.2
  let rightWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (right j).1.1.2
  intro scale hretained
  have hword' :
      excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, leftWords))) n
          (assembledTerminalHorizon data.skeleton leftWords) x scale =
        excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, rightWords))) n
          (assembledTerminalHorizon data.skeleton rightWords) x scale := by
    simpa only [geometry, leftWords, rightWords, leftCodes, rightCodes,
      reconstructTerminalPacket, assembledTerminalHorizon_eq_alternatingConcat_length,
      hskeleton, compressTimedSkeleton] using hword scale hretained
  exact congrFun (assembledTerminalPath_excursionProfile_eq_wordWalk
    (n := n) (z := x) data.skeleton leftWords) scale |>.trans
      (hword'.trans
        (congrFun (assembledTerminalPath_excursionProfile_eq_wordWalk
          (n := n) (z := x) data.skeleton rightWords) scale).symm)

/-- With three genuinely separated scales, the sharper two-coordinate
buffer also retains the first excursion coordinate.  This is the endpoint
geometry needed at separation level three. -/
theorem extracted_profile_eq_of_coarseReturnCodes_of_separation_le_twoBuffer
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 2 ≤ n) (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n) (hthree : 3 ≤ separationLevel n x y)
    (data : CoarseSplitCompletionData start n k)
    (t : TimedTerminalSkeleton data.returnCount) (ht : t.WellFormed)
    (hskeleton : data.skeleton = compressTimedSkeleton omega t)
    (hentrance : ∀ j, t.entrancePoint j = trajectory omega (t.entrance j))
    (hexit : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j) :
    ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 2) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (left j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (left j).1.1.2)) x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (right j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (right j).1.1.2)) x scale := by
  let leftCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(left j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (left j).1.2⟩
  let rightCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(right j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (right j).1.2⟩
  let geometry :=
    extracted_endpointGeometry_between_boundaryExitWordCodes
      omega t ht (profileInnerBoundary n k y) leftCodes rightCodes
  have hstart (j : Fin data.returnCount) :
      trajectory omega (t.entrance j) ∈ disc y (scaleRadius n k) := by
    have hs := hstarts j
    rw [hskeleton] at hs
    simpa only [compressTimedSkeleton_entrancePoint, hentrance] using hs
  have hdisc : disc y (scaleRadius n k) ⊆
      disc y (scaleRadius n (separationLevel n x y)) := by
    intro z hz
    exact hz.trans (scaleRadius_antitone_of_le hseparation hlevel)
  have hleft : ∀ j q, q ≤ (List.ofFn (leftCodes j).1.2).length →
      wordWalk (geometry.wordStart j) (List.ofFn (leftCodes j).1.2) q ∈
        disc y (scaleRadius n (separationLevel n x y)) := by
    intro j q hq
    rw [extracted_endpointGeometry_between_wordStart]
    apply hdisc
    exact wordWalk_mem_of_wordWithin
      (boundaryExitWordCode_wordWithin_and_endpoint
        (hstart j) (leftCodes j)).1 q hq
  have hright : ∀ j q, q ≤ (List.ofFn (rightCodes j).1.2).length →
      wordWalk (geometry.wordStart j) (List.ofFn (rightCodes j).1.2) q ∈
        disc y (scaleRadius n (separationLevel n x y)) := by
    intro j q hq
    rw [extracted_endpointGeometry_between_wordStart]
    apply hdisc
    exact wordWalk_mem_of_wordWithin
      (boundaryExitWordCode_wordWithin_and_endpoint
        (hstart j) (rightCodes j)).1 q hq
  have hword :=
    excursionProfile_alternatingConcat_eq_outside_two_coordinate_buffer
      hn (show separationLevel n x y = separationLevel n x y by rfl)
      (hseparation.trans hlevel) hthree geometry hleft hright
  let leftWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (left j).1.1.2
  let rightWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (right j).1.1.2
  intro scale hretained
  have hword' :
      excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, leftWords))) n
          (assembledTerminalHorizon data.skeleton leftWords) x scale =
        excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, rightWords))) n
          (assembledTerminalHorizon data.skeleton rightWords) x scale := by
    simpa only [geometry, leftWords, rightWords, leftCodes, rightCodes,
      reconstructTerminalPacket, assembledTerminalHorizon_eq_alternatingConcat_length,
      hskeleton, compressTimedSkeleton] using hword scale hretained
  exact congrFun (assembledTerminalPath_excursionProfile_eq_wordWalk
    (n := n) (z := x) data.skeleton leftWords) scale |>.trans
      (hword'.trans
        (congrFun (assembledTerminalPath_excursionProfile_eq_wordWalk
          (n := n) (z := x) data.skeleton rightWords) scale).symm)

/-- Equality-level wrapper for an extracted skeleton at the original split. -/
theorem extracted_profile_eq_of_coarseReturnCodes
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 2 ≤ n) (hseparation : k = separationLevel n x y)
    (hlevel : k ≤ n)
    (data : CoarseSplitCompletionData start n k)
    (t : TimedTerminalSkeleton data.returnCount) (ht : t.WellFormed)
    (hskeleton : data.skeleton = compressTimedSkeleton omega t)
    (hentrance : ∀ j, t.entrancePoint j = trajectory omega (t.entrance j))
    (hexit : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j) :
    ∀ scale : Fin (n + 2), RetainedCoordinate (k - 3) (k + 1) scale.1 →
      excursionProfile
          (trajectory (assembledTerminalPath data.skeleton
            (fun j ↦ List.ofFn (left j).1.1.2))) n
          (assembledTerminalHorizon data.skeleton
            (fun j ↦ List.ofFn (left j).1.1.2)) x scale =
        excursionProfile
          (trajectory (assembledTerminalPath data.skeleton
            (fun j ↦ List.ofFn (right j).1.1.2))) n
          (assembledTerminalHorizon data.skeleton
            (fun j ↦ List.ofFn (right j).1.1.2)) x scale := by
  subst k
  apply extracted_profile_eq_of_coarseReturnCodes_of_separation_le
    hn (by omega) (by omega) data t ht hskeleton hentrance hexit hstarts
    left right

/-- A single retained scanner signature preserves the completed excursion
count at the split clock. -/
theorem extracted_completedExcursionCount_eq_of_coarseReturnCodes
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (data : CoarseSplitCompletionData start n k)
    (t : TimedTerminalSkeleton data.returnCount) (ht : t.WellFormed)
    (hskeleton : data.skeleton = compressTimedSkeleton omega t)
    (hentrance : ∀ j, t.entrancePoint j = trajectory omega (t.entrance j))
    (hexit : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hdisjoint : Disjoint (profileOuterBoundary n (k + 1) y)
      (profileInnerBoundary n (k + 1) y))
    (hstarts : ∀ j : Fin data.returnCount,
      trajectory omega (t.entrance j) ∈
        profileInnerBoundary n (k + 1) y)
    (hpiecesNe : ∀ j : Fin data.returnCount,
      complementaryPieces data.returnCount omega 0 t.horizon
        t.entrance t.exit j.castSucc ≠ [])
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j) :
    let leftWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (left j).1.1.2
    let rightWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (right j).1.1.2
    completedExcursionCount
        (trajectory (assembledTerminalPath data.skeleton leftWords))
        (profileOuterBoundary n (k + 1) y)
        (profileInnerBoundary n (k + 1) y)
        (assembledTerminalHorizon data.skeleton leftWords) =
      completedExcursionCount
        (trajectory (assembledTerminalPath data.skeleton rightWords))
        (profileOuterBoundary n (k + 1) y)
        (profileInnerBoundary n (k + 1) y)
        (assembledTerminalHorizon data.skeleton rightWords) := by
  dsimp only
  let leftWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (left j).1.1.2
  let rightWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (right j).1.1.2
  let leftCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(left j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (left j).1.2⟩
  let rightCodes : ∀ j : Fin data.returnCount,
      BoundaryExitWordCode (profileInnerBoundary n k y)
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(right j).1, by
      rw [← hentrance j, ← hexit j]
      have hstart : data.skeleton.2.1 j = t.entrancePoint j := by
        rw [hskeleton]
        rfl
      have hstop : data.skeleton.2.2 j = t.exitPoint j := by
        rw [hskeleton]
        rfl
      rw [← hstart, ← hstop]
      exact (right j).1.2⟩
  let geometry :=
    extracted_endpointGeometry_between_boundaryExitWordCodes
      omega t ht (profileInnerBoundary n k y) leftCodes rightCodes
  have houterEq : profileOuterBoundary n (k + 1) y =
      profileInnerBoundary n k y := by
    simp only [profileOuterBoundary, profileInnerBoundary,
      Nat.add_sub_cancel]
  have hscanRaw :=
    scanWordFrom_alternatingConcat_eq_of_endpointGeometry_seekingOuter
    data.returnCount
    (profileOuterBoundary n (k + 1) y)
    (profileInnerBoundary n (k + 1) y)
    (complementaryPieces data.returnCount omega 0 t.horizon
      t.entrance t.exit)
    (fun j ↦ List.ofFn (leftCodes j).1.2)
    (fun j ↦ List.ofFn (rightCodes j).1.2) (0, 0)
    (visitBoundary (profileOuterBoundary n (k + 1) y)
      (profileInnerBoundary n (k + 1) y)
      TerminalBoundaryScan.initialState (0, 0)) geometry
    (by
      intro j state
      apply scanWordFrom_seekingOuter_of_nonempty_endpoint_inner
        (profileOuterBoundary n (k + 1) y)
        (profileInnerBoundary n (k + 1) y)
        (geometry.pieceStart j.castSucc) state
        (complementaryPieces data.returnCount omega 0 t.horizon
          t.entrance t.exit j.castSucc) (hpiecesNe j)
      · rw [wordWalk_length, geometry.retainedEndpoint]
        intro hout
        exact Set.disjoint_left.1 hdisjoint hout (hstarts j)
      · rw [wordWalk_length, geometry.retainedEndpoint]
        exact hstarts j)
    (by
      intro j completed
      rw [extracted_endpointGeometry_between_wordStart]
      apply scanWordFrom_eq_of_endpointMatched_first_outer_words
      · intro hempty
        have hduration : (leftCodes j).1.1 = 0 := by
          have hlen := congrArg List.length hempty
          simpa only [List.length_ofFn, List.length_nil] using hlen
        have hout : trajectory omega (t.entrance j) ∈
            profileOuterBoundary n (k + 1) y := by
          rw [houterEq]
          have hend := (leftCodes j).2.1.1
          rw [hduration] at hend
          simpa using hend
        exact Set.disjoint_left.1 hdisjoint hout (hstarts j)
      · intro hempty
        have hduration : (rightCodes j).1.1 = 0 := by
          have hlen := congrArg List.length hempty
          simpa only [List.length_ofFn, List.length_nil] using hlen
        have hout : trajectory omega (t.entrance j) ∈
            profileOuterBoundary n (k + 1) y := by
          rw [houterEq]
          have hend := (rightCodes j).2.1.1
          rw [hduration] at hend
          simpa using hend
        exact Set.disjoint_left.1 hdisjoint hout (hstarts j)
      · intro q hqpos hq
        rw [houterEq]
        rw [wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ hq.le]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn] using
          (leftCodes j).2.1.2 q (by simpa using hq)
      · intro q hqpos hq
        rw [houterEq]
        rw [wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ hq.le]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn] using
          (rightCodes j).2.1.2 q (by simpa using hq)
      · rw [houterEq,
          wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ le_rfl]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn,
          List.length_ofFn] using (leftCodes j).2.1.1
      · rw [houterEq,
          wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ le_rfl]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn,
          List.length_ofFn] using (rightCodes j).2.1.1
      · rw [wordWalk_length, wordWalk_length]
        exact (boundaryExitWordCode_wordEndpoint (leftCodes j)).trans
          (boundaryExitWordCode_wordEndpoint (rightCodes j)).symm)
  have hscan :
      scanWordFrom (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) (0, 0)
          (visitBoundary (profileOuterBoundary n (k + 1) y)
            (profileInnerBoundary n (k + 1) y)
            TerminalBoundaryScan.initialState (0, 0))
          (reconstructTerminalPacket (data.skeleton, leftWords)) =
        scanWordFrom (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y) (0, 0)
          (visitBoundary (profileOuterBoundary n (k + 1) y)
            (profileInnerBoundary n (k + 1) y)
            TerminalBoundaryScan.initialState (0, 0))
          (reconstructTerminalPacket (data.skeleton, rightWords)) := by
    simpa only [reconstructTerminalPacket, leftWords, rightWords, leftCodes,
      rightCodes, hskeleton, compressTimedSkeleton] using hscanRaw
  have hwordCount := completedExcursionCount_wordWalk_eq_of_scanWordFrom_eq
    hdisjoint hscan
  have hleft :
      completedExcursionCount
          (trajectory (assembledTerminalPath data.skeleton leftWords))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y)
          (assembledTerminalHorizon data.skeleton leftWords) =
        completedExcursionCount
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, leftWords)))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y)
          (assembledTerminalHorizon data.skeleton leftWords) := by
    apply Proposition13Measurability.completedExcursionCount_congr_prefix
    intro r hr
    exact (wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      data.skeleton leftWords hr).symm
  have hright :
      completedExcursionCount
          (trajectory (assembledTerminalPath data.skeleton rightWords))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y)
          (assembledTerminalHorizon data.skeleton rightWords) =
        completedExcursionCount
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, rightWords)))
          (profileOuterBoundary n (k + 1) y)
          (profileInnerBoundary n (k + 1) y)
          (assembledTerminalHorizon data.skeleton rightWords) := by
    apply Proposition13Measurability.completedExcursionCount_congr_prefix
    intro r hr
    exact (wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      data.skeleton rightWords hr).symm
  exact hleft.trans (hwordCount.trans hright.symm)

/-- Source specialization: a coarse candidate has the same full left
profile as the canonical coarse reference tuple. -/
theorem sourceCoarseReferenceCandidate_profile_eq_of_separation_le
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : separationLevel n x y ≤ k) (hlevel : k ≤ n)
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :
    let data := sourceCoarseSplitCompletionData start n k hk x y source
    ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 3) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn
                (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                  hk hy hexit j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn
                (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                  hk hy hexit j).1.1.2)) x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (candidate j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (candidate j).1.1.2)) x scale := by
  dsimp only
  let horizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  have hcomplete : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner horizon (j + 1) ≤
        horizon := sourceReturnComplete (Nat.one_le_of_lt hn) hk hy hexit
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  apply extracted_profile_eq_of_coarseReturnCodes_of_separation_le
    hn hseparation hlevel
    (sourceCoarseSplitCompletionData start n k hk x y source) t ht
  · rfl
  · intro j
    exact extractTimedReturnSkeleton_entrancePoint_apply
      sigma middle inner horizon q j
  · intro j
    exact extractTimedReturnSkeleton_exitPoint_apply
      sigma middle inner horizon q j
  · exact sourceCoarseReturnStart_mem_profileDisc
      (x := x) (y := y) (source := source)
        (Nat.one_le_of_lt hn) hk hy hexit

/-- Source specialization of the sharper two-coordinate buffer. -/
theorem sourceCoarseReferenceCandidate_profile_eq_of_separation_le_twoBuffer
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : separationLevel n x y ≤ k) (hlevel : k ≤ n)
    (hthree : 3 ≤ separationLevel n x y)
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :
    let data := sourceCoarseSplitCompletionData start n k hk x y source
    ∀ scale : Fin (n + 2),
      RetainedCoordinate
          (separationLevel n x y - 2) (separationLevel n x y + 1) scale.1 →
        excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn
                (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                  hk hy hexit j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn
                (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                  hk hy hexit j).1.1.2)) x scale =
          excursionProfile
            (trajectory (assembledTerminalPath data.skeleton
              (fun j ↦ List.ofFn (candidate j).1.1.2))) n
            (assembledTerminalHorizon data.skeleton
              (fun j ↦ List.ofFn (candidate j).1.1.2)) x scale := by
  dsimp only
  let horizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  have hcomplete : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner horizon (j + 1) ≤
        horizon := sourceReturnComplete (Nat.one_le_of_lt hn) hk hy hexit
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  apply extracted_profile_eq_of_coarseReturnCodes_of_separation_le_twoBuffer
    hn hseparation hlevel hthree
    (sourceCoarseSplitCompletionData start n k hk x y source) t ht
  · rfl
  · intro j
    exact extractTimedReturnSkeleton_entrancePoint_apply
      sigma middle inner horizon q j
  · intro j
    exact extractTimedReturnSkeleton_exitPoint_apply
      sigma middle inner horizon q j
  · exact sourceCoarseReturnStart_mem_profileDisc
      (x := x) (y := y) (source := source)
        (Nat.one_le_of_lt hn) hk hy hexit

/-- Equality-level wrapper for the canonical source reference tuple. -/
theorem sourceCoarseReferenceCandidate_profile_eq
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (hseparation : k = separationLevel n x y) (hlevel : k ≤ n)
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :
    let data := sourceCoarseSplitCompletionData start n k hk x y source
    ∀ scale : Fin (n + 2), RetainedCoordinate (k - 3) (k + 1) scale.1 →
      excursionProfile
          (trajectory (assembledTerminalPath data.skeleton
            (fun j ↦ List.ofFn
              (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                hk hy hexit j).1.1.2))) n
          (assembledTerminalHorizon data.skeleton
            (fun j ↦ List.ofFn
              (sourceCoarseReferenceCandidate (Nat.one_le_of_lt hn)
                hk hy hexit j).1.1.2)) x scale =
        excursionProfile
          (trajectory (assembledTerminalPath data.skeleton
            (fun j ↦ List.ofFn (candidate j).1.1.2))) n
          (assembledTerminalHorizon data.skeleton
            (fun j ↦ List.ofFn (candidate j).1.1.2)) x scale := by
  subst k
  apply sourceCoarseReferenceCandidate_profile_eq_of_separation_le
    hn hk hy hexit (by omega) (by omega) candidate

/-- The retained split-clock signature also preserves the completed return
count used by coarse re-extraction. -/
theorem sourceCoarseReferenceCandidate_completedCount_eq
    {start n k : ℕ} {x y : Point} {source : StepPath}
    (hn : 2 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory (shiftSteps start source)) n
      (stoppedOuterExitHorizon start n source))
    (candidate : (j : Fin
      (sourceCoarseSplitCompletionData start n k hk x y source).returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y)
        (sourceCoarseSplitCompletionData start n k hk x y source) j) :
    let data := sourceCoarseSplitCompletionData start n k hk x y source
    let reference := sourceCoarseReferenceCandidate
      (x := x) (y := y) (Nat.one_le_of_lt hn) hk hy hexit
    let referenceWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (reference j).1.1.2
    let candidateWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (candidate j).1.1.2
    completedExcursionCount
        (trajectory (assembledTerminalPath data.skeleton referenceWords))
        (profileOuterBoundary n (k + 1) y)
        (profileInnerBoundary n (k + 1) y)
        (assembledTerminalHorizon data.skeleton referenceWords) =
      completedExcursionCount
        (trajectory (assembledTerminalPath data.skeleton candidateWords))
        (profileOuterBoundary n (k + 1) y)
        (profileInnerBoundary n (k + 1) y)
        (assembledTerminalHorizon data.skeleton candidateWords) := by
  dsimp only
  let horizon := stoppedOuterExitHorizon start n source
  let sigma := shiftSteps start source
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  have hcomplete : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner horizon (j + 1) ≤
        horizon := sourceReturnComplete (Nat.one_le_of_lt hn) hk hy hexit
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have hsplitDisjoint : Disjoint middle inner := by
    let level : Fin (n + 2) := ⟨k + 1, by omega⟩
    simpa only [middle, inner, level, profileOuterBoundary,
      profileInnerBoundary, Nat.add_sub_cancel] using
      (profileBoundaries_disjoint hn y level (by
        simpa only [level] using Nat.succ_ne_zero k))
  have hstartsT : ∀ j : Fin q, trajectory sigma (t.entrance j) ∈ inner := by
    intro j
    have hj := extractedReturnEntrancePoint_mem_inner hcomplete j
    simpa only [t, extractTimedReturnSkeleton, returnEntranceTime,
      trajectoryFrom_zero_eq_trajectory] using hj
  have hstrict : ∀ j : Fin q,
      excursionStart (trajectory sigma) middle inner horizon j <
        excursionFinish (trajectory sigma) middle inner horizon j := by
    intro j
    have hfinish : excursionFinish (trajectory sigma) middle inner horizon j ≤
        horizon :=
      (TerminalExcursionPathwise.excursionFinish_le_next_start
        (trajectory sigma) middle inner horizon j).trans (hcomplete j)
    have hout := excursionStart_mem_outer_of_finish_le
      (trajectory sigma) middle inner horizon j hfinish
    have hin := excursionFinish_mem_inner_of_le
      (trajectory sigma) middle inner horizon j hfinish
    apply lt_of_le_of_ne
      (TerminalExcursionPathwise.excursionStart_le_finish
        (trajectory sigma) middle inner horizon j)
    intro heq
    exact Set.disjoint_left.1 hsplitDisjoint hout (heq ▸ hin)
  have hpieces : ∀ j : Fin q,
      complementaryPieces q sigma 0 t.horizon t.entrance t.exit
        j.castSucc ≠ [] := by
    intro j
    have hqpos : 0 < q := Nat.zero_lt_of_lt j.isLt
    apply List.ne_nil_of_length_pos
    by_cases hjzero : (j : ℕ) = 0
    · have hjEq : j = ⟨0, hqpos⟩ := Fin.ext hjzero
      subst j
      have hcast : (⟨0, hqpos⟩ : Fin q).castSucc =
          (0 : Fin (q + 1)) := Fin.ext rfl
      rw [hcast, complementaryPieces_zero_of_pos hqpos sigma 0 t.horizon
        t.entrance t.exit, incrementSlice_length, Nat.sub_zero]
      have hs := hstrict (⟨0, hqpos⟩ : Fin q)
      dsimp only [t, extractTimedReturnSkeleton, returnEntranceTime]
      rw [trajectoryFrom_zero_eq_trajectory]
      exact (Nat.zero_le _).trans_lt (by simpa using hs)
    · let prev : Fin q := ⟨(j : ℕ) - 1, by omega⟩
      have hprevNext : (prev : ℕ) + 1 < q := by
        dsimp only [prev]
        omega
      have hnext : (⟨(prev : ℕ) + 1, hprevNext⟩ : Fin q) = j := by
        apply Fin.ext
        dsimp only [prev]
        omega
      have hindex : prev.succ = j.castSucc := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc]
        dsimp only [prev]
        omega
      rw [← hindex, complementaryPieces_succ sigma 0 t.horizon
        t.entrance t.exit prev hprevNext, incrementSlice_length]
      have hs := hstrict j
      dsimp only [t, extractTimedReturnSkeleton, returnEntranceTime,
        returnExitTime]
      rw [trajectoryFrom_zero_eq_trajectory]
      apply Nat.sub_pos_of_lt
      have hval : (j : ℕ) = (prev : ℕ) + 1 := by
        have := congrArg Fin.val hnext
        simpa only [Fin.val_mk] using this.symm
      simpa only [hval] using hs
  apply extracted_completedExcursionCount_eq_of_coarseReturnCodes
    (sourceCoarseSplitCompletionData start n k hk x y source) t ht
  · rfl
  · intro j
    exact extractTimedReturnSkeleton_entrancePoint_apply
      sigma middle inner horizon q j
  · intro j
    exact extractTimedReturnSkeleton_exitPoint_apply
      sigma middle inner horizon q j
  · change Disjoint middle inner
    exact hsplitDisjoint
  · change ∀ j : Fin q, trajectory sigma (t.entrance j) ∈ inner
    exact hstartsT
  · change ∀ j : Fin q,
      complementaryPieces q sigma 0 t.horizon t.entrance t.exit
        j.castSucc ≠ []
    exact hpieces

end

end Erdos1165.AsymmetricCoarseCompletionSourceGeometry
