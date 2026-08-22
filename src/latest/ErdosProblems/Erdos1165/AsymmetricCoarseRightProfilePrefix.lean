/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseRecursiveSourceCode
import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation

/-!
# The right profile prefix retained by a coarse asymmetric code

The erased right-hand returns are first hits of the level-`k` boundary from
the level-`k+1` boundary.  Consequently they are invisible to every coarser
right-hand profile scanner.  The one remaining scanner, at level `k+1`, is
recorded explicitly in the coarse signature.  Thus every successful tail
over one coarse code has one common profile prefix through `k+1`.
-/

open Set

namespace Erdos1165.AsymmetricCoarseRightProfilePrefix

open AnnularBoundaryExcursionKernel AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularProfileLiteralAtoms
open AnnularRecursiveProfileSourceSegment
open AppendixFirstMoment
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseScanSignature AsymmetricCoarseSplitCompletion
open AsymmetricCoarseSplitCompletionSource
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricExtractedReturnClockRecovery
open AsymmetricPostSeparationReturnSignature
open AsymmetricReturnPrefixRecovery AsymmetricSplitCompletionSource
open AsymmetricSplitCompletionRecovered AsymmetricSplitLevelSplice
open MarkedBridgeFactorization ProfileListExponent ProfileWeightUpper
open Proposition13Assembly RealDiscFinite
open TerminalGlobalExitSplice TerminalProfileBoundarySeparation
open TerminalProfileClockEquivalence TerminalSkeletonInvariance
open TerminalSkeletonWords TerminalSpliceProfileGeometry
open TerminalVisitSpliceInvariance ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A first return from the level-`k+1` boundary to the level-`k` boundary
has the same action on every profile scanner at or below level `k`, once its
endpoint is fixed. -/
theorem scanWordFrom_eq_of_nestedBoundaryExitWordCodes
    {n k l : ℕ} {y start endpoint : Point}
    (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1) (hk : k + 1 ≤ n)
    (hlpos : 0 < l) (hl : l ≤ k)
    (hstartInner : start ∈ profileInnerBoundary n (k + 1) y)
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n k y) start endpoint)
    (state : BoundaryScanState) :
    scanWordFrom (profileOuterBoundary n l y)
        (profileInnerBoundary n l y) start state (List.ofFn left.1.2) =
      scanWordFrom (profileOuterBoundary n l y)
        (profileInnerBoundary n l y) start state
        (List.ofFn right.1.2) := by
  let D := disc y (scaleRadius n k)
  have hstart : start ∈ D := by
    exact hstartInner.1.trans
      (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk)
  have hleftWithin : WordWithin D start (List.ofFn left.1.2) := by
    simpa only [D, profileInnerBoundary, discBoundary] using
      (boundaryExitWordCode_wordWithin_and_endpoint hstart left).1
  have hrightWithin : WordWithin D start (List.ofFn right.1.2) := by
    simpa only [D, profileInnerBoundary, discBoundary] using
      (boundaryExitWordCode_wordWithin_and_endpoint hstart right).1
  have hleftEnd : wordWalk start (List.ofFn left.1.2)
      (List.ofFn left.1.2).length = endpoint := by
    rw [wordWalk_length]
    exact (boundaryExitWordCode_wordWithin_and_endpoint hstart left).2
  have hrightEnd : wordWalk start (List.ofFn right.1.2)
      (List.ofFn right.1.2).length = endpoint := by
    rw [wordWalk_length]
    exact (boundaryExitWordCode_wordWithin_and_endpoint hstart right).2
  have hend : wordWalk start (List.ofFn left.1.2)
        (List.ofFn left.1.2).length =
      wordWalk start (List.ofFn right.1.2)
        (List.ofFn right.1.2).length := hleftEnd.trans hrightEnd.symm
  by_cases hlk : l = k
  · subst l
    let level : Fin (n + 2) := ⟨k + 1, by omega⟩
    have hdisjoint : Disjoint (profileInnerBoundary n k y)
        (profileInnerBoundary n (k + 1) y) := by
      simpa only [level, profileOuterBoundary, profileInnerBoundary,
        Nat.add_sub_cancel] using
        (profileBoundaries_disjoint hn y level (by
          simpa only [level] using Nat.succ_ne_zero k))
    have firstHit (bridge : BoundaryExitWordCode
        (profileInnerBoundary n k y) start endpoint) :
        WordFirstHitsAtEnd (profileInnerBoundary n k y) start
          (List.ofFn bridge.1.2) := by
      apply WordFirstHitsAtEnd.of_isFirstHit
      · rw [wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ le_rfl]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn,
          List.length_ofFn] using
          bridge.2.1.1
      · intro q hq
        rw [wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ hq.le]
        simpa only [extendStoppedWord_stoppedWordOfList_ofFn] using
          bridge.2.1.2 q (by simpa using hq)
    have hleftFirst := firstHit left
    have hrightFirst := firstHit right
    have nonempty (bridge : BoundaryExitWordCode
        (profileInnerBoundary n k y) start endpoint)
        (hfirst : WordFirstHitsAtEnd (profileInnerBoundary n k y) start
          (List.ofFn bridge.1.2)) : List.ofFn bridge.1.2 ≠ [] := by
      intro hempty
      have houter : start ∈ profileInnerBoundary n k y := by
        simpa only [hempty, wordEndpoint_nil] using hfirst.endpoint_mem
      exact Set.disjoint_left.mp hdisjoint houter hstartInner
    have hsepOuter : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) :=
      scaleRadius_add_one_le_previous hn (by omega) (by omega)
    have avoidOuter (word : List Direction)
        (hwithin : WordWithin D start word) :
        ∀ q ≤ word.length,
          wordWalk start word q ∉ profileOuterBoundary n k y := by
      intro q hq
      have hmem := wordWalk_mem_of_wordWithin hwithin q hq
      exact not_mem_discBoundary_of_mem_disc_of_add_one_le hmem hsepOuter
    apply scanWordFrom_eq_of_endpointMatched_first_inner_words
    · exact nonempty left hleftFirst
    · exact nonempty right hrightFirst
    · intro q hqpos hq
      exact ⟨avoidOuter _ hleftWithin q hq.le,
        hleftFirst.before_endpoint_not_mem q hq⟩
    · intro q hqpos hq
      exact ⟨avoidOuter _ hrightWithin q hq.le,
        hrightFirst.before_endpoint_not_mem q hq⟩
    · exact avoidOuter _ hleftWithin _ le_rfl
    · exact avoidOuter _ hrightWithin _ le_rfl
    · rw [wordWalk_length]
      exact hleftFirst.endpoint_mem
    · rw [wordWalk_length]
      exact hrightFirst.endpoint_mem
    · exact hend
  · have hlklt : l < k := by omega
    have hkpos : 0 < k := by omega
    have hadj : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) :=
      scaleRadius_add_one_le_previous hn hkpos (by omega)
    have hsepInner : scaleRadius n k + 1 ≤ scaleRadius n l :=
      hadj.trans (scaleRadius_antitone_of_le (by omega) (by omega))
    have hsepOuter : scaleRadius n k + 1 ≤ scaleRadius n (l - 1) :=
      hadj.trans (scaleRadius_antitone_of_le (by omega) (by omega))
    have avoids (word : List Direction)
        (hwithin : WordWithin D start word) :
        ∀ q, 0 < q → q ≤ word.length →
          wordWalk start word q ∉ profileOuterBoundary n l y ∧
            wordWalk start word q ∉ profileInnerBoundary n l y := by
      intro q _hqpos hq
      have hmem := wordWalk_mem_of_wordWithin hwithin q hq
      exact ⟨not_mem_discBoundary_of_mem_disc_of_add_one_le hmem hsepOuter,
        not_mem_discBoundary_of_mem_disc_of_add_one_le hmem hsepInner⟩
    exact scanWordFrom_eq_of_endpointMatched_avoiding_words
      _ _ start state _ _ (avoids _ hleftWithin) (avoids _ hrightWithin) hend

/-- On an extracted coarse skeleton, two compatible bridge tuples have the
same completed right-hand excursion count at every retained prefix scale. -/
theorem extracted_completedCount_eq_of_coarseReturnCodes_of_le
    {start n k l : ℕ} {x y : Point} {omega : StepPath}
    (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1) (hk : k + 1 ≤ n)
    (hlTwo : 2 ≤ l) (hl : l ≤ k)
    (data : CoarseSplitCompletionData start n k)
    (t : TimedTerminalSkeleton data.returnCount) (ht : t.WellFormed)
    (hskeleton : data.skeleton = compressTimedSkeleton omega t)
    (hentrance : ∀ j, t.entrancePoint j = trajectory omega (t.entrance j))
    (hexit : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ profileInnerBoundary n (k + 1) y)
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j) :
    let leftWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (left j).1.1.2
    let rightWords : TerminalSegmentWords data.returnCount :=
      fun j ↦ List.ofFn (right j).1.1.2
    profileCompletedCount
        (trajectory (assembledTerminalPath data.skeleton leftWords))
        n (assembledTerminalHorizon data.skeleton leftWords) y l =
      profileCompletedCount
        (trajectory (assembledTerminalPath data.skeleton rightWords))
        n (assembledTerminalHorizon data.skeleton rightWords) y l := by
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
  have hscanRaw := scanWordFrom_alternatingConcat_eq_of_endpointGeometry
    data.returnCount
    (profileOuterBoundary n l y) (profileInnerBoundary n l y)
    (complementaryPieces data.returnCount omega 0 t.horizon
      t.entrance t.exit)
    (fun j ↦ List.ofFn (leftCodes j).1.2)
    (fun j ↦ List.ofFn (rightCodes j).1.2) (0, 0)
    (visitBoundary (profileOuterBoundary n l y)
      (profileInnerBoundary n l y)
      TerminalBoundaryScan.initialState (0, 0)) geometry (by
        intro j state
        rw [extracted_endpointGeometry_between_wordStart]
        have hstartInner : trajectory omega (t.entrance j) ∈
            profileInnerBoundary n (k + 1) y := by
          have hs := hstarts j
          rw [hskeleton] at hs
          simpa only [compressTimedSkeleton_entrancePoint, hentrance] using hs
        exact scanWordFrom_eq_of_nestedBoundaryExitWordCodes
          hn hkTwo hk (by omega) hl hstartInner
            (leftCodes j) (rightCodes j) state)
  have hscan :
      scanWordFrom (profileOuterBoundary n l y)
          (profileInnerBoundary n l y) (0, 0)
          (visitBoundary (profileOuterBoundary n l y)
            (profileInnerBoundary n l y)
            TerminalBoundaryScan.initialState (0, 0))
          (reconstructTerminalPacket (data.skeleton, leftWords)) =
        scanWordFrom (profileOuterBoundary n l y)
          (profileInnerBoundary n l y) (0, 0)
          (visitBoundary (profileOuterBoundary n l y)
            (profileInnerBoundary n l y)
            TerminalBoundaryScan.initialState (0, 0))
          (reconstructTerminalPacket (data.skeleton, rightWords)) := by
    simpa only [reconstructTerminalPacket, leftWords, rightWords, leftCodes,
      rightCodes, hskeleton, compressTimedSkeleton] using hscanRaw
  let level : Fin (n + 2) := ⟨l, by omega⟩
  have hdisjoint : Disjoint (profileOuterBoundary n l y)
      (profileInnerBoundary n l y) := by
    simpa only [level, profileOuterBoundary, profileInnerBoundary] using
      (profileBoundaries_disjoint hn y level (by
        simpa only [level] using (show l ≠ 0 by omega)))
  have hwordCount := completedExcursionCount_wordWalk_eq_of_scanWordFrom_eq
    hdisjoint hscan
  have hleft :
      profileCompletedCount
          (trajectory (assembledTerminalPath data.skeleton leftWords)) n
          (assembledTerminalHorizon data.skeleton leftWords) y l =
        completedExcursionCount
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, leftWords)))
          (profileOuterBoundary n l y) (profileInnerBoundary n l y)
          (assembledTerminalHorizon data.skeleton leftWords) := by
    unfold profileCompletedCount
    apply Proposition13Measurability.completedExcursionCount_congr_prefix
    intro r hr
    exact (wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      data.skeleton leftWords hr).symm
  have hright :
      profileCompletedCount
          (trajectory (assembledTerminalPath data.skeleton rightWords)) n
          (assembledTerminalHorizon data.skeleton rightWords) y l =
        completedExcursionCount
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, rightWords)))
          (profileOuterBoundary n l y) (profileInnerBoundary n l y)
          (assembledTerminalHorizon data.skeleton rightWords) := by
    unfold profileCompletedCount
    apply Proposition13Measurability.completedExcursionCount_congr_prefix
    intro r hr
    exact (wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
      data.skeleton rightWords hr).symm
  exact hleft.trans (hwordCount.trans hright.symm)

/-- The split-clock extractor on a successful assembled coarse tail is a
genuine timed skeleton with all selected return intervals complete. -/
theorem coarseSuccessfulTimedReturnSkeleton_wellFormed
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    let words : TerminalSegmentWords code.1.returnCount :=
      coarseTupleWords code tail.1
    let horizon := assembledTerminalHorizon code.1.skeleton words
    let assembled := assembledTerminalPath code.1.skeleton words
    let actualT := extractTimedReturnSkeleton assembled (0, 0)
      (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
      horizon code.1.returnCount
    actualT.WellFormed := by
  dsimp only
  let words : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code tail.1
  let horizon := assembledTerminalHorizon code.1.skeleton words
  let assembled := assembledTerminalPath code.1.skeleton words
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  have hfixed : FixedSuccessfulProfile n profileDelta
      (coarseSuccessfulProfile code tail)
      (excursionProfile (trajectory assembled) n horizon y) := by
    simpa only [coarseSuccessfulProfile, assembled, horizon, words] using
      fixedSuccessfulProfile_internalProfile tail.2.2
  have hprofile : profileCompletedCount (trajectory assembled) n horizon y
      (k + 1) = profileAtScale (coarseSuccessfulProfile code tail) (k + 1) :=
    profileCompletedCount_eq_profileAtScale hkTwo hk hfixed
  have hcount : boundaryExcursionCount middle inner (0, 0) assembled horizon =
      code.1.returnCount := by
    calc
      boundaryExcursionCount middle inner (0, 0) assembled horizon =
          profileCompletedCount (trajectory assembled) n horizon y
            (k + 1) := by
        simp only [boundaryExcursionCount, profileCompletedCount, middle,
          inner, profileOuterBoundary, profileInnerBoundary,
          Nat.add_sub_cancel, trajectoryFrom_zero_eq_trajectory]
      _ = profileAtScale (coarseSuccessfulProfile code tail) (k + 1) :=
        hprofile
      _ = code.1.returnCount :=
        (coarseSuccessfulReturnCount_eq_profileAtScale
          hkTwo code tail).symm
  have hcompleteAll := sourceReturnComplete
    (Nat.one_le_of_lt hn) hk tail.2.1
      (coarseSuccessfulAssembled_isOuterExitTime code tail)
  have hcomplete : ∀ j : Fin code.1.returnCount,
      excursionStart (trajectory assembled) middle inner horizon (j + 1) ≤
        horizon :=
    returnComplete_of_boundaryExcursionCount_eq hcount hcompleteAll
  apply extractTimedReturnSkeleton_wellFormed
  simpa only [middle, inner, trajectoryFrom_zero_eq_trajectory] using hcomplete

/-- The internal right-hand profile value at every scale through `k+1` is
independent of the successful tail chosen over a fixed coarse code. -/
theorem coarseSuccessfulProfileAtScale_eq_of_le
    {start n k l : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (left right : CoarseSuccessfulReturnTuple code)
    (hlTwo : 2 ≤ l) (hl : l ≤ k + 1) :
    profileAtScale (coarseSuccessfulProfile code left) l =
      profileAtScale (coarseSuccessfulProfile code right) l := by
  by_cases hlTop : l = k + 1
  · subst l
    exact (coarseSuccessfulReturnCount_eq_profileAtScale
      hkTwo code left).symm.trans
        (coarseSuccessfulReturnCount_eq_profileAtScale hkTwo code right)
  have hlk : l ≤ k := by omega
  let leftWords : TerminalSegmentWords code.1.returnCount :=
    coarseTupleWords code left.1
  let leftHorizon := assembledTerminalHorizon code.1.skeleton leftWords
  let leftAssembled := assembledTerminalPath code.1.skeleton leftWords
  let actualT := extractTimedReturnSkeleton leftAssembled (0, 0)
    (profileInnerBoundary n k y) (profileInnerBoundary n (k + 1) y)
    leftHorizon code.1.returnCount
  have ht : actualT.WellFormed := by
    simpa only [actualT, leftAssembled, leftHorizon, leftWords] using
      coarseSuccessfulTimedReturnSkeleton_wellFormed hn hkTwo code left
  have hskeleton : code.1.skeleton =
      compressTimedSkeleton leftAssembled actualT := by
    exact (coarseSuccessfulReturnData_recovered hn code left).1.symm
  have hstarts : ∀ j : Fin code.1.returnCount,
      code.1.skeleton.2.1 j ∈ profileInnerBoundary n (k + 1) y := by
    intro j
    let entrance := coarseSuccessfulRecursiveEntrance
      hn hkTwo hdelta code left j
    have hval : entrance.1 = code.1.skeleton.2.1 j :=
      coarseSuccessfulRecursiveEntrance_eq_skeleton
        hn hkTwo hdelta code left j
    rw [← hval]
    exact mem_discBoundaryFinset.mp entrance.2
  have hcount := extracted_completedCount_eq_of_coarseReturnCodes_of_le
    hn hkTwo hk hlTwo hlk code.1 actualT ht hskeleton
    (fun j ↦ by
      exact extractTimedReturnSkeleton_entrancePoint_apply
        leftAssembled (profileInnerBoundary n k y)
          (profileInnerBoundary n (k + 1) y)
          leftHorizon code.1.returnCount j)
    (fun j ↦ by
      exact extractTimedReturnSkeleton_exitPoint_apply
        leftAssembled (profileInnerBoundary n k y)
          (profileInnerBoundary n (k + 1) y)
          leftHorizon code.1.returnCount j)
    hstarts left.1 right.1
  have hfixedLeft : FixedSuccessfulProfile n profileDelta
      (coarseSuccessfulProfile code left)
      (excursionProfile
        (trajectory (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code left.1))) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code left.1)) y) := by
    exact fixedSuccessfulProfile_internalProfile left.2.2
  have hfixedRight : FixedSuccessfulProfile n profileDelta
      (coarseSuccessfulProfile code right)
      (excursionProfile
        (trajectory (assembledTerminalPath code.1.skeleton
          (coarseTupleWords code right.1))) n
        (assembledTerminalHorizon code.1.skeleton
          (coarseTupleWords code right.1)) y) := by
    exact fixedSuccessfulProfile_internalProfile right.2.2
  have hleft := profileCompletedCount_eq_profileAtScale
    hlTwo (hl.trans hk) hfixedLeft
  have hright := profileCompletedCount_eq_profileAtScale
    hlTwo (hl.trans hk) hfixedRight
  exact hleft.symm.trans (hcount.trans hright)

/-- Every successful tail over one retained coarse code has the same exact
right-hand profile prefix through the first free scale `k+1`. -/
theorem coarseSuccessfulProfilePrefix_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (left right : CoarseSuccessfulReturnTuple code) :
    profilePrefix hkTwo hk (coarseSuccessfulProfile code left) =
      profilePrefix hkTwo hk (coarseSuccessfulProfile code right) := by
  funext i
  let full : Fin (n - 1) := ⟨i.1, by have := i.2; omega⟩
  have hscaleTwo : 2 ≤ scaleIndex full := by simp [scaleIndex]
  have hscaleTop : scaleIndex full ≤ k + 1 := by
    have hkpos : 0 < k := by omega
    have hi : i.1 < k := by
      have := i.2
      omega
    dsimp only [scaleIndex, full]
    omega
  have h := coarseSuccessfulProfileAtScale_eq_of_le
    hn hkTwo hdelta code left right hscaleTwo hscaleTop
  change (coarseSuccessfulProfile code left) full =
    (coarseSuccessfulProfile code right) full
  rw [← profileAtScale_scaleIndex (coarseSuccessfulProfile code left) full,
    ← profileAtScale_scaleIndex (coarseSuccessfulProfile code right) full]
  exact h

/-- The exact right-hand prefix retained by a coarse code.  Empty coarse
fibers receive an arbitrary harmless default; every inhabited successful
fiber uses the prefix of one canonical tail. -/
def retainedYProfilePrefix
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) : Profile (k + 1) :=
  if h : Nonempty (CoarseSuccessfulReturnTuple code) then
    profilePrefix hkTwo hk
      (coarseSuccessfulProfile code (Classical.choice h))
  else default

/-- Every successful tail realizes the prefix canonically attached to its
coarse code. -/
theorem profilePrefix_coarseSuccessfulProfile_eq_retained
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    profilePrefix hkTwo hk (coarseSuccessfulProfile code tail) =
      retainedYProfilePrefix hn hkTwo hdelta code := by
  rw [retainedYProfilePrefix, dif_pos ⟨tail⟩]
  exact coarseSuccessfulProfilePrefix_eq
    hn hkTwo hdelta code tail (Classical.choice ⟨tail⟩)

end

end Erdos1165.AsymmetricCoarseRightProfilePrefix
