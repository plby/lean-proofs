/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricReturnPrefixRecovery
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionCode
import ErdosProblems.Erdos1165.SharedPrefixPairExtraction

/-!
# Actual stopped sources for the asymmetric split completion

The code is extracted from the full stopped pair path.  Only the `y`
inner-to-middle return words at the split are subsequently variable.  Their
finite `x` and `y` scanner signatures make the stopped return count and the
compressed complementary skeleton exactly re-extractable.
-/

open Set

namespace Erdos1165.AsymmetricSplitCompletionSource

open AnnularBoundaryExcursionKernel AnnularOffspringRenewal AnnularProfileClocks
open AsymmetricExtractedReturnClockRecovery AsymmetricExtractedReturnCompletion
open AsymmetricPairTwoStageMass
open AsymmetricReturnPrefixRecovery AsymmetricSplitCompletionCode
open AsymmetricSplitCompletionPreservation AsymmetricSplitLevelSplice
open MarkedBridgeFactorization SharedPrefixPairExtraction
open TerminalSpliceProfileGeometry
open TerminalGlobalExitSplice TerminalSkeletonFactorization
open TerminalProfileClockEquivalence TerminalSkeletonInvariance
open TerminalSkeletonWords
open TerminalSequentialVisitLaw ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Every erased return selected by the literal completed-excursion count
returns to the split middle boundary before the first global exit. -/
theorem sourceReturnComplete
    {n k horizon : ℕ} {y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon) :
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) omega horizon
    ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon := by
  classical
  dsimp only
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) omega horizon
  have hfirst : AbsoluteBoundaryFirstAt
      (discBoundary (0, 0) (outerScale n)) (0, 0) omega horizon := by
    have hzeroAdd : ∀ p : Point, (0, 0) + p = p := by
      rintro ⟨a, b⟩
      simp only [Prod.mk_add_mk, zero_add]
    simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
      PlanarPotential.trajectoryFrom, hzeroAdd] using hexit
  have hcount : boundaryExcursionCount middle inner (0, 0) omega horizon = q :=
    rfl
  have hseparates : ∀ z ∈ inner,
      FirstHitSeparates middle (discBoundary (0, 0) (outerScale n)) z := by
    intro z hz
    apply FirstHitSeparates.innerBoundary
    · exact hz.1.trans (scaleRadius_antitone_of_le
        (by omega : k ≤ k + 1) hk)
    · intro w hw hlocal
      exact (profileDisc_disjoint_globalBoundary hn (by omega : k ≤ n)
        hy hlocal) hw
  intro j
  have hreturn := returnExitTime_le_of_boundaryExcursionExitAtom
    hfirst hcount hseparates j
  simpa only [returnExitTime, trajectoryFrom_zero_eq_trajectory] using hreturn

/-- Every selected entrance point of a completed extracted return lies on
the inner boundary.  Keeping this reduction separate prevents the large
assembled-path theorem from repeatedly unfolding the clock extractor. -/
theorem extractedReturnEntrancePoint_mem_inner
    {horizon q : ℕ} {omega : StepPath} {middle inner : Set Point}
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon) (j : Fin q) :
    trajectory omega
        (returnEntranceTime omega (0, 0) middle inner horizon (j : ℕ)) ∈
      inner := by
  have hfinish :
      excursionFinish (trajectory omega) middle inner horizon (j : ℕ) ≤
        horizon :=
    (TerminalExcursionPathwise.excursionFinish_le_next_start
      (trajectory omega) middle inner horizon (j : ℕ)).trans (hcomplete j)
  have hj := ThickPoint.excursionFinish_mem_inner_of_le
    (trajectory omega) middle inner horizon (j : ℕ)
    hfinish
  simpa only [returnEntranceTime, trajectoryFrom_zero_eq_trajectory] using hj

theorem profileInnerBoundary_succ_subset_disc
    {n k : ℕ} {y z : Point} (hk : k + 1 ≤ n)
    (hz : z ∈ profileInnerBoundary n (k + 1) y) :
    z ∈ disc y (scaleRadius n k) :=
  hz.1.trans (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk)

theorem extractedReturnEntrancePoint_mem_profileDisc
    {n k horizon q : ℕ} {y : Point} {omega : StepPath}
    (hk : k + 1 ≤ n)
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) (profileInnerBoundary n k y)
          (profileInnerBoundary n (k + 1) y) horizon (j + 1) ≤ horizon)
    (j : Fin q) :
    (extractTimedReturnSkeleton omega (0, 0) (profileInnerBoundary n k y)
        (profileInnerBoundary n (k + 1) y) horizon q).entrancePoint j ∈
      disc y (scaleRadius n k) := by
  apply profileInnerBoundary_succ_subset_disc
    (n := n) (k := k) (y := y) hk
  have hj := extractedReturnEntrancePoint_mem_inner hcomplete j
  simpa only [extractTimedReturnSkeleton, returnEntrancePoint,
    trajectoryFrom_zero_eq_trajectory] using hj

/-- Arbitrary endpoint-matched first-middle-hit replacements preserve the
first global exit of an actual stopped source. -/
theorem sourceGlobalFirst
    {n k horizon : ℕ} {y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon) :
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) omega horizon
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let code := compressTimedSkeleton omega t
    ∀ bridges : (j : Fin q) → BoundaryExitWordCode middle
        (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale n))
        (0, 0) (assembledTerminalPath code
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2)) := by
  classical
  dsimp only
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) omega horizon
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let code := compressTimedSkeleton omega t
  have hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon := by
    exact sourceReturnComplete hn hk hy hexit
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  intro bridges
  have hword : IsOuterExitTime
      (wordWalk (0, 0)
        (reconstructTerminalPacket
          (code, fun j ↦ List.ofFn (bridges j).1.2))) n
      (assembledTerminalHorizon code
        (fun j ↦ List.ofFn (bridges j).1.2)) := by
    have h := isOuterExitTime_assembled_profileReturnCodes hn
      (by omega : k ≤ n) hy ht hexit
      (fun j ↦ by
        simpa only [t] using
          extractTimedReturnSkeleton_entrancePoint_apply
            omega middle inner horizon q j)
      (fun j ↦ by
        simpa only [t] using
          extractTimedReturnSkeleton_exitPoint_apply
            omega middle inner horizon q j) ?_ bridges
    · exact h
    · intro j
      simpa only [t, middle, inner] using
        extractedReturnEntrancePoint_mem_profileDisc hk hcomplete j
  have hpath := isOuterExitTime_assembledTerminalPath_of_wordWalk hword
  have hzeroAdd : ∀ p : Point, (0, 0) + p = p := by
    rintro ⟨a, b⟩
    simp only [Prod.mk_add_mk, zero_add]
  simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
    PlanarPotential.trajectoryFrom, hzeroAdd] using hpath

/-- One endpoint-matched replacement carrying the source return's complete
scanner transition.  Naming this dependent type avoids repeatedly reducing
the clock extractor in the source-profile theorem below. -/
abbrev ExtractedCompatibleReturnCandidate
    (n : ℕ) (z : Point) (omega : StepPath) (middle inner : Set Point)
    (horizon q : ℕ) (j : Fin q) :=
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let code := compressTimedSkeleton omega t
  {b : BoundaryExitWordCode middle (code.2.1 j) (code.2.2 j) //
    XProfileScanCompatible n z (code.2.1 j)
      (intervalWords omega t.entrance t.exit j) (List.ofFn b.1.2)}

theorem sourceReconstructedPacketProfile_eq
    {n horizon q : ℕ} {z : Point} {omega : StepPath}
    {middle inner : Set Point}
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let code := compressTimedSkeleton omega t
    let sourceWords : TerminalSegmentWords q :=
      intervalWords omega t.entrance t.exit
    excursionProfile
        (wordWalk (0, 0) (reconstructTerminalPacket (code, sourceWords)))
        n (assembledTerminalHorizon code sourceWords) z =
      excursionProfile (trajectory omega) n horizon z := by
  classical
  dsimp only
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let code := compressTimedSkeleton omega t
  let sourceWords : TerminalSegmentWords q :=
    intervalWords omega t.entrance t.exit
  have hreconstruct : reconstructTerminalPacket (code, sourceWords) =
      incrementSlice omega 0 horizon := by
    apply reconstruct_extractTimedReturnSkeleton
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have hsourceHorizon : assembledTerminalHorizon code sourceWords = horizon := by
    unfold assembledTerminalHorizon assembledTerminalWord
    simp only [TerminalSkeletonInvariance.stoppedWordOfList_length]
    rw [hreconstruct, incrementSlice_length]
    omega
  rw [hsourceHorizon]
  apply Proposition13Measurability.excursionProfile_congr_prefix
  intro r hr
  rw [hreconstruct]
  simpa only [wordWalk, Nat.zero_add, trajectory_zero] using
    wordPosition_incrementSlice omega (Nat.zero_le horizon) hr

theorem assembledTerminalPath_excursionProfile_eq_wordWalk
    {n q : ℕ} {z : Point} (code : TerminalSkeletonCode q)
    (words : TerminalSegmentWords q) :
    excursionProfile (trajectory (assembledTerminalPath code words)) n
        (assembledTerminalHorizon code words) z =
      excursionProfile
        (wordWalk (0, 0) (reconstructTerminalPacket (code, words))) n
        (assembledTerminalHorizon code words) z := by
  apply Proposition13Measurability.excursionProfile_congr_prefix
  intro r hr
  exact (wordWalk_reconstruct_eq_trajectory_assembledTerminalPath_of_le
    code words hr).symm

theorem excursionProfile_assembled_eq_of_skeletonPointCompatibleReturnCodes
    {n q : ℕ} (hn : 2 ≤ n) {z : Point}
    {omega : StepPath} {t : TimedTerminalSkeleton q}
    (ht : t.WellFormed) (returnBoundary : Set Point)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j,
      t.exitPoint j = trajectory omega (t.exit j))
    (candidate : (j : Fin q) →
      {b : BoundaryExitWordCode returnBoundary
          (t.entrancePoint j) (t.exitPoint j) //
        XProfileScanCompatible n z (t.entrancePoint j)
          (intervalWords omega t.entrance t.exit j) (List.ofFn b.1.2)}) :
    excursionProfile
        (wordWalk (0, 0)
          (alternatingConcat q
            (complementaryPieces q omega 0 t.horizon t.entrance t.exit)
            (intervalWords omega t.entrance t.exit))) n
        (alternatingConcat q
          (complementaryPieces q omega 0 t.horizon t.entrance t.exit)
          (intervalWords omega t.entrance t.exit)).length z =
      excursionProfile
        (wordWalk (0, 0)
          (alternatingConcat q
            (complementaryPieces q omega 0 t.horizon t.entrance t.exit)
            (fun j ↦ List.ofFn (candidate j).1.1.2))) n
        (alternatingConcat q
          (complementaryPieces q omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (candidate j).1.1.2)).length z := by
  classical
  let bridges : ∀ j : Fin q, BoundaryExitWordCode returnBoundary
      (trajectory omega (t.entrance j)) (trajectory omega (t.exit j)) :=
    fun j ↦ ⟨(candidate j).1, by
      rw [← hentrancePoint j, ← hexitPoint j]
      exact (candidate j).1.2⟩
  let geometry := extracted_endpointGeometry_of_boundaryExitWordCodes
    omega t ht returnBoundary bridges
  apply excursionProfile_alternatingConcat_eq_of_xProfileScanCompatible
    hn geometry
  intro j
  rw [extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart]
  have hc : XProfileScanCompatible n z (trajectory omega (t.entrance j))
      (intervalWords omega t.entrance t.exit j)
      (List.ofFn (candidate j).1.1.2) :=
    Eq.mp (congrArg (fun p ↦ XProfileScanCompatible n z p
      (intervalWords omega t.entrance t.exit j)
      (List.ofFn (candidate j).1.1.2)) (hentrancePoint j))
      (candidate j).2
  simpa only [bridges] using hc

theorem assembledCandidateProfile_eq_sourcePacketProfile
    {n horizon q : ℕ} {z : Point} {omega : StepPath}
    {middle inner : Set Point}
    (hn : 2 ≤ n)
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon)
    (candidate : (j : Fin q) →
      ExtractedCompatibleReturnCandidate n z omega middle inner horizon q j) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let code := compressTimedSkeleton omega t
    let sourceWords : TerminalSegmentWords q :=
      intervalWords omega t.entrance t.exit
    let words : TerminalSegmentWords q :=
      fun j ↦ List.ofFn (candidate j).1.1.2
    excursionProfile (trajectory (assembledTerminalPath code words)) n
        (assembledTerminalHorizon code words) z =
      excursionProfile
        (wordWalk (0, 0) (reconstructTerminalPacket (code, sourceWords))) n
        (assembledTerminalHorizon code sourceWords) z := by
  classical
  dsimp only
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let code := compressTimedSkeleton omega t
  let sourceWords : TerminalSegmentWords q :=
    intervalWords omega t.entrance t.exit
  let words : TerminalSegmentWords q :=
    fun j ↦ List.ofFn (candidate j).1.1.2
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j) := by
    intro j
    simpa only [t] using extractTimedReturnSkeleton_entrancePoint_apply
      omega middle inner horizon q j
  have hexitPoint : ∀ j,
      t.exitPoint j = trajectory omega (t.exit j) := by
    intro j
    simpa only [t] using extractTimedReturnSkeleton_exitPoint_apply
      omega middle inner horizon q j
  have hwordProfile :=
    excursionProfile_assembled_eq_of_skeletonPointCompatibleReturnCodes
      hn ht middle hentrancePoint hexitPoint candidate
  exact (assembledTerminalPath_excursionProfile_eq_wordWalk code words).trans
    hwordProfile.symm

/-- Scanner-compatible replacement identifies the complete profile of the
canonical assembled path with that of the actual stopped source. -/
theorem sourceCandidateProfile_eq
    {n horizon q : ℕ} {z : Point} {omega : StepPath}
    {middle inner : Set Point}
    (hn : 2 ≤ n)
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤
        horizon)
    (candidate : (j : Fin q) →
      ExtractedCompatibleReturnCandidate n z omega middle inner horizon q j) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let code := compressTimedSkeleton omega t
    let words : TerminalSegmentWords q :=
      fun j ↦ List.ofFn (candidate j).1.1.2
    excursionProfile (trajectory (assembledTerminalPath code words)) n
      (assembledTerminalHorizon code words) z =
      excursionProfile (trajectory omega) n horizon z := by
  exact (assembledCandidateProfile_eq_sourcePacketProfile hn hcomplete
    candidate).trans (sourceReconstructedPacketProfile_eq hcomplete)

noncomputable abbrev sourceSplitCompletionData
    (start n k : ℕ) (x y : Point) (omega : StepPath) :
    SplitCompletionData start n :=
  splitCompletionDataAt start n k x y omega

@[simp] theorem sourceSplitCompletionData_returnCount
    (start n k : ℕ) (x y : Point) (omega : StepPath) :
    (sourceSplitCompletionData start n k x y omega).returnCount =
      boundaryExcursionCount (profileInnerBoundary n k y)
        (profileInnerBoundary n (k + 1) y) (0, 0)
        (shiftSteps start omega) (stoppedOuterExitHorizon start n omega) := rfl

@[simp] theorem sourceSplitCompletionData_pre
    (start n k : ℕ) (x y : Point) (omega : StepPath) :
    (sourceSplitCompletionData start n k x y omega).pre =
      stepPrefix start omega := rfl

@[simp] theorem sourceSplitCompletionData_skeleton
    (start n k : ℕ) (x y : Point) (omega : StepPath) :
    (sourceSplitCompletionData start n k x y omega).skeleton =
      let horizon := stoppedOuterExitHorizon start n omega
      let sigma := shiftSteps start omega
      let middle := profileInnerBoundary n k y
      let inner := profileInnerBoundary n (k + 1) y
      let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
      compressTimedSkeleton sigma
        (extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q) := rfl

@[simp] theorem sourceSplitCompletionData_signature_apply
    (start n k : ℕ) (x y : Point) (omega : StepPath)
    (j : Fin (sourceSplitCompletionData start n k x y omega).returnCount) :
    let horizon := stoppedOuterExitHorizon start n omega
    let sigma := shiftSteps start omega
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
    (sourceSplitCompletionData start n k x y omega).signature j =
      (XProfileScanSignature n x (t.entrancePoint j)
          (intervalWords sigma t.entrance t.exit j),
        XProfileScanSignature n y (t.entrancePoint j)
          (intervalWords sigma t.entrance t.exit j)) := by
  rfl

/-- Forget the scanner certificate on a source-data candidate while
presenting its endpoints in the literal extracted-clock coordinates. -/
noncomputable def sourceCandidateBoundaryCodes
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (candidate : (j : Fin
      (sourceSplitCompletionData start n k x y omega).returnCount) →
      SignatureCompatibleReturnCode x y (profileInnerBoundary n k y)
        (sourceSplitCompletionData start n k x y omega) j) :
    let horizon := stoppedOuterExitHorizon start n omega
    let sigma := shiftSteps start omega
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
    (j : Fin q) → BoundaryExitWordCode middle
      (trajectory sigma (t.entrance j)) (trajectory sigma (t.exit j)) := by
  dsimp only
  intro j
  refine ⟨(candidate j).1.1, ?_, ?_⟩
  · simpa only [sourceSplitCompletionData_skeleton,
      compressTimedSkeleton_entrancePoint,
      extractTimedReturnSkeleton_entrancePoint_apply] using
        (candidate j).1.2.1
  · simpa only [sourceSplitCompletionData_skeleton,
      compressTimedSkeleton_entrancePoint,
      compressTimedSkeleton_exitPoint,
      extractTimedReturnSkeleton_entrancePoint_apply,
      extractTimedReturnSkeleton_exitPoint_apply] using (candidate j).1.2.2

@[simp] theorem sourceCandidateBoundaryCodes_word
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (candidate : (j : Fin
      (sourceSplitCompletionData start n k x y omega).returnCount) →
      SignatureCompatibleReturnCode x y (profileInnerBoundary n k y)
        (sourceSplitCompletionData start n k x y omega) j)
    (j : Fin (sourceSplitCompletionData start n k x y omega).returnCount) :
    List.ofFn ((sourceCandidateBoundaryCodes candidate j).1.2) =
      List.ofFn (candidate j).1.1.2 := by
  rfl

noncomputable def sourceSplitCompletionAtom
    {start n k : ℕ} {x y : Point} (omega : StepPath)
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) := by
  let horizon := stoppedOuterExitHorizon start n omega
  let sigma := shiftSteps start omega
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  let code := compressTimedSkeleton sigma t
  exact pairedSignatureFixedCompletionAtom (n := n) x y code
    (intervalWords sigma t.entrance t.exit) middle
    (discBoundary (0, 0) (outerScale n)) (0, 0)
    (stepPrefix start omega) (sourceGlobalFirst hn hk hy hexit)

attribute [irreducible] sourceSplitCompletionAtom

theorem source_mem_intervalWordsStoppedCylinder
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) :
    let horizon := stoppedOuterExitHorizon start n omega
    let sigma := shiftSteps start omega
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
    omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix start omega)
        (compressTimedSkeleton sigma t)
        (intervalWords sigma t.entrance t.exit)) := by
  classical
  dsimp only
  let horizon := stoppedOuterExitHorizon start n omega
  let sigma := shiftSteps start omega
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  have hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom (0, 0) sigma)
        middle inner horizon (j + 1) ≤ horizon := by
    simpa only [trajectoryFrom_zero_eq_trajectory] using
      (sourceReturnComplete hn hk hy hexit)
  have ht : t.WellFormed := by
    exact extractTimedReturnSkeleton_wellFormed hcomplete
  exact mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
    omega t ht

theorem source_mem_pairedSignatureCompletionAt
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) :
    let horizon := stoppedOuterExitHorizon start n omega
    let sigma := shiftSteps start omega
    let middle := profileInnerBoundary n k y
    let inner := profileInnerBoundary n (k + 1) y
    let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
    let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
    let code := compressTimedSkeleton sigma t
    omega ∈ (pairedSignatureFixedCompletionAtom (n := n) x y code
      (intervalWords sigma t.entrance t.exit) middle
      (discBoundary (0, 0) (outerScale n)) (0, 0)
      (stepPrefix start omega) (sourceGlobalFirst hn hk hy hexit)).event := by
  classical
  dsimp only
  let horizon := stoppedOuterExitHorizon start n omega
  let sigma := shiftSteps start omega
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  let code := compressTimedSkeleton sigma t
  let sourceFirst := sourceGlobalFirst hn hk hy hexit
  have hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom (0, 0) sigma)
        middle inner horizon (j + 1) ≤ horizon := by
    simpa only [trajectoryFrom_zero_eq_trajectory] using
      (sourceReturnComplete hn hk hy hexit)
  let source := extractedReturnCodes hcomplete
  have hcylinder : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix start omega) code
        (intervalWords sigma t.entrance t.exit)) := by
    exact source_mem_intervalWordsStoppedCylinder (x := x) hn hk hy hexit
  apply mem_pairedSignatureFixedCompletionAtom_of_sourceCylinder
    sourceFirst source
  · intro j
    exact extractedReturnCodes_toList hcomplete j
  · exact hcylinder

/-- The stopped source belongs to the completion atom indexed by its own
prefix, compressed return skeleton, and two scanner signatures. -/
theorem source_mem_splitCompletionAtomAt
    {start n k : ℕ} {x y : Point} {omega : StepPath}
    (hn : 1 ≤ n) (hk : k + 1 ≤ n)
    (hy : y ∈ candidateBox n)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) n
      (stoppedOuterExitHorizon start n omega)) :
    omega ∈ (sourceSplitCompletionAtom (start := start) (n := n) (k := k)
      (x := x) (y := y) omega hn hk hy hexit).event := by
  unfold sourceSplitCompletionAtom
  exact source_mem_pairedSignatureCompletionAt hn hk hy hexit

end

end Erdos1165.AsymmetricSplitCompletionSource
