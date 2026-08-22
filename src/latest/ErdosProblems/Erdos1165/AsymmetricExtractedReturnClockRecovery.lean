/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricExtractedReturnCompletion
import ErdosProblems.Erdos1165.TerminalRetainedHitSplice

/-!
# Exact re-extraction after annular return replacement

The split completion deletes the first `q` inner-to-middle return words.
Canonical first-hit replacement words recover those same clocks at their
literal offsets.  This is the arbitrary-profile-boundary analogue of the
terminal-only clock-recovery adapter.
-/

namespace Erdos1165.AsymmetricExtractedReturnClockRecovery

open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalVisitSpliceInvariance TerminalClockSplice
open TerminalRetainedHitSplice TerminalPacketEndpointAlignment
open TerminalRetainedPieceOffsets TerminalGlobalExitSplice
open MarkedBridgeFactorization AsymmetricSplitLevelSplice
open TerminalSkeletonInvariance

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] lemma trajectoryFrom_zero_eq_trajectory (omega : StepPath) :
    PlanarPotential.trajectoryFrom (0, 0) omega = trajectory omega := by
  funext r
  rw [PlanarPotential.trajectoryFrom_eq_add_trajectory]
  ext <;> simp

/-- Canonical endpoint-matched first-middle-hit words recover the literal
return clocks of an extracted annular skeleton. -/
theorem returnClocks_reconstructed_of_boundaryExitWordCodes
    {horizon q : ℕ} {middle inner : Set Point} {omega : StepPath}
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤ horizon)
    (bridges : ∀ j : Fin q,
      BoundaryExitWordCode middle
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).entrance j))
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).exit j))) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let pieces := complementaryPieces q omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords q := fun j ↦ List.ofFn (bridges j).1.2
    let newHorizon := (alternatingConcat q pieces words).length
    ∀ j : Fin q,
      returnEntranceTime (reconstructedTerminalStepPath pieces words)
          (0, 0) middle inner newHorizon j =
        replacementWordStart q pieces words j ∧
      returnExitTime (reconstructedTerminalStepPath pieces words)
          (0, 0) middle inner newHorizon j =
        replacementWordStop pieces words j := by
  classical
  dsimp only
  by_cases hq : q = 0
  · subst q
    intro j
    exact Fin.elim0 j
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let pieces := complementaryPieces q omega 0 horizon t.entrance t.exit
  let words : TerminalSegmentWords q := fun j ↦ List.ofFn (bridges j).1.2
  let newOmega := reconstructedTerminalStepPath pieces words
  let newHorizon := (alternatingConcat q pieces words).length
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have halign : ∀ j : Fin q,
      trajectory newOmega (replacementWordStart q pieces words j) =
          trajectory omega (t.entrance j) ∧
      trajectory newOmega (replacementWordStop pieces words j) =
          trajectory omega (t.exit j) := by
    simpa [t, pieces, words, newOmega, extractTimedReturnSkeleton] using
      replacementWordStart_stop_alignment_of_boundaryExitWordCodes
        omega t ht middle bridges
  let s := trajectory omega
  let initialOuterTime := excursionStart s middle inner horizon 0
  have hentranceZeroLe : t.entrance ⟨0, hqpos⟩ ≤ horizon :=
    (ht.1 ⟨0, hqpos⟩).1.trans (ht.1 ⟨0, hqpos⟩).2
  have hinitialLe : initialOuterTime ≤ horizon := by
    have hle : initialOuterTime ≤ t.entrance ⟨0, hqpos⟩ := by
      have hclock := excursionStart_le_finish s middle inner horizon 0
      simpa only [initialOuterTime, t, extractTimedReturnSkeleton,
        returnEntranceTime, s, trajectoryFrom_zero_eq_trajectory] using hclock
    exact hle.trans hentranceZeroLe
  have hfirstOuter : IsFirstHitSegment s middle
      0 initialOuterTime horizon := by
    have hle : firstHitThrough s middle 0 horizon ≤ horizon := by
      simpa [initialOuterTime, excursionStart] using hinitialLe
    simpa [initialOuterTime, excursionStart] using
      isFirstHitSegment_firstHitThrough_of_le s middle 0 horizon hle
  have hfirstInnerZero : IsFirstHitSegment s inner initialOuterTime
      (t.entrance ⟨0, hqpos⟩) horizon := by
    have hclock : t.entrance ⟨0, hqpos⟩ =
        firstHitThrough s inner initialOuterTime horizon := by
      simp only [t, extractTimedReturnSkeleton, returnEntranceTime,
        excursionFinish, initialOuterTime, s,
        trajectoryFrom_zero_eq_trajectory]
    have hle : firstHitThrough s inner initialOuterTime horizon ≤ horizon := by
      rw [← hclock]
      exact hentranceZeroLe
    have hseg := isFirstHitSegment_firstHitThrough_of_le s inner
      initialOuterTime horizon hle
    rwa [← hclock] at hseg
  have hfirstInnerSucc : ∀ (j : Fin q) (hj : (j : ℕ) + 1 < q),
      IsFirstHitSegment s inner (t.exit j)
        (t.entrance ⟨(j : ℕ) + 1, hj⟩) horizon := by
    intro j hj
    let next : Fin q := ⟨(j : ℕ) + 1, hj⟩
    have hnextLe : t.entrance next ≤ horizon :=
      (ht.1 next).1.trans (ht.1 next).2
    have hstartClock : t.exit j =
        excursionStart s middle inner horizon ((j : ℕ) + 1) := by
      simp only [t, extractTimedReturnSkeleton, returnExitTime, s,
        trajectoryFrom_zero_eq_trajectory]
    have hstopClock : t.entrance next =
        firstHitThrough s inner (t.exit j) horizon := by
      rw [hstartClock]
      simp only [t, extractTimedReturnSkeleton, returnEntranceTime,
        excursionFinish, next, s, trajectoryFrom_zero_eq_trajectory]
    have hle : firstHitThrough s inner (t.exit j) horizon ≤ horizon := by
      rw [← hstopClock]
      exact hnextLe
    have hseg := isFirstHitSegment_firstHitThrough_of_le s inner
      (t.exit j) horizon hle
    rwa [← hstopClock] at hseg
  have retained : RetainedFirstHitInputs omega t words middle inner := by
    apply retainedFirstHitInputsOfEndpointAlignment hqpos omega t words
      middle inner initialOuterTime hfirstOuter hfirstInnerZero hfirstInnerSucc
    intro j
    exact (halign j).2
  let visits : Fin q → ℕ := fun j ↦
    replacementWordVisitCount (trajectory omega (t.entrance j))
      (0, 0) (words j)
  have hadmissible : ∀ j : Fin q,
      AdmissibleReplacementWord middle (0, 0)
        (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j)) (visits j) (words j) := by
    intro j
    simpa [visits, words] using
      admissibleReplacementWord_of_boundaryExitWordCode middle (0, 0)
        (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j)) (bridges j)
  have hclocks := terminalClocks_reconstructed_eq_replacementOffsets hqpos
    pieces words middle inner (0, 0)
    (fun j ↦ trajectory omega (t.entrance j))
    (fun j ↦ trajectory omega (t.exit j)) visits newHorizon
    retained.initialOuterTime le_rfl retained.firstOuter
    (retained.firstInnerZero hqpos) retained.firstInnerSucc
    (fun j ↦ (halign j).1) hadmissible
  intro j
  have hj := hclocks j
  simpa only [returnEntranceTime, returnExitTime,
    trajectoryFrom_zero_eq_trajectory] using hj

/-- The interval between the literal replacement offsets of the
reconstructed packet is exactly the inserted word. -/
theorem intervalWords_reconstructed_eq_replacementWords
    {q : ℕ} (pieces : Fin (q + 1) → List Direction)
    (words : TerminalSegmentWords q) (j : Fin q) :
    intervalWords (reconstructedTerminalStepPath pieces words)
        (fun i ↦ replacementWordStart q pieces words i)
        (fun i ↦ replacementWordStop pieces words i) j = words j := by
  have hmem := shift_reconstructed_mem_stoppedWordCylinder pieces words j
  have hlength : replacementWordStop pieces words j -
      replacementWordStart q pieces words j = (words j).length := by
    simp [replacementWordStop]
  unfold intervalWords
  rw [incrementSlice]
  simp only [hlength]
  change List.ofFn
      (stepPrefix (words j).length
        (shiftSteps (replacementWordStart q pieces words j)
          (reconstructedTerminalStepPath pieces words))) = words j
  have hprefix : stepPrefix (words j).length
      (shiftSteps (replacementWordStart q pieces words j)
        (reconstructedTerminalStepPath pieces words)) =
        (TerminalVisitSpliceInvariance.stoppedWordOfList (words j)).2 := by
    change stepPrefix (words j).length
        (shiftSteps (replacementWordStart q pieces words j)
          (reconstructedTerminalStepPath pieces words)) =
      fun i ↦ (words j).get i at hmem
    exact hmem
  rw [hprefix]
  exact List.ofFn_get _

/-- Re-extracting after arbitrary canonical first-middle-hit replacements
recovers both the compressed retained skeleton and the literal replacement
word at every erased coordinate. -/
theorem compressedReturnSkeleton_reconstructed_of_boundaryExitWordCodes
    {horizon q : ℕ} {middle inner : Set Point} {omega : StepPath}
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory omega) middle inner horizon (j + 1) ≤ horizon)
    (bridges : ∀ j : Fin q,
      BoundaryExitWordCode middle
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).entrance j))
        (trajectory omega
          ((extractTimedReturnSkeleton omega (0, 0) middle inner
            horizon q).exit j))) :
    let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
    let pieces := complementaryPieces q omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords q := fun j ↦ List.ofFn (bridges j).1.2
    let newOmega := reconstructedTerminalStepPath pieces words
    let newHorizon := (alternatingConcat q pieces words).length
    let newT := extractTimedReturnSkeleton newOmega (0, 0) middle inner
      newHorizon q
    compressTimedSkeleton newOmega newT = compressTimedSkeleton omega t ∧
      ∀ j, intervalWords newOmega newT.entrance newT.exit j = words j := by
  classical
  dsimp only
  let t := extractTimedReturnSkeleton omega (0, 0) middle inner horizon q
  let pieces := complementaryPieces q omega 0 horizon t.entrance t.exit
  let words : TerminalSegmentWords q := fun j ↦ List.ofFn (bridges j).1.2
  let newOmega := reconstructedTerminalStepPath pieces words
  let newHorizon := (alternatingConcat q pieces words).length
  let newT := extractTimedReturnSkeleton newOmega (0, 0) middle inner
    newHorizon q
  have ht : t.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have halign : ∀ j : Fin q,
      trajectory newOmega (replacementWordStart q pieces words j) =
          trajectory omega (t.entrance j) ∧
      trajectory newOmega (replacementWordStop pieces words j) =
          trajectory omega (t.exit j) := by
    simpa [t, pieces, words, newOmega, extractTimedReturnSkeleton] using
      replacementWordStart_stop_alignment_of_boundaryExitWordCodes
        omega t ht middle bridges
  have hclocks : ∀ j : Fin q,
      newT.entrance j = replacementWordStart q pieces words j ∧
      newT.exit j = replacementWordStop pieces words j := by
    exact returnClocks_reconstructed_of_boundaryExitWordCodes
      hcomplete bridges
  have hentrancePoint : newT.entrancePoint = t.entrancePoint := by
    funext j
    calc
      newT.entrancePoint j =
          PlanarPotential.trajectoryFrom (0, 0) newOmega
            (newT.entrance j) := rfl
      _ = trajectory newOmega (newT.entrance j) := by
        rw [trajectoryFrom_zero_eq_trajectory]
      _ = trajectory newOmega
          (replacementWordStart q pieces words j) := by rw [(hclocks j).1]
      _ = trajectory omega (t.entrance j) := (halign j).1
      _ = PlanarPotential.trajectoryFrom (0, 0) omega
          (t.entrance j) := by rw [trajectoryFrom_zero_eq_trajectory]
      _ = t.entrancePoint j := rfl
  have hexitPoint : newT.exitPoint = t.exitPoint := by
    funext j
    calc
      newT.exitPoint j =
          PlanarPotential.trajectoryFrom (0, 0) newOmega
            (newT.exit j) := rfl
      _ = trajectory newOmega (newT.exit j) := by
        rw [trajectoryFrom_zero_eq_trajectory]
      _ = trajectory newOmega
          (replacementWordStop pieces words j) := by rw [(hclocks j).2]
      _ = trajectory omega (t.exit j) := (halign j).2
      _ = PlanarPotential.trajectoryFrom (0, 0) omega
          (t.exit j) := by rw [trajectoryFrom_zero_eq_trajectory]
      _ = t.exitPoint j := rfl
  have hrecovery :=
    compressTimedSkeleton_reconstructed_eq_of_replacementOffsets pieces words
      newT t.entrancePoint t.exitPoint rfl (fun j ↦ (hclocks j).1)
      (fun j ↦ (hclocks j).2) hentrancePoint hexitPoint
  have horiginal : compressTimedSkeleton omega t =
      (⟨pieces⟩, (t.entrancePoint, t.exitPoint)) := rfl
  constructor
  · exact hrecovery.trans horiginal.symm
  · intro j
    calc
      intervalWords newOmega newT.entrance newT.exit j =
          intervalWords newOmega
            (fun i ↦ replacementWordStart q pieces words i)
            (fun i ↦ replacementWordStop pieces words i) j := by
        unfold intervalWords
        rw [(hclocks j).1, (hclocks j).2]
      _ = words j :=
        intervalWords_reconstructed_eq_replacementWords pieces words j

end

end Erdos1165.AsymmetricExtractedReturnClockRecovery
