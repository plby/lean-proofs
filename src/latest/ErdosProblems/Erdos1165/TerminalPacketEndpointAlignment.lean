/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.TerminalGlobalExitSplice
import ErdosProblems.Erdos1165.TerminalRetainedPieceOffsets

/-!
# Endpoint alignment in a reconstructed terminal packet

The complementary pieces of a timed terminal skeleton remember the literal
walk between successive deleted words.  Consequently replacement words which
have the recorded relative endpoints force, rather than assume, the absolute
splice positions.  At every coordinate the reconstructed walk is at the old
entrance point when the replacement word starts and at the old exit point
when it stops.

This is the missing non-circular endpoint input for the retained-piece clock
transport: the induction advances through a replacement word using its
relative endpoint, then through the following retained increment slice.
-/

namespace Erdos1165.TerminalPacketEndpointAlignment

open TerminalSkeletonWords TerminalVisitSpliceInvariance
open TerminalRetainedPieceOffsets TerminalGlobalExitSplice
open TerminalSequentialVisitLaw MarkedBridgeFactorization

noncomputable section

/-! ## Finite-word endpoint lemmas -/

/-- The finite extension of a list reaches its `wordEndpoint` at the list's
length. -/
theorem trajectoryFrom_extendStoppedWord_stoppedWordOfList_length
    (a : Point) (word : List Direction) :
    PlanarPotential.trajectoryFrom a
        (extendStoppedWord (stoppedWordOfList word)) word.length =
      wordEndpoint a word := by
  have h := wordEndpoint_ofFn_stepPrefix a
    (extendStoppedWord (stoppedWordOfList word)) word.length
  have hprefix : stepPrefix word.length
      (extendStoppedWord (stoppedWordOfList word)) =
        (stoppedWordOfList word).2 := by
    simpa [stoppedWordOfList] using
      stepPrefix_extendStoppedWord (stoppedWordOfList word)
  rw [hprefix] at h
  simpa [stoppedWordOfList] using h.symm

/-- The reconstructed walk follows an inserted word from its absolute splice
start through its absolute splice stop. -/
theorem trajectory_reconstructed_replacementWordStop
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m) :
    trajectory (reconstructedTerminalStepPath pieces words)
        (replacementWordStop pieces words j) =
      wordEndpoint
        (trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStart m pieces words j))
        (words j) := by
  let newOmega := reconstructedTerminalStepPath pieces words
  let start := replacementWordStart m pieces words j
  have hmem := shift_reconstructed_mem_stoppedWordCylinder pieces words j
  have hprefix := trajectoryFrom_eq_extendStoppedWord_of_mem hmem
    (trajectory newOmega start) (q := (words j).length) le_rfl
  calc
    trajectory newOmega (replacementWordStop pieces words j) =
        trajectory newOmega (start + (words j).length) := by
          rfl
    _ = PlanarPotential.trajectoryFrom (trajectory newOmega start)
          (shiftSteps start newOmega) (words j).length := by
            rw [trajectoryFrom_shiftSteps_eq]
    _ = PlanarPotential.trajectoryFrom (trajectory newOmega start)
          (extendStoppedWord (stoppedWordOfList (words j)))
          (words j).length := hprefix
    _ = wordEndpoint (trajectory newOmega start) (words j) :=
      trajectoryFrom_extendStoppedWord_stoppedWordOfList_length _ _

/-- A retained piece which is an old increment slice carries an aligned left
endpoint to its old right endpoint. -/
theorem trajectory_reconstructed_retainedPieceStop_eq_of_incrementSlice
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1))
    (omega : StepPath) {start stop : ℕ} (hstart : start ≤ stop)
    (hpiece : pieces j = incrementSlice omega start stop)
    (halign : trajectory (reconstructedTerminalStepPath pieces words)
        (retainedPieceStart m pieces words j) = trajectory omega start) :
    trajectory (reconstructedTerminalStepPath pieces words)
        (retainedPieceStop pieces words j) = trajectory omega stop := by
  rw [trajectory_reconstructed_retainedPieceStop, halign, hpiece]
  rw [trajectoryFrom_extendStoppedWord_stoppedWordOfList_length]
  exact wordEndpoint_incrementSlice omega hstart

/-- Index-generic form of the literal retained gap identity. -/
theorem complementaryPieces_succ_of_lt : ∀ {m : ℕ} (omega : StepPath)
    (base horizon : ℕ) (entrance exit : Fin m → ℕ)
    (j : Fin m) (hj : (j : ℕ) + 1 < m),
    complementaryPieces m omega base horizon entrance exit j.succ =
      incrementSlice omega (exit j) (entrance ⟨(j : ℕ) + 1, hj⟩) := by
  intro m
  induction m with
  | zero =>
      intro omega base horizon entrance exit j
      exact Fin.elim0 j
  | succ m ih =>
      cases m with
      | zero =>
          intro omega base horizon entrance exit j hj
          omega
      | succ n =>
          intro omega base horizon entrance exit j hj
          let jj : Fin (n + 1) := ⟨(j : ℕ), by omega⟩
          have hcast : jj.castSucc = j := Fin.ext rfl
          have hsucc : jj.succ = ⟨(j : ℕ) + 1, hj⟩ := Fin.ext rfl
          simpa only [hcast, hsucc] using
            complementaryPieces_between n omega base horizon entrance exit jj

/-! ## Joint alignment theorem -/

/-- Endpoint-matched replacement words in the literal complementary packet
have the recorded absolute entrance and exit positions at every splice
coordinate. -/
theorem replacementWordStart_stop_alignment
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (words : TerminalSegmentWords m) (ht : t.WellFormed)
    (hwordEndpoint : ∀ j : Fin m,
      wordEndpoint (trajectory omega (t.entrance j)) (words j) =
        trajectory omega (t.exit j)) :
    ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStart m
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.entrance j) ∧
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStop
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.exit j) := by
  cases m with
  | zero =>
      intro j
      exact Fin.elim0 j
  | succ n =>
      let pieces := complementaryPieces (n + 1) omega 0 t.horizon
        t.entrance t.exit
      let newOmega := reconstructedTerminalStepPath pieces words
      have hzeroStart :
          trajectory newOmega
              (replacementWordStart (n + 1) pieces words 0) =
            trajectory omega (t.entrance 0) := by
        have hpiece : pieces (0 : Fin (n + 2)) =
            incrementSlice omega 0 (t.entrance 0) := by
          rfl
        have halign : trajectory newOmega
            (retainedPieceStart (n + 1) pieces words 0) =
              trajectory omega 0 := by
          simp [newOmega]
        have hstop :=
          trajectory_reconstructed_retainedPieceStop_eq_of_incrementSlice
            pieces words (0 : Fin (n + 2)) omega (Nat.zero_le _)
            hpiece halign
        have htime : retainedPieceStop pieces words (0 : Fin (n + 2)) =
            replacementWordStart (n + 1) pieces words
              (0 : Fin (n + 1)) := by
          simpa using retainedPieceStop_castSucc_eq_replacementWordStart
            pieces words (0 : Fin (n + 1))
        rw [htime] at hstop
        simpa [newOmega] using hstop
      have hzeroStop :
          trajectory newOmega (replacementWordStop pieces words 0) =
            trajectory omega (t.exit 0) := by
        rw [trajectory_reconstructed_replacementWordStop,
          hzeroStart, hwordEndpoint]
      intro j
      induction j using Fin.induction with
      | zero => exact ⟨hzeroStart, hzeroStop⟩
      | @succ i ih =>
          have hindex : (i.succ.castSucc : Fin (n + 2)) =
              (i.castSucc.succ : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          let next : Fin (n + 1) :=
            ⟨(i.castSucc : ℕ) + 1, by simp⟩
          have hnext : next = i.succ := by
            apply Fin.ext
            rfl
          have hpiece : pieces i.castSucc.succ =
              incrementSlice omega (t.exit i.castSucc)
                (t.entrance i.succ) := by
            have hp := complementaryPieces_succ_of_lt omega 0 t.horizon
              t.entrance t.exit i.castSucc (by simp)
            change pieces i.castSucc.succ =
              incrementSlice omega (t.exit i.castSucc) (t.entrance next) at hp
            simpa only [hnext] using hp
          have hordered : t.exit i.castSucc ≤ t.entrance i.succ :=
            ht.2 i.castSucc i.succ (by simp)
          have halignAtRetainedStart :
              trajectory newOmega
                  (retainedPieceStart (n + 1) pieces words
                    i.castSucc.succ) =
                trajectory omega (t.exit i.castSucc) := by
            rw [retainedPieceStart_succ_eq_replacementWordStop]
            exact ih.2
          have hnextStart :
              trajectory newOmega
                  (replacementWordStart (n + 1) pieces words i.succ) =
                trajectory omega (t.entrance i.succ) := by
            have hstop :=
              trajectory_reconstructed_retainedPieceStop_eq_of_incrementSlice
                pieces words i.castSucc.succ omega hordered hpiece
                halignAtRetainedStart
            rw [← hindex,
              retainedPieceStop_castSucc_eq_replacementWordStart] at hstop
            exact hstop
          have hnextStop :
              trajectory newOmega (replacementWordStop pieces words i.succ) =
                trajectory omega (t.exit i.succ) := by
            rw [trajectory_reconstructed_replacementWordStop,
              hnextStart, hwordEndpoint]
          exact ⟨hnextStart, hnextStop⟩

/-! ## Canonical word adapters -/

/-- The same joint alignment follows directly from admissibility of each
replacement word. -/
theorem replacementWordStart_stop_alignment_of_admissible
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (words : TerminalSegmentWords m) (ht : t.WellFormed)
    (boundary : Set Point) (target : Point) (visits : Fin m → ℕ)
    (hadmissible : ∀ j : Fin m,
      AdmissibleReplacementWord boundary target
        (trajectory omega (t.entrance j)) (trajectory omega (t.exit j))
        (visits j) (words j)) :
    ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStart m
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.entrance j) ∧
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)
          (replacementWordStop
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            words j) = trajectory omega (t.exit j) := by
  apply replacementWordStart_stop_alignment omega t words ht
  intro j
  rw [← trajectoryFrom_extendStoppedWord_stoppedWordOfList_length]
  exact (hadmissible j).2.2

/-- Canonical boundary-exit codes supply endpoint-matched words without any
additional geometric hypothesis. -/
theorem replacementWordStart_stop_alignment_of_boundaryExitWordCodes
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) (boundary : Set Point)
    (bridges : ∀ j : Fin m,
      BoundaryExitWordCode boundary (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j))) :
    ∀ j : Fin m,
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun k ↦ List.ofFn (bridges k).1.2))
          (replacementWordStart m
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            (fun k ↦ List.ofFn (bridges k).1.2) j) =
        trajectory omega (t.entrance j) ∧
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun k ↦ List.ofFn (bridges k).1.2))
          (replacementWordStop
            (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
            (fun k ↦ List.ofFn (bridges k).1.2) j) =
        trajectory omega (t.exit j) := by
  apply replacementWordStart_stop_alignment omega t
    (fun k ↦ List.ofFn (bridges k).1.2) ht
  intro j
  exact boundaryExitWordCode_wordEndpoint (bridges j)

end

end Erdos1165.TerminalPacketEndpointAlignment
