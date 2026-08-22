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

import ErdosProblems.Erdos1165.TerminalSkeletonWords
import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# Visit marks under terminal-word splicing

This file supplies the pathwise marking part of the compressed terminal
skeleton construction.  It first locates every inserted word inside the
literal `alternatingConcat`.  It then shows that, once the terminal excursion
clocks identify those same endpoints, the canonical `terminalVisitVector` is
exactly the vector of target-visit counts carried by the inserted words.

The clock identification is deliberately a premise of the final theorem.
It is the geometric part of splice invariance; the result here is the purely
finite-word visit-count calculation that follows from it.
-/

open Set

namespace Erdos1165.TerminalVisitSpliceInvariance

open ThickPoint
open TerminalExcursionPathwise TerminalSkeletonWords
open TerminalSequentialVisitLaw MarkedBridgeFactorization

noncomputable section

/-! ## Exact coordinates of inserted words -/

/-- The offset at which coordinate `j` of the replacement-word vector begins
inside the alternating concatenation. -/
def replacementWordStart : (m : ℕ) →
    (Fin (m + 1) → List Direction) → TerminalSegmentWords m → Fin m → ℕ
  | 0, _pieces, _words, j => Fin.elim0 j
  | m + 1, pieces, words, j =>
      Fin.cases (pieces 0).length
        (fun i ↦ (pieces 0).length + (words 0).length +
          replacementWordStart m (fun k ↦ pieces k.succ)
            (fun k ↦ words k.succ) i) j

/-- The offset immediately after replacement word `j`. -/
def replacementWordStop {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m) : ℕ :=
  replacementWordStart m pieces words j + (words j).length

lemma alternatingConcat_drop_replacementWordStart : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m),
    ∃ suffix,
      (alternatingConcat m pieces words).drop
          (replacementWordStart m pieces words j) =
        words j ++ suffix := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      exact Fin.elim0 j
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · refine ⟨alternatingConcat m (fun k ↦ pieces k.succ)
            (fun k ↦ words k.succ), ?_⟩
        simp [alternatingConcat, replacementWordStart]
      · obtain ⟨suffix, hsuffix⟩ := ih (fun k ↦ pieces k.succ)
          (fun k ↦ words k.succ) i
        refine ⟨suffix, ?_⟩
        calc
          (alternatingConcat (m + 1) pieces words).drop
              (replacementWordStart (m + 1) pieces words i.succ) =
              (alternatingConcat m (fun k ↦ pieces k.succ)
                (fun k ↦ words k.succ)).drop
                  (replacementWordStart m (fun k ↦ pieces k.succ)
                    (fun k ↦ words k.succ) i) := by
                      simp only [alternatingConcat, replacementWordStart,
                        Fin.cases_succ]
                      rw [← List.drop_drop]
                      simp
          _ = words i.succ ++ suffix := hsuffix

lemma replacementWordStart_le_alternatingConcat_length : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m),
    replacementWordStart m pieces words j ≤
      (alternatingConcat m pieces words).length := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      exact Fin.elim0 j
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp [replacementWordStart, alternatingConcat]
      · have htail := ih (fun k ↦ pieces k.succ) (fun k ↦ words k.succ) i
        simp only [replacementWordStart, Fin.cases_succ, alternatingConcat,
          List.length_append]
        omega

lemma replacementWordStop_le_alternatingConcat_length {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m) :
    replacementWordStop pieces words j ≤
      (alternatingConcat m pieces words).length := by
  obtain ⟨suffix, hsuffix⟩ :=
    alternatingConcat_drop_replacementWordStart m pieces words j
  have hlen := congrArg List.length hsuffix
  simp only [List.length_drop, List.length_append] at hlen
  have hstart := replacementWordStart_le_alternatingConcat_length
    m pieces words j
  unfold replacementWordStop
  omega

/-! ## Finite words as stopped-word paths -/

/-- A list of directions viewed as the stopped word having precisely that
length. -/
def stoppedWordOfList (word : List Direction) : StoppedWord :=
  ⟨word.length, fun j ↦ word.get j⟩

/-- Extend the whole alternating concatenation to an infinite step path.
Only its prefix through the concatenation length is ever used. -/
def reconstructedTerminalStepPath {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) : StepPath :=
  extendStoppedWord (stoppedWordOfList (alternatingConcat m pieces words))

/-- Literal target visits carried by one replacement word. -/
def replacementWordVisitCount (start target : Point)
    (word : List Direction) : ℕ :=
  targetVisitSum start target (extendStoppedWord (stoppedWordOfList word))
    word.length

/-- A replacement word is admissible for a marked terminal coordinate when
it first hits the prescribed boundary at its final time, carries the
prescribed number of target visits, and ends at the prescribed endpoint. -/
def AdmissibleReplacementWord (boundary : Set Point)
    (target start endpoint : Point) (visits : ℕ)
    (word : List Direction) : Prop :=
  AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (stoppedWordOfList word)) word.length ∧
    replacementWordVisitCount start target word = visits ∧
    PlanarPotential.trajectoryFrom start
      (extendStoppedWord (stoppedWordOfList word)) word.length = endpoint

@[simp] theorem extendStoppedWord_stoppedWordOfList_ofFn
    (word : StoppedWord) :
    extendStoppedWord (stoppedWordOfList (List.ofFn word.2)) =
      extendStoppedWord word := by
  rcases word with ⟨n, word⟩
  funext q
  simp [extendStoppedWord, stoppedWordOfList]

/-- Every canonical marked first-boundary word becomes an admissible list
after erasing its proof fields. -/
theorem admissibleReplacementWord_of_boundaryVisitExitWordCode
    (boundary : Set Point) (target start endpoint : Point) (visits : ℕ)
    (bridge : BoundaryVisitExitWordCode boundary target start visits endpoint) :
    AdmissibleReplacementWord boundary target start endpoint visits
      (List.ofFn bridge.1.2) := by
  simpa [AdmissibleReplacementWord, replacementWordVisitCount,
    extendStoppedWord_stoppedWordOfList_ofFn] using bridge.2

/-- Shifting the reconstructed path to the beginning of an inserted word
has that word as its exact stopped prefix. -/
theorem shift_reconstructed_mem_stoppedWordCylinder {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m) :
    shiftSteps (replacementWordStart m pieces words j)
        (reconstructedTerminalStepPath pieces words) ∈
      stoppedWordCylinder (stoppedWordOfList (words j)) := by
  let full := alternatingConcat m pieces words
  let start := replacementWordStart m pieces words j
  obtain ⟨suffix, hsuffix⟩ :=
    alternatingConcat_drop_replacementWordStart m pieces words j
  have hstop : start + (words j).length ≤ full.length := by
    simpa [full, start, replacementWordStop] using
      replacementWordStop_le_alternatingConcat_length pieces words j
  change stepPrefix (words j).length
      (shiftSteps start (extendStoppedWord (stoppedWordOfList full))) =
        (stoppedWordOfList (words j)).2
  funext q
  have hqfull : start + (q : ℕ) < full.length := by
    omega
  have hqdrop : (q : ℕ) < (full.drop start).length := by
    simp only [List.length_drop]
    omega
  have hqword : (q : ℕ) < (words j).length := q.isLt
  change extendStoppedWord (stoppedWordOfList full) (start + q) =
    (words j).get q
  have hqfull' : start + (q : ℕ) < (stoppedWordOfList full).1 := by
    exact hqfull
  rw [extendStoppedWord, dif_pos hqfull']
  change full.get ⟨start + q, hqfull⟩ = (words j).get q
  rw [List.get_eq_getElem, List.get_eq_getElem]
  have hsuffix' : full.drop start = words j ++ suffix := by
    simpa [full, start] using hsuffix
  have hopt := congrArg (fun l : List Direction ↦ l[(q : ℕ)]?) hsuffix'
  simp only [List.getElem?_eq_getElem hqdrop, List.getElem?_append,
    if_pos hqword, List.getElem?_eq_getElem hqword] at hopt
  have hdropWord : (full.drop start)[q] = (words j)[q] :=
    Option.some.inj hopt
  exact (List.getElem_drop (xs := full) (i := start) (j := q)).symm.trans hdropWord

/-! ## Visit-vector identification -/

/-- A single terminal excursion coordinate counts exactly the visits carried
by its replacement word, once the excursion clocks identify the word's two
splice offsets. -/
theorem innerVisitCount_reconstructed_eq_replacementWordVisitCount
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (target : Point) (j : Fin m)
    (hfinish : excursionFinish (trajectory
        (reconstructedTerminalStepPath pieces words)) outer inner horizon j =
      replacementWordStart m pieces words j)
    (hstart : excursionStart (trajectory
        (reconstructedTerminalStepPath pieces words)) outer inner horizon
          ((j : ℕ) + 1) = replacementWordStop pieces words j) :
    innerVisitCount (trajectory (reconstructedTerminalStepPath pieces words))
        outer inner horizon target j =
      replacementWordVisitCount
        (trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStart m pieces words j)) target (words j) := by
  let omega := reconstructedTerminalStepPath pieces words
  let t := replacementWordStart m pieces words j
  let u := replacementWordStop pieces words j
  have htu : t ≤ u := by simp [t, u, replacementWordStop]
  have hmem : shiftSteps t omega ∈ stoppedWordCylinder (stoppedWordOfList (words j)) :=
    shift_reconstructed_mem_stoppedWordCylinder pieces words j
  have hword := targetVisitSum_eq_extendStoppedWord_of_mem hmem
    (trajectory omega t) target
  have hshift := targetVisitSum_shift_eq_Ico_card omega target htu
  simp only [innerVisitCount, innerVisitTimes, hfinish, hstart]
  rw [← hshift]
  unfold replacementWordVisitCount
  have hlength : u - t = (words j).length := by
    simp [u, t, replacementWordStop]
  rw [hlength]
  simpa [stoppedWordOfList, omega, t] using hword

/-- For an alternating retained skeleton and any replacement terminal words,
the canonical terminal visit vector is the coordinatewise vector of literal
word visit counts, provided the terminal clocks select precisely the splice
offsets. -/
theorem terminalVisitVector_reconstructed_eq_replacementWordVisitCounts
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (pieces : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta + 1) →
      List Direction)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hfinish : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      extractedEntrance
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale horizon x (j : ℕ) =
        replacementWordStart
          (AppendixLocalTime.requiredTerminalCount scale profileDelta)
          pieces words j)
    (hstart : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      extractedExit
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale horizon x (j : ℕ) = replacementWordStop pieces words j) :
    terminalVisitVector (trajectory (reconstructedTerminalStepPath pieces words))
        scale horizon profileDelta x =
      fun j ↦ replacementWordVisitCount
        (trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStart
            (AppendixLocalTime.requiredTerminalCount scale profileDelta)
            pieces words j)) x (words j) := by
  classical
  funext j
  have hf :
      excursionFinish (trajectory (reconstructedTerminalStepPath pieces words))
          (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
          horizon (j : ℕ) =
        replacementWordStart
          (AppendixLocalTime.requiredTerminalCount scale profileDelta)
          pieces words j := by
    simpa [extractedEntrance] using hfinish j
  have hs :
      excursionStart (trajectory (reconstructedTerminalStepPath pieces words))
          (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
          horizon ((j : ℕ) + 1) = replacementWordStop pieces words j := by
    simpa [extractedExit, terminalSegmentExitTime] using hstart j
  exact innerVisitCount_reconstructed_eq_replacementWordVisitCount pieces words
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
    horizon x j hf hs

/-- Marked admissible replacement words therefore reproduce their prescribed
visit vector exactly.  This is the call-site form used by the marked terminal
skeleton factorization. -/
theorem terminalVisitVector_reconstructed_eq_of_admissibleReplacementWords
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (pieces : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta + 1) →
      List Direction)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (starts endpoints :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → Point)
    (visits :
      Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (hposition : ∀ j,
      trajectory (reconstructedTerminalStepPath pieces words)
          (replacementWordStart
            (AppendixLocalTime.requiredTerminalCount scale profileDelta)
            pieces words j) = starts j)
    (hadmissible : ∀ j,
      AdmissibleReplacementWord (terminalOuterBoundary scale x)
        x (starts j) (endpoints j) (visits j) (words j))
    (hfinish : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      extractedEntrance
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale horizon x (j : ℕ) =
        replacementWordStart
          (AppendixLocalTime.requiredTerminalCount scale profileDelta)
          pieces words j)
    (hstart : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      extractedExit
          (trajectory (reconstructedTerminalStepPath pieces words))
          scale horizon x (j : ℕ) = replacementWordStop pieces words j) :
    terminalVisitVector (trajectory (reconstructedTerminalStepPath pieces words))
        scale horizon profileDelta x = visits := by
  rw [terminalVisitVector_reconstructed_eq_replacementWordVisitCounts
    scale horizon profileDelta x pieces words hfinish hstart]
  funext j
  rw [hposition j]
  exact (hadmissible j).2.1

end

end Erdos1165.TerminalVisitSpliceInvariance
