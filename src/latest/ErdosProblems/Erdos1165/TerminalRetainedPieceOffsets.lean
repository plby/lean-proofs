/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.TerminalVisitSpliceInvariance

/-!
# Retained-piece offsets in a terminal splice

Besides the replacement words, an `alternatingConcat` contains the retained
pieces of the compressed terminal skeleton.  This module gives their literal
start and stop offsets and proves that the corresponding substring, shifted
increment path, and translated trajectory are exactly those of the retained
piece.  These facts are purely finite-word identities and do not use any
clock or boundary assumptions.
-/

namespace Erdos1165.TerminalRetainedPieceOffsets

open TerminalSkeletonWords TerminalVisitSpliceInvariance
open MarkedBridgeFactorization TerminalSequentialVisitLaw

noncomputable section

/-! ## Coordinates of retained pieces -/

/-- The offset at which retained piece `j` begins in an alternating
concatenation. -/
def retainedPieceStart : (m : ℕ) →
    (Fin (m + 1) → List Direction) → TerminalSegmentWords m →
      Fin (m + 1) → ℕ
  | 0, _pieces, _words, _j => 0
  | m + 1, pieces, words, j =>
      Fin.cases 0
        (fun i ↦ (pieces 0).length + (words 0).length +
          retainedPieceStart m (fun k ↦ pieces k.succ)
            (fun k ↦ words k.succ) i) j

/-- The offset immediately after retained piece `j`. -/
def retainedPieceStop {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) : ℕ :=
  retainedPieceStart m pieces words j + (pieces j).length

@[simp] theorem retainedPieceStart_zero {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) :
    retainedPieceStart m pieces words 0 = 0 := by
  cases m <;> rfl

@[simp] theorem retainedPieceStart_succ {m : ℕ}
    (pieces : Fin (m + 2) → List Direction)
    (words : TerminalSegmentWords (m + 1)) (j : Fin (m + 1)) :
    retainedPieceStart (m + 1) pieces words j.succ =
      (pieces 0).length + (words 0).length +
        retainedPieceStart m (fun k ↦ pieces k.succ)
          (fun k ↦ words k.succ) j := by
  rfl

/-- The retained piece following replacement coordinate `j` begins exactly
where that replacement word stops. -/
theorem retainedPieceStart_succ_eq_replacementWordStop : ∀ {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m),
    retainedPieceStart m pieces words j.succ =
      replacementWordStop pieces words j := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      exact Fin.elim0 j
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · change (pieces 0).length + (words 0).length +
            retainedPieceStart m (fun k ↦ pieces k.succ)
              (fun k ↦ words k.succ) 0 =
          (pieces 0).length + (words 0).length
        rw [retainedPieceStart_zero]
        omega
      · simp only [retainedPieceStart, replacementWordStart, Fin.cases_succ,
          replacementWordStop]
        rw [ih (fun k ↦ pieces k.succ) (fun k ↦ words k.succ) i]
        simp only [replacementWordStop]
        omega

/-- Replacement coordinate `j` begins exactly where retained piece `j`
ends. -/
theorem retainedPieceStop_castSucc_eq_replacementWordStart : ∀ {m : ℕ}
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin m),
    retainedPieceStop pieces words j.castSucc =
      replacementWordStart m pieces words j := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      exact Fin.elim0 j
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp [retainedPieceStop, retainedPieceStart, replacementWordStart]
      · simp only [retainedPieceStop, retainedPieceStart,
          replacementWordStart, Fin.cases_succ]
        have hindex : (i.succ.castSucc : Fin (m + 2)) =
            (i.castSucc.succ : Fin (m + 2)) := by
          apply Fin.ext
          rfl
        rw [hindex, Fin.cases_succ]
        have hi := ih (fun k ↦ pieces k.succ) (fun k ↦ words k.succ) i
        unfold retainedPieceStop at hi
        change retainedPieceStart m (fun k ↦ pieces k.succ)
            (fun k ↦ words k.succ) i.castSucc +
              (pieces i.castSucc.succ).length =
            replacementWordStart m (fun k ↦ pieces k.succ)
              (fun k ↦ words k.succ) i at hi
        omega

/-! ## Retained pieces extracted from a timed skeleton -/

/-- The first retained piece is the increment slice from the extraction base
to the first entrance time. -/
@[simp] theorem complementaryPieces_zero
    {m : ℕ} (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (m + 1) → ℕ) :
    complementaryPieces (m + 1) omega base horizon entrance exit 0 =
      incrementSlice omega base (entrance 0) := by
  rfl

@[simp] theorem complementaryPieces_zero_length
    {m : ℕ} (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (m + 1) → ℕ) :
    (complementaryPieces (m + 1) omega base horizon entrance exit 0).length =
      entrance 0 - base := by
  simp

/-- Every non-final retained piece is the literal increment slice from one
removed word's exit to the next removed word's entrance.  The indexing by
`Fin (n+1)` makes the existence of that next entrance intrinsic. -/
theorem complementaryPieces_between : ∀ (n : ℕ)
    (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (n + 2) → ℕ) (j : Fin (n + 1)),
    complementaryPieces (n + 2) omega base horizon entrance exit
        j.castSucc.succ =
      incrementSlice omega (exit j.castSucc) (entrance j.succ) := by
  intro n
  induction n with
  | zero =>
      intro omega base horizon entrance exit j
      have hj : j = 0 := by
        apply Fin.ext
        omega
      subst j
      rfl
  | succ n ih =>
      intro omega base horizon entrance exit j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · rfl
      · change complementaryPieces (n + 2) omega (exit 0) horizon
            (fun k ↦ entrance k.succ) (fun k ↦ exit k.succ)
              i.castSucc.succ =
          incrementSlice omega (exit i.succ.castSucc) (entrance i.succ.succ)
        have hi := ih omega (exit 0) horizon
          (fun k ↦ entrance k.succ) (fun k ↦ exit k.succ) i
        have hindex : (i.succ.castSucc : Fin (n + 3)) =
            (i.castSucc.succ : Fin (n + 3)) := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hi

@[simp] theorem complementaryPieces_between_length
    (n : ℕ) (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (n + 2) → ℕ) (j : Fin (n + 1)) :
    (complementaryPieces (n + 2) omega base horizon entrance exit
        j.castSucc.succ).length = entrance j.succ - exit j.castSucc := by
  rw [complementaryPieces_between]
  exact incrementSlice_length _ _ _

/-- The final retained piece is the increment slice from the last removed
word's exit through the extraction horizon. -/
theorem complementaryPieces_last : ∀ (n : ℕ)
    (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (n + 1) → ℕ),
    complementaryPieces (n + 1) omega base horizon entrance exit
        (Fin.last (n + 1)) =
      incrementSlice omega (exit (Fin.last n)) horizon := by
  intro n
  induction n with
  | zero =>
      intro omega base horizon entrance exit
      rfl
  | succ n ih =>
      intro omega base horizon entrance exit
      change complementaryPieces (n + 1) omega (exit 0) horizon
            (fun k ↦ entrance k.succ) (fun k ↦ exit k.succ)
              (Fin.last (n + 1)) =
          incrementSlice omega (exit (Fin.last (n + 1))) horizon
      have hlast := ih omega (exit 0) horizon
        (fun k ↦ entrance k.succ) (fun k ↦ exit k.succ)
      have hindex : ((Fin.last n).succ : Fin (n + 2)) =
          Fin.last (n + 1) := by
        apply Fin.ext
        simp
      rw [hindex] at hlast
      exact hlast

@[simp] theorem complementaryPieces_last_length
    (n : ℕ) (omega : StepPath) (base horizon : ℕ)
    (entrance exit : Fin (n + 1) → ℕ) :
    (complementaryPieces (n + 1) omega base horizon entrance exit
        (Fin.last (n + 1))).length = horizon - exit (Fin.last n) := by
  rw [complementaryPieces_last]
  exact incrementSlice_length _ _ _

/-- The stop of the final retained piece is the end of the complete
alternating concatenation. -/
theorem retainedPieceStop_last_eq_alternatingConcat_length : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m),
    retainedPieceStop pieces words (Fin.last m) =
      (alternatingConcat m pieces words).length := by
  intro m
  induction m with
  | zero =>
      intro pieces words
      simp [retainedPieceStop, retainedPieceStart, alternatingConcat]
  | succ m ih =>
      intro pieces words
      simp only [retainedPieceStop, retainedPieceStart, alternatingConcat,
        List.length_append]
      change (pieces 0).length + (words 0).length +
            retainedPieceStart m (fun k ↦ pieces k.succ)
              (fun k ↦ words k.succ) (Fin.last m) +
            (pieces (Fin.last (m + 1))).length =
          (pieces 0).length + (words 0).length +
            (alternatingConcat m (fun k ↦ pieces k.succ)
              (fun k ↦ words k.succ)).length
      have htail := ih (fun k ↦ pieces k.succ) (fun k ↦ words k.succ)
      unfold retainedPieceStop at htail
      have hindex : ((Fin.last m).succ : Fin (m + 2)) = Fin.last (m + 1) := by
        apply Fin.ext
        simp
      change retainedPieceStart m (fun k ↦ pieces k.succ)
          (fun k ↦ words k.succ) (Fin.last m) +
            (pieces (Fin.last m).succ).length =
          (alternatingConcat m (fun k ↦ pieces k.succ)
            (fun k ↦ words k.succ)).length at htail
      rw [hindex] at htail
      omega


/-- Dropping to a retained-piece start exposes that piece as the literal
prefix of the remaining concatenation. -/
theorem alternatingConcat_drop_retainedPieceStart : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)),
    ∃ suffix,
      (alternatingConcat m pieces words).drop
          (retainedPieceStart m pieces words j) =
        pieces j ++ suffix := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      refine ⟨[], ?_⟩
      have hj : j = 0 := by
        apply Fin.ext
        omega
      subst j
      simp [alternatingConcat, retainedPieceStart]
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · refine ⟨words 0 ++
            alternatingConcat m (fun k ↦ pieces k.succ)
              (fun k ↦ words k.succ), ?_⟩
        simp [alternatingConcat, retainedPieceStart]
      · obtain ⟨suffix, hsuffix⟩ := ih (fun k ↦ pieces k.succ)
          (fun k ↦ words k.succ) i
        refine ⟨suffix, ?_⟩
        calc
          (alternatingConcat (m + 1) pieces words).drop
              (retainedPieceStart (m + 1) pieces words i.succ) =
              (alternatingConcat m (fun k ↦ pieces k.succ)
                (fun k ↦ words k.succ)).drop
                  (retainedPieceStart m (fun k ↦ pieces k.succ)
                    (fun k ↦ words k.succ) i) := by
                      simp only [alternatingConcat, retainedPieceStart,
                        Fin.cases_succ]
                      rw [← List.drop_drop]
                      simp
          _ = pieces i.succ ++ suffix := hsuffix

/-- The retained piece is the exact substring at its recorded offset. -/
theorem alternatingConcat_drop_take_retainedPiece
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    ((alternatingConcat m pieces words).drop
        (retainedPieceStart m pieces words j)).take (pieces j).length =
      pieces j := by
  obtain ⟨suffix, hsuffix⟩ :=
    alternatingConcat_drop_retainedPieceStart m pieces words j
  rw [hsuffix]
  simp

theorem retainedPieceStart_le_alternatingConcat_length
    : ∀ {m : ℕ} (pieces : Fin (m + 1) → List Direction)
      (words : TerminalSegmentWords m) (j : Fin (m + 1)),
      retainedPieceStart m pieces words j ≤
        (alternatingConcat m pieces words).length := by
  intro m
  induction m with
  | zero =>
      intro pieces words j
      simp [retainedPieceStart, alternatingConcat]
  | succ m ih =>
      intro pieces words j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp [retainedPieceStart, alternatingConcat]
      · have htail := ih (fun k ↦ pieces k.succ) (fun k ↦ words k.succ) i
        simp only [retainedPieceStart, Fin.cases_succ, alternatingConcat,
          List.length_append]
        omega

theorem retainedPieceStop_le_alternatingConcat_length
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    retainedPieceStop pieces words j ≤
      (alternatingConcat m pieces words).length := by
  obtain ⟨suffix, hsuffix⟩ :=
    alternatingConcat_drop_retainedPieceStart m pieces words j
  have hlength := congrArg List.length hsuffix
  simp only [List.length_drop, List.length_append] at hlength
  have hstart := retainedPieceStart_le_alternatingConcat_length pieces words j
  unfold retainedPieceStop
  omega

@[simp] theorem retainedPieceStop_sub_start
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    retainedPieceStop pieces words j -
        retainedPieceStart m pieces words j = (pieces j).length := by
  simp [retainedPieceStop]

/-! ## Shifted reconstructed paths -/

/-- Shifting the reconstructed path to a retained-piece start has precisely
that piece as its stopped prefix. -/
theorem shift_reconstructed_mem_retainedPieceCylinder
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    shiftSteps (retainedPieceStart m pieces words j)
        (reconstructedTerminalStepPath pieces words) ∈
      stoppedWordCylinder (stoppedWordOfList (pieces j)) := by
  let full := alternatingConcat m pieces words
  let start := retainedPieceStart m pieces words j
  obtain ⟨suffix, hsuffix⟩ :=
    alternatingConcat_drop_retainedPieceStart m pieces words j
  have hstop : start + (pieces j).length ≤ full.length := by
    simpa [full, start, retainedPieceStop] using
      retainedPieceStop_le_alternatingConcat_length pieces words j
  change stepPrefix (pieces j).length
      (shiftSteps start (extendStoppedWord (stoppedWordOfList full))) =
        (stoppedWordOfList (pieces j)).2
  funext q
  have hqfull : start + (q : ℕ) < full.length := by omega
  have hqdrop : (q : ℕ) < (full.drop start).length := by
    simp only [List.length_drop]
    omega
  have hqpiece : (q : ℕ) < (pieces j).length := q.isLt
  change extendStoppedWord (stoppedWordOfList full) (start + q) =
    (pieces j).get q
  have hqfull' : start + (q : ℕ) < (stoppedWordOfList full).1 := hqfull
  rw [extendStoppedWord, dif_pos hqfull']
  change full.get ⟨start + q, hqfull⟩ = (pieces j).get q
  rw [List.get_eq_getElem, List.get_eq_getElem]
  have hsuffix' : full.drop start = pieces j ++ suffix := by
    simpa [full, start] using hsuffix
  have hopt := congrArg (fun l : List Direction ↦ l[(q : ℕ)]?) hsuffix'
  simp only [List.getElem?_eq_getElem hqdrop, List.getElem?_append,
    if_pos hqpiece, List.getElem?_eq_getElem hqpiece] at hopt
  have hdropPiece : (full.drop start)[q] = (pieces j)[q] :=
    Option.some.inj hopt
  exact (List.getElem_drop (xs := full) (i := start) (j := q)).symm.trans
    hdropPiece

/-- The increment slice between retained-piece offsets is the retained piece
itself. -/
theorem incrementSlice_reconstructed_retainedPiece
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    incrementSlice (reconstructedTerminalStepPath pieces words)
        (retainedPieceStart m pieces words j)
        (retainedPieceStop pieces words j) = pieces j := by
  let start := retainedPieceStart m pieces words j
  have hmem := shift_reconstructed_mem_retainedPieceCylinder pieces words j
  apply List.ext_get
  · simp [incrementSlice, retainedPieceStop]
  · intro q hq hq'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [incrementSlice, List.getElem_ofFn]
    have hqpiece : q < (stoppedWordOfList (pieces j)).1 := by
      simpa [stoppedWordOfList] using hq'
    have hstep := congrFun hmem ⟨q, hqpiece⟩
    simpa only [stepPrefix, shiftSteps, start, stoppedWordOfList,
      List.get_eq_getElem] using hstep

/-! ## Position translation along a retained piece -/

/-- At every time within a retained piece, the global reconstructed position
is the local retained-piece walk translated by the position at the piece's
start. -/
theorem trajectory_reconstructed_along_retainedPiece
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1))
    {q : ℕ} (hq : q ≤ (pieces j).length) :
    trajectory (reconstructedTerminalStepPath pieces words)
        (retainedPieceStart m pieces words j + q) =
      PlanarPotential.trajectoryFrom
        (trajectory (reconstructedTerminalStepPath pieces words)
          (retainedPieceStart m pieces words j))
        (extendStoppedWord (stoppedWordOfList (pieces j))) q := by
  rw [← trajectoryFrom_shiftSteps_eq]
  exact trajectoryFrom_eq_extendStoppedWord_of_mem
    (shift_reconstructed_mem_retainedPieceCylinder pieces words j) _ hq

/-- Endpoint form of `trajectory_reconstructed_along_retainedPiece`. -/
theorem trajectory_reconstructed_retainedPieceStop
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (j : Fin (m + 1)) :
    trajectory (reconstructedTerminalStepPath pieces words)
        (retainedPieceStop pieces words j) =
      PlanarPotential.trajectoryFrom
        (trajectory (reconstructedTerminalStepPath pieces words)
          (retainedPieceStart m pieces words j))
        (extendStoppedWord (stoppedWordOfList (pieces j)))
        (pieces j).length := by
  simpa only [retainedPieceStop] using
    trajectory_reconstructed_along_retainedPiece pieces words j le_rfl

/-! ## Recovery of the complementary skeleton -/

/-- Recovery of the initial retained piece from its replacement-word entrance
offset. -/
theorem complementaryPieces_reconstructed_zero_of_entrance
    {m : ℕ} (pieces : Fin (m + 2) → List Direction)
    (words : TerminalSegmentWords (m + 1))
    (entrance exit : Fin (m + 1) → ℕ)
    (hentrance : entrance 0 =
      replacementWordStart (m + 1) pieces words 0) :
    complementaryPieces (m + 1)
        (reconstructedTerminalStepPath pieces words) 0
        (alternatingConcat (m + 1) pieces words).length entrance exit 0 =
      pieces 0 := by
  rw [complementaryPieces_zero, hentrance,
    ← retainedPieceStop_castSucc_eq_replacementWordStart pieces words 0]
  have hindex : ((0 : Fin (m + 1)).castSucc : Fin (m + 2)) = 0 := by
    apply Fin.ext
    rfl
  rw [hindex]
  simpa only [retainedPieceStart_zero] using
    incrementSlice_reconstructed_retainedPiece pieces words (0 : Fin (m + 2))

/-- Recovery of every retained piece lying strictly between two replacement
words. -/
theorem complementaryPieces_reconstructed_between_of_offsets
    (n : ℕ) (pieces : Fin (n + 3) → List Direction)
    (words : TerminalSegmentWords (n + 2))
    (entrance exit : Fin (n + 2) → ℕ)
    (hentrance : ∀ j, entrance j =
      replacementWordStart (n + 2) pieces words j)
    (hexit : ∀ j, exit j = replacementWordStop pieces words j)
    (j : Fin (n + 1)) :
    complementaryPieces (n + 2)
        (reconstructedTerminalStepPath pieces words) 0
        (alternatingConcat (n + 2) pieces words).length entrance exit
          j.castSucc.succ = pieces j.castSucc.succ := by
  rw [complementaryPieces_between, hexit j.castSucc, hentrance j.succ]
  have hstart := retainedPieceStart_succ_eq_replacementWordStop
    pieces words j.castSucc
  have hstop := retainedPieceStop_castSucc_eq_replacementWordStart
    pieces words j.succ
  have hindex : (j.succ.castSucc : Fin (n + 3)) =
      (j.castSucc.succ : Fin (n + 3)) := by
    apply Fin.ext
    rfl
  rw [hindex] at hstop
  rw [← hstart, ← hstop]
  exact incrementSlice_reconstructed_retainedPiece pieces words
    j.castSucc.succ

/-- Recovery of the final retained suffix from the last replacement-word exit
offset and the intrinsic concatenation horizon. -/
theorem complementaryPieces_reconstructed_last_of_exit
    (n : ℕ) (pieces : Fin (n + 2) → List Direction)
    (words : TerminalSegmentWords (n + 1))
    (entrance exit : Fin (n + 1) → ℕ)
    (hexit : exit (Fin.last n) =
      replacementWordStop pieces words (Fin.last n)) :
    complementaryPieces (n + 1)
        (reconstructedTerminalStepPath pieces words) 0
        (alternatingConcat (n + 1) pieces words).length entrance exit
          (Fin.last (n + 1)) = pieces (Fin.last (n + 1)) := by
  rw [complementaryPieces_last, hexit]
  have hstart := retainedPieceStart_succ_eq_replacementWordStop
    pieces words (Fin.last n)
  have hindex : ((Fin.last n).succ : Fin (n + 2)) =
      Fin.last (n + 1) := by
    apply Fin.ext
    simp
  rw [hindex] at hstart
  have hstop := retainedPieceStop_last_eq_alternatingConcat_length
    (n + 1) pieces words
  rw [← hstart, ← hstop]
  exact incrementSlice_reconstructed_retainedPiece pieces words
    (Fin.last (n + 1))

/-- If all entrance and exit clocks equal the splice offsets, extracting the
complementary pieces from the reconstructed terminal path recovers the entire
retained-piece vector. -/
theorem complementaryPieces_reconstructed_eq_of_replacementOffsets
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (entrance exit : Fin m → ℕ)
    (hentrance : ∀ j, entrance j =
      replacementWordStart m pieces words j)
    (hexit : ∀ j, exit j = replacementWordStop pieces words j) :
    complementaryPieces m (reconstructedTerminalStepPath pieces words) 0
        (alternatingConcat m pieces words).length entrance exit = pieces := by
  funext k
  cases m with
  | zero =>
      have hk : k = 0 := by
        apply Fin.ext
        omega
      subst k
      change incrementSlice (reconstructedTerminalStepPath pieces words) 0
          (alternatingConcat 0 pieces words).length = pieces 0
      have hstop := retainedPieceStop_last_eq_alternatingConcat_length
        0 pieces words
      rw [← hstop]
      have hindex : (Fin.last 0 : Fin 1) = 0 := by
        apply Fin.ext
        rfl
      rw [hindex]
      simpa only [retainedPieceStart_zero] using
        incrementSlice_reconstructed_retainedPiece pieces words (0 : Fin 1)
  | succ n =>
      refine Fin.cases ?_ (fun i ↦ ?_) k
      · exact complementaryPieces_reconstructed_zero_of_entrance
          pieces words entrance exit (hentrance 0)
      · cases n with
        | zero =>
            have hi : i = 0 := by
              apply Fin.ext
              omega
            subst i
            simpa using complementaryPieces_reconstructed_last_of_exit 0
              pieces words entrance exit (hexit 0)
        | succ n =>
            refine Fin.lastCases ?_ (fun j ↦ ?_) i
            · simpa using complementaryPieces_reconstructed_last_of_exit
                (n + 1) pieces words entrance exit (hexit (Fin.last (n + 1)))
            · simpa only using
                complementaryPieces_reconstructed_between_of_offsets n
                  pieces words entrance exit hentrance hexit j

/-- Bundled code recovery: once the reconstructed horizon, splice clocks,
and endpoint arrays agree, compression returns the prescribed terminal
skeleton code exactly. -/
theorem compressTimedSkeleton_reconstructed_eq_of_replacementOffsets
    {m : ℕ} (pieces : Fin (m + 1) → List Direction)
    (words : TerminalSegmentWords m) (t : TimedTerminalSkeleton m)
    (entrancePoint exitPoint : Fin m → Point)
    (hhorizon : t.horizon = (alternatingConcat m pieces words).length)
    (hentrance : ∀ j, t.entrance j =
      replacementWordStart m pieces words j)
    (hexit : ∀ j, t.exit j = replacementWordStop pieces words j)
    (hentrancePoint : t.entrancePoint = entrancePoint)
    (hexitPoint : t.exitPoint = exitPoint) :
    compressTimedSkeleton (reconstructedTerminalStepPath pieces words) t =
      (⟨pieces⟩, (entrancePoint, exitPoint)) := by
  apply Prod.ext
  · apply TerminalSkeletonData.ext
    dsimp only [compressTimedSkeleton]
    rw [hhorizon]
    exact complementaryPieces_reconstructed_eq_of_replacementOffsets
      pieces words t.entrance t.exit hentrance hexit
  · apply Prod.ext
    · exact hentrancePoint
    · exact hexitPoint

end

end Erdos1165.TerminalRetainedPieceOffsets
