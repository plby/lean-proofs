/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.TerminalSpliceProfileGeometry
import ErdosProblems.Erdos1165.TerminalBoundaryScan
import ErdosProblems.Erdos1165.TerminalExtractedBridgeCodes
import ErdosProblems.Erdos1165.TerminalPacketEndpointAlignment
import ErdosProblems.Erdos1165.TerminalRetainedHitSplice

/-!
# Excursion-profile clocks under terminal word splicing

The completed annular-excursion count is the output of a two-state scan:
first seek the outer boundary, then seek the inner boundary and increment the
count, and repeat.  This file records the compositional word-level part of
the splice argument.  It is deliberately phrased for arbitrary finite words,
so the two replacements may have different lengths.
-/

open Set

namespace Erdos1165.TerminalProfileClockEquivalence

open ThickPoint TerminalSkeletonWords TerminalVisitSpliceInvariance
open TerminalGlobalExitSplice TerminalSpliceProfileGeometry
open TerminalBoundaryScan
open TerminalSequentialVisitLaw TerminalExcursionPathwise AnnularProfileClocks
open TerminalExtractedBridgeCodes TerminalPacketEndpointAlignment
open TerminalRetainedPieceOffsets MarkedBridgeFactorization
open TerminalRetainedHitSplice TerminalClockSplice

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Local name for the deterministic boundary scanner state. -/
abbrev BoundaryScanState := TerminalBoundaryScan.BoundaryScanState

/-- Process one visited vertex.  `true` means that the next relevant vertex
is on the outer boundary; `false` means that it is on the inner boundary. -/
def visitBoundary (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (state : BoundaryScanState) (z : Point) : BoundaryScanState :=
  if state.seekingOuter then
    if z ∈ outer then ⟨false, state.completed⟩ else state
  else
    if z ∈ inner then ⟨true, state.completed + 1⟩ else state

/-- Fold a direction word, processing the newly reached vertex after every
increment.  The vertex at time zero is intentionally not processed here;
this makes concatenation literal. -/
def scanWordFrom (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction) :
    Point × BoundaryScanState :=
  word.foldl (fun acc d ↦
    let next := Annulus.neighbor acc.1 d
    (next, visitBoundary outer inner acc.2 next)) (start, state)

@[simp] theorem scanWordFrom_nil (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) :
    scanWordFrom outer inner start state [] = (start, state) := by
  rfl

theorem scanWordFrom_append (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState)
    (u v : List Direction) :
    scanWordFrom outer inner start state (u ++ v) =
      scanWordFrom outer inner
        (scanWordFrom outer inner start state u).1
        (scanWordFrom outer inner start state u).2 v := by
  simp [scanWordFrom, List.foldl_append]

/-- Scanning a word reaches its ordinary finite-word endpoint. -/
theorem scanWordFrom_fst (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction) :
    (scanWordFrom outer inner start state word).1 =
      word.foldl Annulus.neighbor start := by
  induction word generalizing start state with
  | nil => rfl
  | cons d word ih =>
      simp only [scanWordFrom, List.foldl_cons]
      exact ih (Annulus.neighbor start d)
        (visitBoundary outer inner state (Annulus.neighbor start d))

theorem visitBoundary_eq_terminalBoundaryScan_visit
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (state : BoundaryScanState) (z : Point) :
    visitBoundary outer inner state z =
      TerminalBoundaryScan.visit outer inner state z := by
  cases state with
  | mk seeking completed =>
      cases seeking <;>
        simp [visitBoundary, TerminalBoundaryScan.visit]

/-- Identification with the shared scanner implementation. -/
theorem scanWordFrom_eq_terminalBoundaryScan_scanDirections
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction) :
    scanWordFrom outer inner start state word =
      TerminalBoundaryScan.scanDirections outer inner start state word := by
  induction word generalizing start state with
  | nil => rfl
  | cons d word ih =>
      simp only [scanWordFrom, List.foldl_cons,
        TerminalBoundaryScan.scanDirections_cons]
      rw [visitBoundary_eq_terminalBoundaryScan_visit]
      exact ih (Annulus.neighbor start d)
        (TerminalBoundaryScan.visit outer inner state
          (Annulus.neighbor start d))

@[simp] theorem visitBoundary_eq_of_avoids (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (state : BoundaryScanState) {z : Point}
    (houter : z ∉ outer) (hinner : z ∉ inner) :
    visitBoundary outer inner state z = state := by
  cases state with
  | mk seeking completed =>
      cases seeking <;> simp [visitBoundary, houter, hinner]

/-- A finite word whose positive-time vertices avoid both boundaries has no
effect on the scanner state. -/
theorem scanWordFrom_eq_of_wordWalk_avoids
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction)
    (havoid : ∀ q, 0 < q → q ≤ word.length →
      wordWalk start word q ∉ outer ∧ wordWalk start word q ∉ inner) :
    scanWordFrom outer inner start state word =
      (wordWalk start word word.length, state) := by
  induction word generalizing start state with
  | nil => simp
  | cons d word ih =>
      let next := Annulus.neighbor start d
      have hnext : next ∉ outer ∧ next ∉ inner := by
        simpa [next, wordWalk] using havoid 1 (by omega) (by simp)
      have htail : ∀ q, 0 < q → q ≤ word.length →
          wordWalk next word q ∉ outer ∧ wordWalk next word q ∉ inner := by
        intro q hqpos hq
        simpa [next, wordWalk] using havoid (q + 1) (by omega) (by simp; omega)
      simp only [scanWordFrom, List.foldl_cons]
      rw [visitBoundary_eq_of_avoids outer inner state hnext.1 hnext.2]
      have hih := ih next state htail
      simpa [scanWordFrom, next, wordWalk] using hih

/-- A word which avoids both boundaries until its last vertex, and whose
last vertex lies on the inner but not the outer boundary, has the canonical
single-inner-hit effect. -/
theorem scanWordFrom_eq_of_first_inner_at_end
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction)
    (hne : word ≠ [])
    (havoid : ∀ q, 0 < q → q < word.length →
      wordWalk start word q ∉ outer ∧ wordWalk start word q ∉ inner)
    (houterEnd : wordWalk start word word.length ∉ outer)
    (hinnerEnd : wordWalk start word word.length ∈ inner) :
    (scanWordFrom outer inner start state word).2 =
      if state.seekingOuter then state
      else ⟨true, state.completed + 1⟩ := by
  induction word generalizing start state with
  | nil => exact (hne rfl).elim
  | cons d word ih =>
      let next := Annulus.neighbor start d
      cases word with
      | nil =>
          have hend : wordWalk start [d] [d].length = next := by
            simp [wordWalk, next]
          rw [hend] at houterEnd hinnerEnd
          cases state with
          | mk seeking completed =>
              cases seeking <;>
                simp only [scanWordFrom, List.foldl_cons, List.foldl_nil,
                  Prod.snd] <;>
                rw [show Annulus.neighbor start d = next by rfl] <;>
                simp [visitBoundary, houterEnd, hinnerEnd]
      | cons e tail =>
          have hnext : next ∉ outer ∧ next ∉ inner := by
            simpa [next, wordWalk] using havoid 1 (by omega) (by simp)
          have htailAvoid : ∀ q, 0 < q → q < (e :: tail).length →
              wordWalk next (e :: tail) q ∉ outer ∧
                wordWalk next (e :: tail) q ∉ inner := by
            intro q hqpos hq
            simpa [next, wordWalk] using
              havoid (q + 1) (by omega) (by simp at hq ⊢; omega)
          have htailOuter :
              wordWalk next (e :: tail) (e :: tail).length ∉ outer := by
            simpa [next, wordWalk] using houterEnd
          have htailInner :
              wordWalk next (e :: tail) (e :: tail).length ∈ inner := by
            simpa [next, wordWalk] using hinnerEnd
          simp only [scanWordFrom, List.foldl_cons]
          rw [visitBoundary_eq_of_avoids outer inner state hnext.1 hnext.2]
          exact ih next state (by simp) htailAvoid htailOuter htailInner

/-- While the scanner is seeking the outer boundary, arbitrary inner visits
are irrelevant.  Thus a word which first reaches the outer boundary at its
last vertex has a duration-independent state effect. -/
theorem scanWordFrom_seekingOuter_eq_of_first_outer_at_end
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (completed : ℕ) (word : List Direction)
    (hne : word ≠ [])
    (havoidOuter : ∀ q, 0 < q → q < word.length →
      wordWalk start word q ∉ outer)
    (houterEnd : wordWalk start word word.length ∈ outer) :
    (scanWordFrom outer inner start ⟨true, completed⟩ word).2 =
      ⟨false, completed⟩ := by
  induction word generalizing start with
  | nil => exact (hne rfl).elim
  | cons d word ih =>
      let next := Annulus.neighbor start d
      cases word with
      | nil =>
          have hend : wordWalk start [d] [d].length = next := by
            simp [wordWalk, next]
          rw [hend] at houterEnd
          change visitBoundary outer inner ⟨true, completed⟩ next = _
          simp [visitBoundary, houterEnd]
      | cons e tail =>
          have hnext : next ∉ outer := by
            simpa [next, wordWalk] using havoidOuter 1 (by omega) (by simp)
          have htailAvoid : ∀ q, 0 < q → q < (e :: tail).length →
              wordWalk next (e :: tail) q ∉ outer := by
            intro q hqpos hq
            simpa [next, wordWalk] using
              havoidOuter (q + 1) (by omega) (by simp at hq ⊢; omega)
          have htailEnd :
              wordWalk next (e :: tail) (e :: tail).length ∈ outer := by
            simpa [next, wordWalk] using houterEnd
          simp only [scanWordFrom, List.foldl_cons]
          have hvisit : visitBoundary outer inner
              ⟨true, completed⟩ next = ⟨true, completed⟩ := by
            simp [visitBoundary, hnext]
          rw [hvisit]
          exact ih next (by simp) htailAvoid htailEnd

/-- `wordWalk` is the finite-prefix presentation of the stopped extension of
the same direction list. -/
theorem wordWalk_eq_trajectoryFrom_extendStoppedWord
    (start : Point) (word : List Direction) {q : ℕ} (hq : q ≤ word.length) :
    wordWalk start word q =
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord (stoppedWordOfList word)) q := by
  have h := wordPosition_ofFn_stepPrefix start
    (extendStoppedWord (stoppedWordOfList word)) hq
  have hp : List.ofFn (stepPrefix word.length
      (extendStoppedWord (stoppedWordOfList word))) = word := by
    change List.ofFn (stepPrefix (stoppedWordOfList word).1
      (extendStoppedWord (stoppedWordOfList word))) = word
    rw [stepPrefix_extendStoppedWord]
    simp [stoppedWordOfList]
  simpa only [wordWalk, hp] using h

/-- If the last (positive-time) vertex of a word is on the inner boundary
and not on the outer boundary, then the scanner leaves the word seeking the
outer boundary, independently of the incoming state. -/
theorem scanWordFrom_seekingOuter_of_nonempty_endpoint_inner
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction)
    (hne : word ≠ [])
    (houter : wordWalk start word word.length ∉ outer)
    (hinner : wordWalk start word word.length ∈ inner) :
    (scanWordFrom outer inner start state word).2.seekingOuter = true := by
  induction word generalizing start state with
  | nil => exact (hne rfl).elim
  | cons d word ih =>
      cases word with
      | nil =>
          have hend : wordWalk start [d] [d].length =
              Annulus.neighbor start d := by simp [wordWalk]
          rw [hend] at houter hinner
          cases state with
          | mk seeking completed =>
              cases seeking <;>
                simp [scanWordFrom, visitBoundary, houter, hinner]
      | cons e tail =>
          simp only [scanWordFrom, List.foldl_cons]
          apply ih (Annulus.neighbor start d)
              (visitBoundary outer inner state (Annulus.neighbor start d))
          · simp
          · simpa [wordWalk] using houter
          · simpa [wordWalk] using hinner

/-! ## Separation of consecutive profile boundaries -/

lemma regular_profile_radius_add_one_le_prev
    {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) :
    scaleRadius n (k + 1) + 1 ≤ scaleRadius n k := by
  rw [scaleRadius_of_le hk, scaleRadius_of_le hk.le]
  unfold regularRadius
  have hkcast : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hdiff : 0 ≤ (n : ℝ) - ((k + 1 : ℕ) : ℝ) := by linarith
  have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
    simpa using Real.exp_le_exp.mpr hdiff
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 9 := one_le_pow₀ hnone
  have hr : (1 : ℝ) ≤
      Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 :=
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 :=
        mul_le_mul hexp hpow (by norm_num) (by positivity)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp 1]
  have hrewrite : (n : ℝ) - (k : ℝ) =
      ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) + 1 := by
    push_cast
    ring
  rw [hrewrite, Real.exp_add]
  change Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 + 1 ≤
    Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * Real.exp 1 * (n : ℝ) ^ 9
  have hnonneg : 0 ≤
      Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 := by
    positivity
  have htwice : 2 *
      (Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9) ≤
      Real.exp 1 *
        (Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9) :=
    mul_le_mul_of_nonneg_right he hnonneg
  calc
    Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 + 1
        ≤ 2 * (Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 9) := by
          linarith
    _ ≤ Real.exp ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * Real.exp 1 *
        (n : ℝ) ^ 9 := by nlinarith

lemma terminal_profile_radius_add_one_le
    {n : ℕ} (hn : 2 ≤ n) :
    scaleRadius n (n + 1) + 1 ≤ scaleRadius n n := by
  rw [scaleRadius_succ_self, scaleRadius_of_le le_rfl, regularRadius_self]
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 :=
    one_le_pow₀ (by linarith)
  have h3 : (2 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      (2 : ℝ) ≤ 2 ^ 3 := by norm_num
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hnreal 3
  rw [show (n : ℝ) ^ 9 = (n : ℝ) ^ 6 * (n : ℝ) ^ 3 by ring]
  nlinarith [mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 6)]

/-- Adjacent HLOZ profile boundaries are disjoint at every nondegenerate
scale. -/
theorem profileBoundaries_disjoint
    {n : ℕ} (hn : 2 ≤ n) (x : Point)
    (k : Fin (n + 2)) (hk : (k : ℕ) ≠ 0) :
    Disjoint
      (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
      (discBoundary x (scaleRadius n (k : ℕ))) := by
  apply Set.disjoint_left.2
  intro z hzOuter hzInner
  apply (not_mem_discBoundary_of_mem_disc_of_add_one_le hzInner.1 ?_) hzOuter
  by_cases hterminal : (k : ℕ) = n + 1
  · rw [hterminal]
    simpa using terminal_profile_radius_add_one_le hn
  · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
    have hklt : (k : ℕ) < n + 1 := by omega
    have hpred : (k : ℕ) - 1 < n := by omega
    have hs := regular_profile_radius_add_one_le_prev hn hpred
    simpa [Nat.sub_add_cancel hkpos] using hs

theorem terminalBoundaries_disjoint
    {n : ℕ} (hn : 2 ≤ n) (x : Point) :
    Disjoint (terminalOuterBoundary n x) (terminalInnerBoundary n x) := by
  apply Set.disjoint_left.2
  intro z hzOuter hzInner
  exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hzInner.1
    (terminal_profile_radius_add_one_le hn)) hzOuter

/-- A first hit from a point on a disjoint inner boundary has positive word
length. -/
theorem word_ne_nil_of_firstHit_from_disjoint_inner
    {outer inner : Set Point} {start : Point} {word : List Direction}
    (hdisjoint : Disjoint outer inner) (hstart : start ∈ inner)
    (hfirst : AbsoluteBoundaryFirstAt outer start
      (extendStoppedWord (stoppedWordOfList word)) word.length) :
    word ≠ [] := by
  intro hnil
  subst word
  have houter : start ∈ outer := by
    simpa using hfirst.1
  exact Set.disjoint_left.1 hdisjoint houter hstart

/-- Two terminal first-hit words are invisible to every strictly coarser
profile clock. -/
theorem scanWordFrom_eq_of_terminalFirstHits_of_lt
    {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) {x start : Point}
    (state : BoundaryScanState) (leftWord rightWord : List Direction)
    (hstart : start ∈ terminalInnerBoundary n x)
    (hleft : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList leftWord)) leftWord.length)
    (hright : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList rightWord)) rightWord.length)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state leftWord =
      scanWordFrom (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        start state rightWord := by
  have hleftAvoid : ∀ q, 0 < q → q ≤ leftWord.length →
      wordWalk start leftWord q ∉ profileOuterBoundary n k x ∧
      wordWalk start leftWord q ∉ profileInnerBoundary n k x := by
    intro q hqpos hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start leftWord hq]
    have hmem := trajectoryFrom_mem_terminalDisc_of_firstHit hn hstart hleft q hq
    exact ⟨terminalDisc_avoids_profileOuterBoundary_of_lt hn hk hmem,
      terminalDisc_avoids_profileInnerBoundary_of_lt hn hk hmem⟩
  have hrightAvoid : ∀ q, 0 < q → q ≤ rightWord.length →
      wordWalk start rightWord q ∉ profileOuterBoundary n k x ∧
      wordWalk start rightWord q ∉ profileInnerBoundary n k x := by
    intro q hqpos hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start rightWord hq]
    have hmem := trajectoryFrom_mem_terminalDisc_of_firstHit hn hstart hright q hq
    exact ⟨terminalDisc_avoids_profileOuterBoundary_of_lt hn hk hmem,
      terminalDisc_avoids_profileInnerBoundary_of_lt hn hk hmem⟩
  rw [scanWordFrom_eq_of_wordWalk_avoids _ _ start state leftWord hleftAvoid,
    scanWordFrom_eq_of_wordWalk_avoids _ _ start state rightWord hrightAvoid,
    hend]

/-- At profile level `n`, terminal first-hit words expose exactly their
common terminal-outer endpoint and nothing else. -/
theorem scanWordFrom_eq_of_terminalFirstHits_at_self
    {n : ℕ} (hn : 2 ≤ n) {x start : Point}
    (state : BoundaryScanState) (leftWord rightWord : List Direction)
    (hstart : start ∈ terminalInnerBoundary n x)
    (hleft : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList leftWord)) leftWord.length)
    (hright : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList rightWord)) rightWord.length)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (profileOuterBoundary n n x) (profileInnerBoundary n n x)
        start state leftWord =
      scanWordFrom (profileOuterBoundary n n x) (profileInnerBoundary n n x)
        start state rightWord := by
  have htermDisjoint : Disjoint (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) := by
    exact terminalBoundaries_disjoint hn x
  have hleftNe := word_ne_nil_of_firstHit_from_disjoint_inner
    htermDisjoint hstart hleft
  have hrightNe := word_ne_nil_of_firstHit_from_disjoint_inner
    htermDisjoint hstart hright
  have avoidOuter (word : List Direction)
      (hfirst : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
        (extendStoppedWord (stoppedWordOfList word)) word.length) :
      ∀ q ≤ word.length, wordWalk start word q ∉ profileOuterBoundary n n x := by
    intro q hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start word hq]
    have hn1 : 1 ≤ n := by omega
    have hmem := trajectoryFrom_mem_terminalDisc_of_firstHit hn1
      hstart hfirst q hq
    simpa [profileOuterBoundary] using
      terminalDisc_avoids_scaleBoundary_of_lt hn1
        (show n - 1 < n by omega) hmem
  have hleftAvoid : ∀ q, 0 < q → q < leftWord.length →
      wordWalk start leftWord q ∉ profileOuterBoundary n n x ∧
      wordWalk start leftWord q ∉ profileInnerBoundary n n x := by
    intro q hqpos hq
    refine ⟨avoidOuter leftWord hleft q hq.le, ?_⟩
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start leftWord hq.le]
    exact (terminalFirstHit_eq_profileInnerBoundary_at_self hleft).2 q hq
  have hrightAvoid : ∀ q, 0 < q → q < rightWord.length →
      wordWalk start rightWord q ∉ profileOuterBoundary n n x ∧
      wordWalk start rightWord q ∉ profileInnerBoundary n n x := by
    intro q hqpos hq
    refine ⟨avoidOuter rightWord hright q hq.le, ?_⟩
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start rightWord hq.le]
    exact (terminalFirstHit_eq_profileInnerBoundary_at_self hright).2 q hq
  have hleftInner : wordWalk start leftWord leftWord.length ∈
      profileInnerBoundary n n x := by
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start leftWord le_rfl]
    exact (terminalFirstHit_eq_profileInnerBoundary_at_self hleft).1
  have hrightInner : wordWalk start rightWord rightWord.length ∈
      profileInnerBoundary n n x := by
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start rightWord le_rfl]
    exact (terminalFirstHit_eq_profileInnerBoundary_at_self hright).1
  apply Prod.ext
  · simpa only [scanWordFrom_fst, wordWalk_length] using hend
  · rw [scanWordFrom_eq_of_first_inner_at_end _ _ start state leftWord
        hleftNe hleftAvoid (avoidOuter leftWord hleft _ le_rfl) hleftInner,
      scanWordFrom_eq_of_first_inner_at_end _ _ start state rightWord
        hrightNe hrightAvoid (avoidOuter rightWord hright _ le_rfl) hrightInner]

/-- At the terminal profile level, two inner-to-outer first-hit words have
the same effect whenever the incoming state is seeking the outer boundary. -/
theorem scanWordFrom_eq_of_terminalFirstHits_at_terminal
    {n : ℕ} (hn : 2 ≤ n) {x start : Point} (completed : ℕ)
    (leftWord rightWord : List Direction)
    (hstart : start ∈ terminalInnerBoundary n x)
    (hleft : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList leftWord)) leftWord.length)
    (hright : AbsoluteBoundaryFirstAt (terminalOuterBoundary n x) start
      (extendStoppedWord (stoppedWordOfList rightWord)) rightWord.length)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom (terminalOuterBoundary n x) (terminalInnerBoundary n x)
        start ⟨true, completed⟩ leftWord =
      scanWordFrom (terminalOuterBoundary n x) (terminalInnerBoundary n x)
        start ⟨true, completed⟩ rightWord := by
  have htermDisjoint : Disjoint (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) := by
    exact terminalBoundaries_disjoint hn x
  have hleftAvoid : ∀ q, 0 < q → q < leftWord.length →
      wordWalk start leftWord q ∉ terminalOuterBoundary n x := by
    intro q hqpos hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start leftWord hq.le]
    exact hleft.2 q hq
  have hrightAvoid : ∀ q, 0 < q → q < rightWord.length →
      wordWalk start rightWord q ∉ terminalOuterBoundary n x := by
    intro q hqpos hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start rightWord hq.le]
    exact hright.2 q hq
  have hleftEnd : wordWalk start leftWord leftWord.length ∈ terminalOuterBoundary n x := by
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start leftWord le_rfl]
    exact hleft.1
  have hrightEnd : wordWalk start rightWord rightWord.length ∈ terminalOuterBoundary n x := by
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord start rightWord le_rfl]
    exact hright.1
  apply Prod.ext
  · simpa only [scanWordFrom_fst, wordWalk_length] using hend
  · rw [scanWordFrom_seekingOuter_eq_of_first_outer_at_end _ _ start completed
        leftWord
        (word_ne_nil_of_firstHit_from_disjoint_inner htermDisjoint hstart hleft)
        hleftAvoid hleftEnd,
      scanWordFrom_seekingOuter_eq_of_first_outer_at_end _ _ start completed
        rightWord
        (word_ne_nil_of_firstHit_from_disjoint_inner htermDisjoint hstart hright)
        hrightAvoid hrightEnd]

/-! ## Compositional replacement -/

/-- If each pair of replacement words has the same scanner transformer, the
two alternating concatenations have the same transformer.  The retained
pieces are literally shared. -/
theorem scanWordFrom_alternatingConcat_eq_of_word_transform_eq :
    ∀ (m : ℕ) (outer inner : Set Point)
      [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
      (pieces : Fin (m + 1) → List Direction)
      (leftWords rightWords : TerminalSegmentWords m)
      (start : Point) (state : BoundaryScanState),
      (∀ (j : Fin m) (a : Point) (u : BoundaryScanState),
        scanWordFrom outer inner a u (leftWords j) =
          scanWordFrom outer inner a u (rightWords j)) →
      scanWordFrom outer inner start state
          (alternatingConcat m pieces leftWords) =
        scanWordFrom outer inner start state
          (alternatingConcat m pieces rightWords) := by
  intro m
  induction m with
  | zero =>
      intro outer inner _ _ pieces leftWords rightWords start state _hwords
      rfl
  | succ m ih =>
      intro outer inner _ _ pieces leftWords rightWords start state hwords
      rw [show alternatingConcat (m + 1) pieces leftWords =
          pieces 0 ++ leftWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ leftWords j.succ) by rfl,
        show alternatingConcat (m + 1) pieces rightWords =
          pieces 0 ++ rightWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ rightWords j.succ) by rfl,
        scanWordFrom_append, scanWordFrom_append,
        scanWordFrom_append, scanWordFrom_append]
      let afterPiece := scanWordFrom outer inner start state (pieces 0)
      have hzero := hwords (0 : Fin (m + 1)) afterPiece.1 afterPiece.2
      rw [show scanWordFrom outer inner
          (scanWordFrom outer inner start state (pieces 0)).1
          (scanWordFrom outer inner start state (pieces 0)).2 (leftWords 0) =
          scanWordFrom outer inner
          (scanWordFrom outer inner start state (pieces 0)).1
          (scanWordFrom outer inner start state (pieces 0)).2 (rightWords 0)
        from hzero]
      apply ih
      intro j a u
      exact hwords j.succ a u

/-- Endpoint data which makes the literal alternating concatenation a chain
of common retained pieces and endpoint-matched replacement words. -/
structure EndpointMatchedAlternatingGeometry (m : ℕ) (start : Point)
    (pieces : Fin (m + 1) → List Direction)
    (leftWords rightWords : TerminalSegmentWords m) where
  pieceStart : Fin (m + 1) → Point
  wordStart : Fin m → Point
  pieceStart_zero : pieceStart 0 = start
  retainedEndpoint : ∀ j : Fin m,
    (pieces j.castSucc).foldl Annulus.neighbor (pieceStart j.castSucc) =
      wordStart j
  leftWordEndpoint : ∀ j : Fin m,
    (leftWords j).foldl Annulus.neighbor (wordStart j) = pieceStart j.succ
  rightWordEndpoint : ∀ j : Fin m,
    (rightWords j).foldl Annulus.neighbor (wordStart j) = pieceStart j.succ

namespace EndpointMatchedAlternatingGeometry

/-- Delete the first retained-piece/word pair from endpoint geometry. -/
def tail {m : ℕ} {start : Point}
    {pieces : Fin (m + 2) → List Direction}
    {leftWords rightWords : TerminalSegmentWords (m + 1)}
    (geometry : EndpointMatchedAlternatingGeometry (m + 1) start
      pieces leftWords rightWords) :
    EndpointMatchedAlternatingGeometry m (geometry.pieceStart 1)
      (fun j ↦ pieces j.succ) (fun j ↦ leftWords j.succ)
      (fun j ↦ rightWords j.succ) where
  pieceStart := fun j ↦ geometry.pieceStart j.succ
  wordStart := fun j ↦ geometry.wordStart j.succ
  pieceStart_zero := rfl
  retainedEndpoint := fun j ↦ geometry.retainedEndpoint j.succ
  leftWordEndpoint := fun j ↦ geometry.leftWordEndpoint j.succ
  rightWordEndpoint := fun j ↦ geometry.rightWordEndpoint j.succ

end EndpointMatchedAlternatingGeometry

/-- Fixed-start version of alternating-concatenation congruence.  Unlike the
fully polymorphic theorem above, word-transformer equality is needed only at
the actual common start point of each replacement coordinate. -/
theorem scanWordFrom_alternatingConcat_eq_of_endpointGeometry :
    ∀ (m : ℕ) (outer inner : Set Point)
      [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
      (pieces : Fin (m + 1) → List Direction)
      (leftWords rightWords : TerminalSegmentWords m)
      (start : Point) (state : BoundaryScanState)
      (geometry : EndpointMatchedAlternatingGeometry m start
        pieces leftWords rightWords),
      (∀ (j : Fin m) (u : BoundaryScanState),
        scanWordFrom outer inner (geometry.wordStart j) u (leftWords j) =
          scanWordFrom outer inner (geometry.wordStart j) u (rightWords j)) →
      scanWordFrom outer inner start state
          (alternatingConcat m pieces leftWords) =
        scanWordFrom outer inner start state
          (alternatingConcat m pieces rightWords) := by
  intro m
  induction m with
  | zero =>
      intro outer inner _ _ pieces leftWords rightWords start state geometry _
      rfl
  | succ m ih =>
      intro outer inner _ _ pieces leftWords rightWords start state geometry hwords
      rw [show alternatingConcat (m + 1) pieces leftWords =
          pieces 0 ++ leftWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ leftWords j.succ) by rfl,
        show alternatingConcat (m + 1) pieces rightWords =
          pieces 0 ++ rightWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ rightWords j.succ) by rfl,
        scanWordFrom_append, scanWordFrom_append,
        scanWordFrom_append, scanWordFrom_append]
      let afterPiece := scanWordFrom outer inner start state (pieces 0)
      have hstart : afterPiece.1 = geometry.wordStart 0 := by
        calc
          afterPiece.1 = (pieces 0).foldl Annulus.neighbor start := by
            exact scanWordFrom_fst outer inner start state (pieces 0)
          _ = (pieces 0).foldl Annulus.neighbor (geometry.pieceStart 0) := by
            rw [geometry.pieceStart_zero]
          _ = geometry.wordStart 0 := geometry.retainedEndpoint 0
      have hzero := hwords (0 : Fin (m + 1)) afterPiece.2
      change scanWordFrom outer inner
          (scanWordFrom outer inner afterPiece.1 afterPiece.2 (leftWords 0)).1
          (scanWordFrom outer inner afterPiece.1 afterPiece.2 (leftWords 0)).2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ leftWords j.succ)) = _
      rw [hstart, hzero]
      let afterWord := scanWordFrom outer inner
        (geometry.wordStart 0) afterPiece.2 (rightWords 0)
      have hnext : afterWord.1 = geometry.pieceStart 1 := by
        rw [scanWordFrom_fst]
        exact geometry.rightWordEndpoint 0
      change scanWordFrom outer inner afterWord.1 afterWord.2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ leftWords j.succ)) =
        scanWordFrom outer inner afterWord.1 afterWord.2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ rightWords j.succ))
      rw [hnext]
      apply ih outer inner (fun j ↦ pieces j.succ)
        (fun j ↦ leftWords j.succ) (fun j ↦ rightWords j.succ)
        (geometry.pieceStart 1) afterWord.2 geometry.tail
      intro j u
      exact hwords j.succ u

/-- Terminal-scale variant.  At each word start the common retained piece
has just visited the terminal inner boundary, hence the scanner is seeking
the outer boundary.  Word equality is therefore required only in that
reachable state. -/
theorem scanWordFrom_alternatingConcat_eq_of_endpointGeometry_seekingOuter :
    ∀ (m : ℕ) (outer inner : Set Point)
      [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
      (pieces : Fin (m + 1) → List Direction)
      (leftWords rightWords : TerminalSegmentWords m)
      (start : Point) (state : BoundaryScanState)
      (geometry : EndpointMatchedAlternatingGeometry m start
        pieces leftWords rightWords),
      (∀ (j : Fin m) (u : BoundaryScanState),
        (scanWordFrom outer inner (geometry.pieceStart j.castSucc) u
          (pieces j.castSucc)).2.seekingOuter = true) →
      (∀ (j : Fin m) (c : ℕ),
        scanWordFrom outer inner (geometry.wordStart j) ⟨true, c⟩
            (leftWords j) =
          scanWordFrom outer inner (geometry.wordStart j) ⟨true, c⟩
            (rightWords j)) →
      scanWordFrom outer inner start state
          (alternatingConcat m pieces leftWords) =
        scanWordFrom outer inner start state
          (alternatingConcat m pieces rightWords) := by
  intro m
  induction m with
  | zero =>
      intro outer inner _ _ pieces leftWords rightWords start state geometry
        _hseek _hwords
      rfl
  | succ m ih =>
      intro outer inner _ _ pieces leftWords rightWords start state geometry
        hseek hwords
      rw [show alternatingConcat (m + 1) pieces leftWords =
          pieces 0 ++ leftWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ leftWords j.succ) by rfl,
        show alternatingConcat (m + 1) pieces rightWords =
          pieces 0 ++ rightWords 0 ++
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ rightWords j.succ) by rfl,
        scanWordFrom_append, scanWordFrom_append,
        scanWordFrom_append, scanWordFrom_append]
      let afterPiece := scanWordFrom outer inner start state (pieces 0)
      have hstart : afterPiece.1 = geometry.wordStart 0 := by
        calc
          afterPiece.1 = (pieces 0).foldl Annulus.neighbor start := by
            exact scanWordFrom_fst outer inner start state (pieces 0)
          _ = (pieces 0).foldl Annulus.neighbor (geometry.pieceStart 0) := by
            rw [geometry.pieceStart_zero]
          _ = geometry.wordStart 0 := geometry.retainedEndpoint 0
      have hmode : afterPiece.2.seekingOuter = true := by
        have hzeroFin : (0 : Fin (m + 2)) =
            (0 : Fin (m + 1)).castSucc := by apply Fin.ext; rfl
        have hs := hseek (0 : Fin (m + 1)) state
        rw [← hzeroFin, geometry.pieceStart_zero] at hs
        exact hs
      let completed := afterPiece.2.completed
      have hstate : afterPiece.2 = ⟨true, completed⟩ := by
        rcases hs : afterPiece.2 with ⟨mode, c⟩
        have hm : mode = true := by simpa [hs] using hmode
        subst mode
        simp [completed, hs]
      have hzero := hwords (0 : Fin (m + 1)) completed
      change scanWordFrom outer inner
          (scanWordFrom outer inner afterPiece.1 afterPiece.2 (leftWords 0)).1
          (scanWordFrom outer inner afterPiece.1 afterPiece.2 (leftWords 0)).2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ leftWords j.succ)) = _
      rw [hstate, hstart, hzero]
      let afterWord := scanWordFrom outer inner
        (geometry.wordStart 0) ⟨true, completed⟩ (rightWords 0)
      have hnext : afterWord.1 = geometry.pieceStart 1 := by
        rw [scanWordFrom_fst]
        exact geometry.rightWordEndpoint 0
      change scanWordFrom outer inner afterWord.1 afterWord.2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ leftWords j.succ)) =
        scanWordFrom outer inner afterWord.1 afterWord.2
          (alternatingConcat m (fun j ↦ pieces j.succ)
            (fun j ↦ rightWords j.succ))
      rw [hnext]
      apply ih outer inner (fun j ↦ pieces j.succ)
        (fun j ↦ leftWords j.succ) (fun j ↦ rightWords j.succ)
        (geometry.pieceStart 1) afterWord.2 geometry.tail
      · intro j u
        exact hseek j.succ u
      · intro j c
        exact hwords j.succ c

/-- Pairwise coarse-scale adapter: two endpoint-matched words which avoid
both boundaries at every positive time have identical scanner effects. -/
theorem scanWordFrom_eq_of_endpointMatched_avoiding_words
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleft : ∀ q, 0 < q → q ≤ leftWord.length →
      wordWalk start leftWord q ∉ outer ∧ wordWalk start leftWord q ∉ inner)
    (hright : ∀ q, 0 < q → q ≤ rightWord.length →
      wordWalk start rightWord q ∉ outer ∧ wordWalk start rightWord q ∉ inner)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom outer inner start state leftWord =
      scanWordFrom outer inner start state rightWord := by
  rw [scanWordFrom_eq_of_wordWalk_avoids outer inner start state leftWord hleft,
    scanWordFrom_eq_of_wordWalk_avoids outer inner start state rightWord hright,
    hend]

/-- Pairwise penultimate-scale adapter: both words have only their common
inner-boundary endpoint visible to the scanner. -/
theorem scanWordFrom_eq_of_endpointMatched_first_inner_words
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState)
    (leftWord rightWord : List Direction)
    (hleftNe : leftWord ≠ []) (hrightNe : rightWord ≠ [])
    (hleftAvoid : ∀ q, 0 < q → q < leftWord.length →
      wordWalk start leftWord q ∉ outer ∧ wordWalk start leftWord q ∉ inner)
    (hrightAvoid : ∀ q, 0 < q → q < rightWord.length →
      wordWalk start rightWord q ∉ outer ∧ wordWalk start rightWord q ∉ inner)
    (hleftOuter : wordWalk start leftWord leftWord.length ∉ outer)
    (hrightOuter : wordWalk start rightWord rightWord.length ∉ outer)
    (hleftInner : wordWalk start leftWord leftWord.length ∈ inner)
    (hrightInner : wordWalk start rightWord rightWord.length ∈ inner)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom outer inner start state leftWord =
      scanWordFrom outer inner start state rightWord := by
  apply Prod.ext
  · simpa only [scanWordFrom_fst, wordWalk_length] using hend
  · rw [scanWordFrom_eq_of_first_inner_at_end outer inner start state leftWord
        hleftNe hleftAvoid hleftOuter hleftInner,
      scanWordFrom_eq_of_first_inner_at_end outer inner start state rightWord
        hrightNe hrightAvoid hrightOuter hrightInner]

/-- Pairwise terminal-scale adapter in the state which actually occurs at
the beginning of an outward terminal gap. -/
theorem scanWordFrom_eq_of_endpointMatched_first_outer_words
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (completed : ℕ)
    (leftWord rightWord : List Direction)
    (hleftNe : leftWord ≠ []) (hrightNe : rightWord ≠ [])
    (hleftAvoid : ∀ q, 0 < q → q < leftWord.length →
      wordWalk start leftWord q ∉ outer)
    (hrightAvoid : ∀ q, 0 < q → q < rightWord.length →
      wordWalk start rightWord q ∉ outer)
    (hleftOuter : wordWalk start leftWord leftWord.length ∈ outer)
    (hrightOuter : wordWalk start rightWord rightWord.length ∈ outer)
    (hend : wordWalk start leftWord leftWord.length =
      wordWalk start rightWord rightWord.length) :
    scanWordFrom outer inner start ⟨true, completed⟩ leftWord =
      scanWordFrom outer inner start ⟨true, completed⟩ rightWord := by
  apply Prod.ext
  · simpa only [scanWordFrom_fst, wordWalk_length] using hend
  · rw [scanWordFrom_seekingOuter_eq_of_first_outer_at_end outer inner start
        completed leftWord hleftNe hleftAvoid hleftOuter,
      scanWordFrom_seekingOuter_eq_of_first_outer_at_end outer inner start
        completed rightWord hrightNe hrightAvoid hrightOuter]

/-! ## From finite scans back to excursion profiles -/

/-- Equal inclusive word scans give equal first-hit excursion counts.  The
schedules merely certify that the finite first-hit implementation and the
two-state scanner agree; no clock endpoint matching between the two words is
assumed. -/
theorem completedExcursionCount_wordWalk_eq_of_scanWordFrom_eq
    {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start : Point} {leftWord rightWord : List Direction}
    (hdisjoint : Disjoint outer inner)
    (hscan : scanWordFrom outer inner start
        (visitBoundary outer inner TerminalBoundaryScan.initialState start)
        leftWord =
      scanWordFrom outer inner start
        (visitBoundary outer inner TerminalBoundaryScan.initialState start)
        rightWord) :
    completedExcursionCount (wordWalk start leftWord) outer inner
        leftWord.length =
      completedExcursionCount (wordWalk start rightWord) outer inner
        rightWord.length := by
  have hvis : visitBoundary outer inner TerminalBoundaryScan.initialState start =
      TerminalBoundaryScan.visit outer inner
        TerminalBoundaryScan.initialState start :=
    visitBoundary_eq_terminalBoundaryScan_visit _ _ _ _
  have hscan' : TerminalBoundaryScan.scanWord outer inner start leftWord =
      TerminalBoundaryScan.scanWord outer inner start rightWord := by
    unfold TerminalBoundaryScan.scanWord
    rw [← scanWordFrom_eq_terminalBoundaryScan_scanDirections,
      ← scanWordFrom_eq_terminalBoundaryScan_scanDirections, ← hvis]
    exact congrArg Prod.snd hscan
  have hthrough : TerminalBoundaryScan.scanThrough
        (wordWalk start leftWord) outer inner leftWord.length =
      TerminalBoundaryScan.scanThrough
        (wordWalk start rightWord) outer inner rightWord.length := by
    rw [← TerminalBoundaryScan.scanWord_eq_scanThrough_wordWalk,
      ← TerminalBoundaryScan.scanWord_eq_scanThrough_wordWalk]
    exact hscan'
  exact TerminalBoundaryScan.completedExcursionCount_eq_of_scanThrough_eq
    hdisjoint hthrough

/-- Whole HLOZ-profile version of the finite trace invariant. -/
theorem excursionProfile_wordWalk_eq_of_scanWordFrom_eq
    {n : ℕ} {x start : Point} {leftWord rightWord : List Direction}
    (hdisjoint : ∀ k : Fin (n + 2), (k : ℕ) ≠ 0 →
      Disjoint
        (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
        (discBoundary x (scaleRadius n (k : ℕ))))
    (hscan : ∀ k : Fin (n + 2), (k : ℕ) ≠ 0 →
      scanWordFrom
          (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
          (discBoundary x (scaleRadius n (k : ℕ))) start
          (visitBoundary
            (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
            (discBoundary x (scaleRadius n (k : ℕ)))
            TerminalBoundaryScan.initialState start) leftWord =
        scanWordFrom
          (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
          (discBoundary x (scaleRadius n (k : ℕ))) start
          (visitBoundary
            (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
            (discBoundary x (scaleRadius n (k : ℕ)))
            TerminalBoundaryScan.initialState start) rightWord) :
    excursionProfile (wordWalk start leftWord) n leftWord.length x =
      excursionProfile (wordWalk start rightWord) n rightWord.length x := by
  classical
  funext k
  unfold excursionProfile
  split_ifs with hk
  · rfl
  · exact completedExcursionCount_wordWalk_eq_of_scanWordFrom_eq
      (hdisjoint k hk) (hscan k hk)

/-! ## One-shot alternating-concatenation theorem -/

/-- Replacing endpoint-matched terminal inner-to-outer first-hit words by
words of arbitrary lengths preserves the entire annular excursion profile.
The retained pieces are shared literally.  Their nonemptiness is used only
at the terminal level, where their common inner endpoint resets the scanner
to seek the next outer boundary. -/
theorem excursionProfile_alternatingConcat_eq_of_terminalFirstHits
    {n m : ℕ} (hn : 2 ≤ n) {x start : Point}
    {pieces : Fin (m + 1) → List Direction}
    {leftWords rightWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      leftWords rightWords)
    (hpiecesNe : ∀ j : Fin m, pieces j.castSucc ≠ [])
    (hstarts : ∀ j : Fin m,
      geometry.wordStart j ∈ terminalInnerBoundary n x)
    (hleftFirst : ∀ j : Fin m,
      AbsoluteBoundaryFirstAt (terminalOuterBoundary n x)
        (geometry.wordStart j)
        (extendStoppedWord (stoppedWordOfList (leftWords j)))
        (leftWords j).length)
    (hrightFirst : ∀ j : Fin m,
      AbsoluteBoundaryFirstAt (terminalOuterBoundary n x)
        (geometry.wordStart j)
        (extendStoppedWord (stoppedWordOfList (rightWords j)))
        (rightWords j).length) :
    excursionProfile
        (wordWalk start (alternatingConcat m pieces leftWords)) n
        (alternatingConcat m pieces leftWords).length x =
      excursionProfile
        (wordWalk start (alternatingConcat m pieces rightWords)) n
        (alternatingConcat m pieces rightWords).length x := by
  classical
  apply excursionProfile_wordWalk_eq_of_scanWordFrom_eq
  · intro k hk
    exact profileBoundaries_disjoint hn x k hk
  · intro k hk
    change scanWordFrom
        (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start
        (visitBoundary
          (profileOuterBoundary n (k : ℕ) x)
          (profileInnerBoundary n (k : ℕ) x)
          TerminalBoundaryScan.initialState start)
        (alternatingConcat m pieces leftWords) = _
    by_cases hcoarse : (k : ℕ) < n
    · apply scanWordFrom_alternatingConcat_eq_of_endpointGeometry
        m _ _ pieces leftWords rightWords start _ geometry
      intro j state
      have hn1 : 1 ≤ n := by omega
      apply scanWordFrom_eq_of_terminalFirstHits_of_lt hn1 hcoarse
        state (leftWords j) (rightWords j) (hstarts j)
        (hleftFirst j) (hrightFirst j)
      simp only [wordWalk_length, geometry.leftWordEndpoint,
        geometry.rightWordEndpoint]
    · by_cases hself : (k : ℕ) = n
      · have hkEq : k = ⟨n, by omega⟩ := Fin.ext hself
        rw [hkEq]
        apply scanWordFrom_alternatingConcat_eq_of_endpointGeometry
          m _ _ pieces leftWords rightWords start _ geometry
        intro j state
        apply scanWordFrom_eq_of_terminalFirstHits_at_self hn state
          (leftWords j) (rightWords j) (hstarts j)
          (hleftFirst j) (hrightFirst j)
        simp only [wordWalk_length, geometry.leftWordEndpoint,
          geometry.rightWordEndpoint]
      · have hterminal : (k : ℕ) = n + 1 := by omega
        have hkEq : k = ⟨n + 1, by omega⟩ := Fin.ext hterminal
        rw [hkEq]
        change scanWordFrom (terminalOuterBoundary n x)
            (terminalInnerBoundary n x) start
            (visitBoundary (terminalOuterBoundary n x)
              (terminalInnerBoundary n x)
              TerminalBoundaryScan.initialState start)
            (alternatingConcat m pieces leftWords) = _
        apply scanWordFrom_alternatingConcat_eq_of_endpointGeometry_seekingOuter
          m _ _ pieces leftWords rightWords start _ geometry
        · intro j state
          apply scanWordFrom_seekingOuter_of_nonempty_endpoint_inner
            (terminalOuterBoundary n x) (terminalInnerBoundary n x)
            (geometry.pieceStart j.castSucc) state (pieces j.castSucc)
            (hpiecesNe j)
          · rw [wordWalk_length, geometry.retainedEndpoint]
            intro houter
            exact Set.disjoint_left.1 (terminalBoundaries_disjoint hn x)
              houter (hstarts j)
          · rw [wordWalk_length, geometry.retainedEndpoint]
            exact hstarts j
        · intro j completed
          apply scanWordFrom_eq_of_terminalFirstHits_at_terminal hn completed
            (leftWords j) (rightWords j) (hstarts j)
            (hleftFirst j) (hrightFirst j)
          simp only [wordWalk_length, geometry.leftWordEndpoint,
            geometry.rightWordEndpoint]

/-! ## Extracted-skeleton specialization -/

/-- The literal complementary pieces, extracted interval words, and any
endpoint-matched boundary-exit words carry canonical common endpoint
geometry. -/
noncomputable def extracted_endpointGeometry_of_boundaryExitWordCodes
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) (boundary : Set Point)
    (bridges : ∀ j : Fin m,
      BoundaryExitWordCode boundary (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j))) :
    let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
    let leftWords := intervalWords omega t.entrance t.exit
    let rightWords : TerminalSegmentWords m :=
      fun j ↦ List.ofFn (bridges j).1.2
    EndpointMatchedAlternatingGeometry m (0, 0) pieces leftWords rightWords := by
  classical
  dsimp only
  let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
  let leftWords := intervalWords omega t.entrance t.exit
  let rightWords : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
  let leftOmega := reconstructedTerminalStepPath pieces leftWords
  have halign : ∀ j : Fin m,
      trajectory leftOmega (replacementWordStart m pieces leftWords j) =
          trajectory omega (t.entrance j) ∧
      trajectory leftOmega (replacementWordStop pieces leftWords j) =
          trajectory omega (t.exit j) := by
    simpa [pieces, leftWords, leftOmega] using
      replacementWordStart_stop_alignment omega t leftWords ht (by
        intro j
        exact wordEndpoint_incrementSlice omega (ht.1 j).1)
  refine
    { pieceStart := fun j ↦
        trajectory leftOmega (retainedPieceStart m pieces leftWords j)
      wordStart := fun j ↦ trajectory omega (t.entrance j)
      pieceStart_zero := ?_
      retainedEndpoint := ?_
      leftWordEndpoint := ?_
      rightWordEndpoint := ?_ }
  · simp [leftOmega]
  · intro j
    change wordEndpoint
        (trajectory leftOmega
          (retainedPieceStart m pieces leftWords j.castSucc))
        (pieces j.castSucc) = trajectory omega (t.entrance j)
    rw [← trajectoryFrom_extendStoppedWord_stoppedWordOfList_length]
    rw [← trajectory_reconstructed_retainedPieceStop]
    rw [retainedPieceStop_castSucc_eq_replacementWordStart]
    exact (halign j).1
  · intro j
    change wordEndpoint (trajectory omega (t.entrance j)) (leftWords j) =
      trajectory leftOmega (retainedPieceStart m pieces leftWords j.succ)
    rw [retainedPieceStart_succ_eq_replacementWordStop, (halign j).2]
    exact wordEndpoint_incrementSlice omega (ht.1 j).1
  · intro j
    change wordEndpoint (trajectory omega (t.entrance j)) (rightWords j) =
      trajectory leftOmega (retainedPieceStart m pieces leftWords j.succ)
    rw [retainedPieceStart_succ_eq_replacementWordStop, (halign j).2]
    exact boundaryExitWordCode_wordEndpoint (bridges j)

@[simp] theorem extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart
    {m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) (boundary : Set Point)
    (bridges : ∀ j : Fin m,
      BoundaryExitWordCode boundary (trajectory omega (t.entrance j))
        (trajectory omega (t.exit j))) (j : Fin m) :
    (extracted_endpointGeometry_of_boundaryExitWordCodes
      omega t ht boundary bridges).wordStart j =
        trajectory omega (t.entrance j) := by
  rfl

/-- Every retained piece immediately preceding one of the selected extracted
terminal gaps has positive length.  The first contains the initial
outer-to-inner passage; every later one runs from a terminal-outer endpoint
to the next terminal-inner endpoint. -/
theorem extracted_complementaryPieces_preword_ne
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 2 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hm : 0 < AppendixLocalTime.requiredTerminalCount scale profileDelta)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hendpoint : ∀ j : Fin
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      trajectory (reconstructedTerminalStepPath
          (complementaryPieces
            (AppendixLocalTime.requiredTerminalCount scale profileDelta)
            omega 0 horizon
            (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
            (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit)
          words)
          (replacementWordStop
            (complementaryPieces
              (AppendixLocalTime.requiredTerminalCount scale profileDelta)
              omega 0 horizon
              (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
              (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit)
            words j) =
        trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j)) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    ∀ j : Fin m, pieces j.castSucc ≠ [] := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 t.horizon t.entrance t.exit
  let newPath := trajectory (reconstructedTerminalStepPath pieces words)
  have htHorizon : t.horizon = horizon := rfl
  have hscale1 : 1 ≤ scale := by omega
  have hretained : RetainedFirstHitInputs omega t words
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) := by
    apply retainedFirstHitInputsOfExtractedTimedSkeleton hscale1
      hexit hx hm words
    simpa [m, t, pieces, newPath, extractTimedTerminalSkeleton] using hendpoint
  have hdisjoint := terminalBoundaries_disjoint hscale x
  intro j
  by_cases hjzero : (j : ℕ) = 0
  · have hjEq : j = ⟨0, hm⟩ := Fin.ext hjzero
    rw [hjEq]
    have hcast : (⟨0, hm⟩ : Fin m).castSucc = (0 : Fin (m + 1)) := Fin.ext rfl
    rw [hcast]
    have hinner := hretained.firstInnerZero hm
    have hout : newPath hretained.initialOuterTime ∈
        terminalOuterBoundary scale x := hretained.firstOuter.2.2.1
    have hin : newPath (replacementWordStart m pieces words ⟨0, hm⟩) ∈
        terminalInnerBoundary scale x := hinner.2.2.1
    have hlt : hretained.initialOuterTime <
        replacementWordStart m pieces words ⟨0, hm⟩ := by
      apply lt_of_le_of_ne hinner.1
      intro heq
      apply Set.disjoint_left.1 hdisjoint hout
      rw [heq]
      exact hin
    have hpos : 0 < replacementWordStart m pieces words ⟨0, hm⟩ := by omega
    have hlen : (pieces (0 : Fin (m + 1))).length =
        replacementWordStart m pieces words ⟨0, hm⟩ := by
      rw [← retainedPieceStop_castSucc_eq_replacementWordStart
        pieces words ⟨0, hm⟩]
      simp [retainedPieceStop]
    intro hempty
    have hempty' : pieces (0 : Fin (m + 1)) = [] := by
      change complementaryPieces m omega 0 t.horizon t.entrance t.exit 0 = []
      rw [htHorizon]
      simpa [m, t] using hempty
    have hz : (pieces (0 : Fin (m + 1))).length = 0 := by simp [hempty']
    omega
  · let prev : Fin m := ⟨(j : ℕ) - 1, by omega⟩
    let next : Fin m := ⟨(prev : ℕ) + 1, by simp [prev, m]; omega⟩
    have hnext : next = j := by
      apply Fin.ext
      simp [next, prev]
      omega
    have hseg := hretained.firstInnerSucc prev (by simp [prev, m]; omega)
    have hout : newPath (replacementWordStop pieces words prev) ∈
        terminalOuterBoundary scale x := by
      have hep := hendpoint prev
      have hep' : newPath (replacementWordStop pieces words prev) =
          trajectory omega (t.exit prev) := by
        simpa [m, t, pieces, newPath, extractTimedTerminalSkeleton] using hep
      rw [hep']
      simpa [t, extractTimedTerminalSkeleton] using
        extractTerminalSkeletonCode_exit_mem hscale1 hexit hx prev
    have hin : newPath (replacementWordStart m pieces words j) ∈
        terminalInnerBoundary scale x := by
      simpa [next, hnext, m, t, pieces, newPath] using hseg.2.2.1
    have hlt : replacementWordStop pieces words prev <
        replacementWordStart m pieces words j := by
      have hle : replacementWordStop pieces words prev ≤
          replacementWordStart m pieces words j := by
        simpa [next, hnext, m, t, pieces, newPath] using hseg.1
      apply lt_of_le_of_ne hle
      intro heq
      apply Set.disjoint_left.1 hdisjoint hout
      rw [heq]
      exact hin
    have hindex : j.castSucc = prev.succ := by
      apply Fin.ext
      simp [prev]
      omega
    have hstart : retainedPieceStart m pieces words j.castSucc =
        replacementWordStop pieces words prev := by
      rw [hindex]
      exact retainedPieceStart_succ_eq_replacementWordStop pieces words prev
    have hstop : retainedPieceStop pieces words j.castSucc =
        replacementWordStart m pieces words j := by
      exact retainedPieceStop_castSucc_eq_replacementWordStart pieces words j
    have hlenpos : 0 < (pieces j.castSucc).length := by
      rw [← hstart, ← hstop] at hlt
      unfold retainedPieceStop at hlt
      omega
    exact List.ne_nil_of_length_pos hlenpos

/-- The literal interval word removed by extraction is itself a terminal
first-hit word.  Keeping this adapter separate prevents callers from having
to unfold the proof-rich canonical bridge code. -/
theorem extracted_intervalWord_absoluteBoundaryFirstAt
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
      (trajectory omega (t.entrance j))
      (extendStoppedWord
        (stoppedWordOfList (intervalWords omega t.entrance t.exit j)))
      (intervalWords omega t.entrance t.exit j).length := by
  classical
  dsimp only
  let w := extractedTerminalStoppedWord scale horizon profileDelta x omega j
  have hbase := extractedTerminalStoppedWord_absoluteBoundaryFirstAt
    hscale hexit hx j
  dsimp only at hbase
  rw [extractTimedTerminalSkeleton_entrancePoint_eq] at hbase
  have herased := extractedTerminalStoppedWord_erased
    scale horizon profileDelta x omega j
  have hext := extendStoppedWord_stoppedWordOfList_ofFn w
  rw [← hext] at hbase
  rw [herased] at hbase
  have hlen :
      (intervalWords omega
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j).length =
        w.1 := by
    rw [← herased]
    simp only [List.length_ofFn, Fintype.card_fin]
    exact extractedTerminalStoppedWord_length
      scale horizon profileDelta x omega j
  rw [hlen]
  exact hbase

/-- Canonical whole-profile splice invariance for a stopped successful path.
The replacement word at every extracted coordinate may have an arbitrary
length; only its terminal first-hit certificate and recorded endpoint are
used. -/
theorem excursionProfile_reconstructed_of_boundaryExitWordCodes
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega : StepPath}
    (hscale : 2 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (bridges : ∀ j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta),
      BoundaryExitWordCode (terminalOuterBoundary scale x)
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j))
        (trajectory omega
          ((extractTimedTerminalSkeleton scale horizon profileDelta x omega).exit j))) :
    let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
    let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
    let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
    let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
    excursionProfile (trajectory omega) scale horizon x =
      excursionProfile (trajectory (reconstructedTerminalStepPath pieces words))
        scale (alternatingConcat m pieces words).length x := by
  classical
  dsimp only
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let pieces := complementaryPieces m omega 0 horizon t.entrance t.exit
  let leftWords := intervalWords omega t.entrance t.exit
  let words : TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2
  let leftFull := alternatingConcat m pieces leftWords
  let rightFull := alternatingConcat m pieces words
  let newOmega := reconstructedTerminalStepPath pieces words
  have hscale1 : 1 ≤ scale := by omega
  have ht : t.WellFormed := by
    exact extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale1 hexit hx
  let geometry : EndpointMatchedAlternatingGeometry m (0, 0)
      pieces leftWords words :=
    extracted_endpointGeometry_of_boundaryExitWordCodes omega t ht
      (terminalOuterBoundary scale x) bridges
  have halign : ∀ j : Fin m,
      trajectory newOmega (replacementWordStart m pieces words j) =
          trajectory omega (t.entrance j) ∧
      trajectory newOmega (replacementWordStop pieces words j) =
          trajectory omega (t.exit j) := by
    simpa [m, t, pieces, words, newOmega, extractTimedTerminalSkeleton] using
      replacementWordStart_stop_alignment_of_boundaryExitWordCodes
        omega t ht (terminalOuterBoundary scale x) bridges
  have hpiecesNe : ∀ j : Fin m, pieces j.castSucc ≠ [] := by
    intro j
    by_cases hm : 0 < m
    · apply extracted_complementaryPieces_preword_ne hscale hexit hx hm words
      intro i
      exact (halign i).2
    · exact (hm (Nat.zero_lt_of_lt j.isLt)).elim
  have hstarts : ∀ j : Fin m,
      geometry.wordStart j ∈ terminalInnerBoundary scale x := by
    intro j
    rw [extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart]
    simpa [t, extractTimedTerminalSkeleton] using
      extractTerminalSkeletonCode_entrance_mem hscale1 hexit hx j
  have hleftFirst : ∀ j : Fin m,
      AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
        (geometry.wordStart j)
        (extendStoppedWord (stoppedWordOfList (leftWords j)))
        (leftWords j).length := by
    intro j
    rw [extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart]
    simpa [leftWords, t] using
      extracted_intervalWord_absoluteBoundaryFirstAt hscale1 hexit hx j
  have hrightFirst : ∀ j : Fin m,
      AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
        (geometry.wordStart j)
        (extendStoppedWord (stoppedWordOfList (words j)))
        (words j).length := by
    intro j
    rw [extracted_endpointGeometry_of_boundaryExitWordCodes_wordStart]
    change AbsoluteBoundaryFirstAt (terminalOuterBoundary scale x)
      (trajectory omega (t.entrance j))
      (extendStoppedWord (stoppedWordOfList (List.ofFn (bridges j).1.2)))
      (List.ofFn (bridges j).1.2).length
    simpa [extendStoppedWord_stoppedWordOfList_ofFn] using (bridges j).2.1
  have hprofileWords :
      excursionProfile (wordWalk (0, 0) leftFull) scale leftFull.length x =
        excursionProfile (wordWalk (0, 0) rightFull) scale rightFull.length x := by
    exact excursionProfile_alternatingConcat_eq_of_terminalFirstHits hscale
      geometry hpiecesNe hstarts hleftFirst hrightFirst
  have hleftFull : leftFull = incrementSlice omega 0 horizon := by
    exact alternatingConcat_complementaryPieces m omega 0 horizon
      t.entrance t.exit (orderedIntervals_of_wellFormed ht)
  have hleftProfile :
      excursionProfile (wordWalk (0, 0) leftFull) scale leftFull.length x =
        excursionProfile (trajectory omega) scale horizon x := by
    rw [hleftFull]
    simp only [incrementSlice_length, Nat.sub_zero]
    apply Proposition13Measurability.excursionProfile_congr_prefix
    intro q hq
    simpa [wordWalk] using
      wordPosition_incrementSlice omega (Nat.zero_le horizon) hq
  have hrightProfile :
      excursionProfile (wordWalk (0, 0) rightFull) scale rightFull.length x =
        excursionProfile (trajectory newOmega) scale rightFull.length x := by
    apply Proposition13Measurability.excursionProfile_congr_prefix
    intro q hq
    rw [wordWalk_eq_trajectoryFrom_extendStoppedWord (0, 0) rightFull hq]
    simpa [newOmega, rightFull, reconstructedTerminalStepPath,
      PlanarPotential.trajectoryFrom] using
      (rfl : PlanarPotential.trajectoryFrom (0, 0)
        (extendStoppedWord (stoppedWordOfList rightFull)) q =
        PlanarPotential.trajectoryFrom (0, 0)
          (extendStoppedWord (stoppedWordOfList rightFull)) q)
  exact hleftProfile.symm.trans (hprofileWords.trans hrightProfile)

end

end Erdos1165.TerminalProfileClockEquivalence
