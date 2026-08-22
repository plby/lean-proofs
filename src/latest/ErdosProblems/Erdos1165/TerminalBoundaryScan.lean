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

import ErdosProblems.Erdos1165.TerminalClockSplice
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice

/-!
# A finite-state scan for alternating annular clocks

The implementation of `ThickPoint.completedExcursionCount` is phrased in
terms of iterated finite first-hit times.  For splicing finite path words it
is more convenient to use the equivalent two-state automaton: while seeking
the outer boundary, ignore every vertex until an outer vertex is seen; then
seek the inner boundary and increment the counter when it is seen.

This file gives the executable scan and proves that its counter is the
first-hit completed-excursion count whenever the two boundaries are
disjoint.  Disjointness is essential for a one-visit-per-vertex automaton:
the first-hit clock is inclusive at both ends and can otherwise complete an
outer and an inner hit at the same time.
-/

namespace Erdos1165.TerminalBoundaryScan

open Set
open ThickPoint TerminalClockSplice

noncomputable section

/-- State of the alternating boundary automaton. -/
structure BoundaryScanState where
  seekingOuter : Bool
  completed : ℕ
deriving DecidableEq, Repr

/-- The initial state seeks the first outer-boundary visit. -/
def initialState : BoundaryScanState := ⟨true, 0⟩

/-- Process one vertex.  An irrelevant boundary is ignored in either phase. -/
def visit (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (state : BoundaryScanState) (x : Point) : BoundaryScanState :=
  if state.seekingOuter then
    if x ∈ outer then ⟨false, state.completed⟩ else state
  else if x ∈ inner then ⟨true, state.completed + 1⟩ else state

/-- Process the `length` vertices beginning at absolute time `start`. -/
def scanSegment (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : ℕ) : ℕ → BoundaryScanState → BoundaryScanState
  | 0, state => state
  | length + 1, state =>
      visit outer inner (scanSegment s outer inner start length state)
        (s (start + length))

/-- Process the vertices at times `0, ..., horizon`, inclusively. -/
def scanThrough (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) : BoundaryScanState :=
  scanSegment s outer inner 0 (horizon + 1) initialState

@[simp] theorem scanSegment_zero (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : ℕ) (state : BoundaryScanState) :
    scanSegment s outer inner start 0 state = state := rfl

@[simp] theorem scanSegment_succ (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length : ℕ) (state : BoundaryScanState) :
    scanSegment s outer inner start (length + 1) state =
      visit outer inner (scanSegment s outer inner start length state)
        (s (start + length)) := rfl

theorem scanSegment_add (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start left right : ℕ) (state : BoundaryScanState) :
    scanSegment s outer inner start (left + right) state =
      scanSegment s outer inner (start + left) right
        (scanSegment s outer inner start left state) := by
  induction right with
  | zero => simp
  | succ right ih =>
      rw [Nat.add_succ, scanSegment_succ, scanSegment_succ, ih]
      congr 2
      omega

/-- Pointwise equal finite path segments produce equal scan results. -/
theorem scanSegment_congr
    (s t : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {sStart tStart length : ℕ} {state : BoundaryScanState}
    (hpath : ∀ q, q < length → s (sStart + q) = t (tStart + q)) :
    scanSegment s outer inner sStart length state =
      scanSegment t outer inner tStart length state := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [scanSegment_succ, scanSegment_succ,
        ih (fun q hq ↦ hpath q (by omega)), hpath length (Nat.lt_succ_self _)]

theorem scanSegment_seekingOuter_of_avoids
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length completed : ℕ)
    (havoid : ∀ q, q < length → s (start + q) ∉ outer) :
    scanSegment s outer inner start length ⟨true, completed⟩ =
      ⟨true, completed⟩ := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [scanSegment_succ, ih (fun q hq ↦ havoid q (by omega))]
      simp [visit, havoid length (Nat.lt_succ_self length)]

theorem scanSegment_seekingInner_of_avoids
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length completed : ℕ)
    (havoid : ∀ q, q < length → s (start + q) ∉ inner) :
    scanSegment s outer inner start length ⟨false, completed⟩ =
      ⟨false, completed⟩ := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [scanSegment_succ, ih (fun q hq ↦ havoid q (by omega))]
      simp [visit, havoid length (Nat.lt_succ_self length)]

theorem scanSegment_firstOuter
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length completed : ℕ)
    (havoid : ∀ q, q < length → s (start + q) ∉ outer)
    (hhit : s (start + length) ∈ outer) :
    scanSegment s outer inner start (length + 1) ⟨true, completed⟩ =
      ⟨false, completed⟩ := by
  rw [scanSegment_succ,
    scanSegment_seekingOuter_of_avoids s outer inner start length completed havoid]
  simp [visit, hhit]

theorem scanSegment_firstInner
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length completed : ℕ)
    (havoid : ∀ q, q < length → s (start + q) ∉ inner)
    (hhit : s (start + length) ∈ inner) :
    scanSegment s outer inner start (length + 1) ⟨false, completed⟩ =
      ⟨true, completed + 1⟩ := by
  rw [scanSegment_succ,
    scanSegment_seekingInner_of_avoids s outer inner start length completed havoid]
  simp [visit, hhit]

theorem scanSegment_after_firstOuter
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start stop horizon completed : ℕ}
    (hfirst : IsFirstHitSegment s outer start stop horizon) :
    scanSegment s outer inner start (stop + 1 - start)
        ⟨true, completed⟩ = ⟨false, completed⟩ := by
  have hstartStop := hfirst.1
  have hlen : stop + 1 - start = (stop - start) + 1 := by omega
  rw [hlen]
  apply scanSegment_firstOuter
  · intro q hq
    apply hfirst.2.2.2 (start + q)
    · omega
    · omega
  · simpa [Nat.add_sub_of_le hfirst.1] using hfirst.2.2.1

theorem scanSegment_after_firstInner
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start stop horizon completed : ℕ}
    (hfirst : IsFirstHitSegment s inner start stop horizon) :
    scanSegment s outer inner start (stop + 1 - start)
        ⟨false, completed⟩ = ⟨true, completed + 1⟩ := by
  have hstartStop := hfirst.1
  have hlen : stop + 1 - start = (stop - start) + 1 := by omega
  rw [hlen]
  apply scanSegment_firstInner
  · intro q hq
    apply hfirst.2.2.2 (start + q)
    · omega
    · omega
  · simpa [Nat.add_sub_of_le hfirst.1] using hfirst.2.2.1

theorem scanSegment_after_firstOuter_strict
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start stop horizon completed : ℕ}
    (hfirst : IsFirstHitSegment s outer start stop horizon)
    (hstrict : start < stop) :
    scanSegment s outer inner (start + 1) (stop - start)
        ⟨true, completed⟩ = ⟨false, completed⟩ := by
  have hlen : stop - start = (stop - (start + 1)) + 1 := by omega
  rw [hlen]
  apply scanSegment_firstOuter
  · intro q hq
    apply hfirst.2.2.2 (start + 1 + q)
    · omega
    · omega
  · simpa [Nat.add_sub_of_le hstrict] using hfirst.2.2.1

theorem scanSegment_after_firstInner_strict
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start stop horizon completed : ℕ}
    (hfirst : IsFirstHitSegment s inner start stop horizon)
    (hstrict : start < stop) :
    scanSegment s outer inner (start + 1) (stop - start)
        ⟨false, completed⟩ = ⟨true, completed + 1⟩ := by
  have hlen : stop - start = (stop - (start + 1)) + 1 := by omega
  rw [hlen]
  apply scanSegment_firstInner
  · intro q hq
    apply hfirst.2.2.2 (start + 1 + q)
    · omega
    · omega
  · simpa [Nat.add_sub_of_le hstrict] using hfirst.2.2.1

theorem IsFirstHitSegment.lt_of_mem_disjoint
    {s : WalkPath} {outer inner : Set Point} (hdisjoint : Disjoint outer inner)
    {start stop horizon : ℕ}
    (hstart : s start ∈ outer)
    (hfirst : IsFirstHitSegment s inner start stop horizon) :
    start < stop := by
  exact lt_of_le_of_ne hfirst.1 fun heq ↦
    Set.disjoint_left.1 hdisjoint hstart (heq ▸ hfirst.2.2.1)

/-! ## The scan at the actual truncated clocks -/

/-- A downward-closed predicate on a finite initial interval occupies exactly
the initial interval whose length is the cardinality of its filter. -/
theorem downward_closed_filter_range
    (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (hdown : ∀ ⦃i j : ℕ⦄, i ≤ j → p j → p i) {j : ℕ} (hj : j < n) :
    p j ↔ j < ((Finset.range n).filter p).card := by
  constructor
  · intro hp
    by_contra hnot
    have hcard : ((Finset.range n).filter p).card ≤ j := Nat.le_of_not_gt hnot
    have hsubset : Finset.range (j + 1) ⊆ (Finset.range n).filter p := by
      intro i hi
      have hij : i ≤ j := by simpa using hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hij.trans_lt hj), hdown hij hp⟩
    have := Finset.card_le_card hsubset
    simp only [Finset.card_range] at this
    omega
  · intro hjcard
    by_contra hnot
    have hsubset : (Finset.range n).filter p ⊆ Finset.range j := by
      intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      apply Finset.mem_range.mpr
      by_contra hij
      exact hnot (hdown (Nat.le_of_not_gt hij) hip)
    have := Finset.card_le_card hsubset
    simp only [Finset.card_range] at this
    omega

/-- The completed clock indices are exactly `0, ..., count - 1`. -/
theorem excursionFinish_le_horizon_iff_lt_completedExcursionCount
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) {j : ℕ} (hj : j < horizon + 1) :
    excursionFinish s outer inner horizon j ≤ horizon ↔
      j < completedExcursionCount s outer inner horizon := by
  unfold completedExcursionCount
  exact downward_closed_filter_range
    (fun k ↦ excursionFinish s outer inner horizon k ≤ horizon)
    (horizon + 1) (fun {_i _k} hik hk ↦
      (TerminalExcursionPathwise.excursionFinish_mono
        s outer inner horizon hik).trans hk) hj

/-- Under disjoint boundaries, a completed `j`-th excursion cannot finish
before time `j+1`. -/
theorem index_succ_le_excursionFinish_of_le
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ) :
    ∀ j, excursionFinish s outer inner horizon j ≤ horizon →
      j + 1 ≤ excursionFinish s outer inner horizon j := by
  intro j hfinish
  induction j with
  | zero =>
      have hstart := excursionStart_mem_outer_of_finish_le
        s outer inner horizon 0 hfinish
      have hinner := excursionFinish_mem_inner_of_le
        s outer inner horizon 0 hfinish
      have hstrict : excursionStart s outer inner horizon 0 <
          excursionFinish s outer inner horizon 0 := by
        exact lt_of_le_of_ne
          (TerminalExcursionPathwise.excursionStart_le_finish
            s outer inner horizon 0) fun heq ↦
          Set.disjoint_left.1 hdisjoint hstart (heq ▸ hinner)
      omega
  | succ j ih =>
      have hprevFinish : excursionFinish s outer inner horizon j ≤ horizon :=
        (TerminalExcursionPathwise.excursionFinish_mono
          s outer inner horizon (Nat.le_succ j)).trans hfinish
      have hprev := ih hprevFinish
      have hstart := excursionStart_mem_outer_of_finish_le
        s outer inner horizon (j + 1) hfinish
      have hinner := excursionFinish_mem_inner_of_le
        s outer inner horizon (j + 1) hfinish
      have hstartFinish : excursionStart s outer inner horizon (j + 1) <
          excursionFinish s outer inner horizon (j + 1) := by
        exact lt_of_le_of_ne
          (TerminalExcursionPathwise.excursionStart_le_finish
            s outer inner horizon (j + 1)) fun heq ↦
          Set.disjoint_left.1 hdisjoint hstart (heq ▸ hinner)
      have hbetween : excursionFinish s outer inner horizon j ≤
          excursionStart s outer inner horizon (j + 1) :=
        TerminalExcursionPathwise.excursionFinish_le_next_start
          s outer inner horizon j
      omega

/-- Just after an actually completed inward excursion, the scan seeks the
next outer boundary and its counter is `j+1`. -/
theorem scan_to_excursionFinish
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ) :
    ∀ j, excursionFinish s outer inner horizon j ≤ horizon →
      scanSegment s outer inner 0
          (excursionFinish s outer inner horizon j + 1) initialState =
        ⟨true, j + 1⟩ := by
  intro j hfinish
  induction j with
  | zero =>
      have hstartLe : excursionStart s outer inner horizon 0 ≤ horizon :=
        (TerminalExcursionPathwise.excursionStart_le_finish
          s outer inner horizon 0).trans hfinish
      have houterFirst : IsFirstHitSegment s outer 0
          (excursionStart s outer inner horizon 0) horizon := by
        simpa [excursionStart] using
          isFirstHitSegment_firstHitThrough_of_le s outer 0 horizon hstartLe
      have hinnerFirst : IsFirstHitSegment s inner
          (excursionStart s outer inner horizon 0)
          (excursionFinish s outer inner horizon 0) horizon := by
        exact isFirstHitSegment_firstHitThrough_of_le s inner _ horizon hfinish
      have houterMem := houterFirst.2.2.1
      have hstrict := IsFirstHitSegment.lt_of_mem_disjoint
        hdisjoint houterMem hinnerFirst
      rw [show excursionFinish s outer inner horizon 0 + 1 =
          (excursionStart s outer inner horizon 0 + 1) +
            (excursionFinish s outer inner horizon 0 -
              excursionStart s outer inner horizon 0) by omega,
        scanSegment_add]
      rw [show 0 + (excursionStart s outer inner horizon 0 + 1) =
          excursionStart s outer inner horizon 0 + 1 by omega]
      have houterScan :=
        scanSegment_after_firstOuter s outer inner houterFirst
          (completed := 0)
      simp only [Nat.sub_zero] at houterScan
      simp only [initialState]
      rw [houterScan]
      rw [scanSegment_after_firstInner_strict
        s outer inner hinnerFirst hstrict]
  | succ j ih =>
      have hprevFinish : excursionFinish s outer inner horizon j ≤ horizon :=
        (TerminalExcursionPathwise.excursionFinish_mono
          s outer inner horizon (Nat.le_succ j)).trans hfinish
      have hstartLe : excursionStart s outer inner horizon (j + 1) ≤ horizon :=
        (TerminalExcursionPathwise.excursionStart_le_finish
          s outer inner horizon (j + 1)).trans hfinish
      have houterFirst : IsFirstHitSegment s outer
          (excursionFinish s outer inner horizon j)
          (excursionStart s outer inner horizon (j + 1)) horizon := by
        have heq := excursionStart_succ_eq_firstHitThrough_finish_global
          s outer inner horizon j
        have hseg := isFirstHitSegment_firstHitThrough_of_le s outer
          (excursionFinish s outer inner horizon j) horizon
          (heq ▸ hstartLe)
        rw [← heq] at hseg
        exact hseg
      have hinnerFirst : IsFirstHitSegment s inner
          (excursionStart s outer inner horizon (j + 1))
          (excursionFinish s outer inner horizon (j + 1)) horizon :=
        isFirstHitSegment_firstHitThrough_of_le s inner _ horizon hfinish
      have hprevInner : s (excursionFinish s outer inner horizon j) ∈ inner :=
        excursionFinish_mem_inner_of_le s outer inner horizon j hprevFinish
      have houterStrict := IsFirstHitSegment.lt_of_mem_disjoint
        hdisjoint.symm hprevInner houterFirst
      have houterMem := houterFirst.2.2.1
      have hinnerStrict := IsFirstHitSegment.lt_of_mem_disjoint
        hdisjoint houterMem hinnerFirst
      rw [show excursionFinish s outer inner horizon (j + 1) + 1 =
          (excursionFinish s outer inner horizon j + 1) +
            (excursionStart s outer inner horizon (j + 1) -
              excursionFinish s outer inner horizon j) +
            (excursionFinish s outer inner horizon (j + 1) -
              excursionStart s outer inner horizon (j + 1)) by omega,
        scanSegment_add, scanSegment_add, ih hprevFinish]
      simp only [Nat.zero_add]
      rw [scanSegment_after_firstOuter_strict
        s outer inner houterFirst houterStrict]
      have hstartEq : excursionFinish s outer inner horizon j + 1 +
            (excursionStart s outer inner horizon (j + 1) -
              excursionFinish s outer inner horizon j) =
          excursionStart s outer inner horizon (j + 1) + 1 := by omega
      rw [hstartEq, scanSegment_after_firstInner_strict
        s outer inner hinnerFirst hinnerStrict]

/-- The first unfinished clock index has sentinel-valued finish time. -/
theorem excursionFinish_completedExcursionCount_eq_sentinel
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ) :
    excursionFinish s outer inner horizon
        (completedExcursionCount s outer inner horizon) = horizon + 1 := by
  let count := completedExcursionCount s outer inner horizon
  have hupper : excursionFinish s outer inner horizon count ≤ horizon + 1 := by
    unfold excursionFinish
    exact TerminalExcursionPathwise.firstHitThrough_le_sentinel s inner _ horizon
  have hnot : ¬excursionFinish s outer inner horizon count ≤ horizon := by
    intro hfinish
    have hindex := index_succ_le_excursionFinish_of_le
      s outer inner hdisjoint horizon count hfinish
    have hcountRange : count < horizon + 1 := by omega
    have hlt :=
      (excursionFinish_le_horizon_iff_lt_completedExcursionCount
        s outer inner horizon hcountRange).mp hfinish
    exact (Nat.lt_irrefl count) hlt
  change excursionFinish s outer inner horizon count = horizon + 1
  omega

/-- For arbitrary paths and horizons, the two-state scan computes the
completed-excursion count. -/
theorem scanThrough_completed_eq_completedExcursionCount
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ) :
    (scanThrough s outer inner horizon).completed =
      completedExcursionCount s outer inner horizon := by
  let count := completedExcursionCount s outer inner horizon
  have hcountLe : count ≤ horizon + 1 :=
    completedExcursionCount_le s outer inner horizon
  have hnext : excursionFinish s outer inner horizon count = horizon + 1 :=
    excursionFinish_completedExcursionCount_eq_sentinel
      s outer inner hdisjoint horizon
  by_cases hcountZero : count = 0
  · have hfinishZero : excursionFinish s outer inner horizon 0 = horizon + 1 := by
      simpa [hcountZero] using hnext
    by_cases houter : excursionStart s outer inner horizon 0 ≤ horizon
    · have houterFirst : IsFirstHitSegment s outer 0
          (excursionStart s outer inner horizon 0) horizon := by
        simpa [excursionStart] using
          isFirstHitSegment_firstHitThrough_of_le s outer 0 horizon houter
      have hinnerAvoid : AvoidsThrough s inner
          (excursionStart s outer inner horizon 0) horizon := by
        unfold excursionFinish at hfinishZero
        exact avoidsThrough_of_firstHitThrough_eq_sentinel
          s inner hfinishZero
      have hprefix := scanSegment_after_firstOuter
        s outer inner houterFirst (completed := 0)
      simp only [Nat.sub_zero] at hprefix
      have htail : scanSegment s outer inner
          (excursionStart s outer inner horizon 0 + 1)
          (horizon - excursionStart s outer inner horizon 0)
          ⟨false, 0⟩ = ⟨false, 0⟩ := by
        apply scanSegment_seekingInner_of_avoids
        intro q hq
        apply hinnerAvoid (excursionStart s outer inner horizon 0 + 1 + q)
        · omega
        · omega
      rw [scanThrough, show horizon + 1 =
          (excursionStart s outer inner horizon 0 + 1) +
            (horizon - excursionStart s outer inner horizon 0) by omega,
        scanSegment_add]
      simp only [Nat.zero_add, initialState]
      rw [hprefix, htail]
      simp [count, hcountZero]
    · have hstartUpper : excursionStart s outer inner horizon 0 ≤ horizon + 1 := by
        unfold excursionStart
        exact TerminalExcursionPathwise.firstHitThrough_le_sentinel s outer _ horizon
      have hstartSentinel : excursionStart s outer inner horizon 0 = horizon + 1 := by
        omega
      have houterAvoid : AvoidsThrough s outer 0 horizon := by
        unfold excursionStart at hstartSentinel
        simpa using avoidsThrough_of_firstHitThrough_eq_sentinel
          s outer hstartSentinel
      have hscan : scanSegment s outer inner 0 (horizon + 1) initialState =
          initialState := by
        apply scanSegment_seekingOuter_of_avoids
        intro q hq
        simpa only [Nat.zero_add] using
          houterAvoid q (Nat.zero_le q) (by omega)
      rw [scanThrough, hscan]
      simp [initialState, count, hcountZero]
  · obtain ⟨j, hjcount⟩ := Nat.exists_eq_succ_of_ne_zero hcountZero
    have hjRange : j < horizon + 1 := by omega
    have hjFinish : excursionFinish s outer inner horizon j ≤ horizon :=
      (excursionFinish_le_horizon_iff_lt_completedExcursionCount
        s outer inner horizon hjRange).mpr (by omega)
    have hprefix := scan_to_excursionFinish
      s outer inner hdisjoint horizon j hjFinish
    have hfinishLe : excursionFinish s outer inner horizon j ≤ horizon := hjFinish
    by_cases houter : excursionStart s outer inner horizon (j + 1) ≤ horizon
    · have heq := excursionStart_succ_eq_firstHitThrough_finish_global
        s outer inner horizon j
      have houterFirst : IsFirstHitSegment s outer
          (excursionFinish s outer inner horizon j)
          (excursionStart s outer inner horizon (j + 1)) horizon := by
        have hseg := isFirstHitSegment_firstHitThrough_of_le s outer
          (excursionFinish s outer inner horizon j) horizon (heq ▸ houter)
        rw [← heq] at hseg
        exact hseg
      have hinnerPoint : s (excursionFinish s outer inner horizon j) ∈ inner :=
        excursionFinish_mem_inner_of_le s outer inner horizon j hjFinish
      have houterStrict := IsFirstHitSegment.lt_of_mem_disjoint
        hdisjoint.symm hinnerPoint houterFirst
      have hinnerAvoid : AvoidsThrough s inner
          (excursionStart s outer inner horizon (j + 1)) horizon := by
        have hfinishNext : excursionFinish s outer inner horizon (j + 1) =
            horizon + 1 := by simpa [count, hjcount] using hnext
        unfold excursionFinish at hfinishNext
        exact avoidsThrough_of_firstHitThrough_eq_sentinel
          s inner hfinishNext
      have houterPart := scanSegment_after_firstOuter_strict
        s outer inner houterFirst houterStrict (completed := j + 1)
      have hinnerTail : scanSegment s outer inner
          (excursionStart s outer inner horizon (j + 1) + 1)
          (horizon - excursionStart s outer inner horizon (j + 1))
          ⟨false, j + 1⟩ = ⟨false, j + 1⟩ := by
        apply scanSegment_seekingInner_of_avoids
        intro q hq
        apply hinnerAvoid
          (excursionStart s outer inner horizon (j + 1) + 1 + q)
        · omega
        · omega
      rw [scanThrough, show horizon + 1 =
          (excursionFinish s outer inner horizon j + 1) +
            (excursionStart s outer inner horizon (j + 1) -
              excursionFinish s outer inner horizon j) +
            (horizon - excursionStart s outer inner horizon (j + 1)) by omega,
        scanSegment_add, scanSegment_add, hprefix]
      simp only [Nat.zero_add]
      rw [houterPart]
      have hstartEq : excursionFinish s outer inner horizon j + 1 +
            (excursionStart s outer inner horizon (j + 1) -
              excursionFinish s outer inner horizon j) =
          excursionStart s outer inner horizon (j + 1) + 1 := by omega
      rw [hstartEq, hinnerTail]
      simp [count, hjcount]
    · have hstartUpper : excursionStart s outer inner horizon (j + 1) ≤
          horizon + 1 := by
        unfold excursionStart
        exact TerminalExcursionPathwise.firstHitThrough_le_sentinel s outer _ horizon
      have hstartSentinel : excursionStart s outer inner horizon (j + 1) =
          horizon + 1 := by omega
      have heq := excursionStart_succ_eq_firstHitThrough_finish_global
        s outer inner horizon j
      have houterAvoid : AvoidsThrough s outer
          (excursionFinish s outer inner horizon j) horizon := by
        apply avoidsThrough_of_firstHitThrough_eq_sentinel s outer
        rw [← heq]
        exact hstartSentinel
      have htail : scanSegment s outer inner
          (excursionFinish s outer inner horizon j + 1)
          (horizon - excursionFinish s outer inner horizon j)
          ⟨true, j + 1⟩ = ⟨true, j + 1⟩ := by
        apply scanSegment_seekingOuter_of_avoids
        intro q hq
        apply houterAvoid (excursionFinish s outer inner horizon j + 1 + q)
        · omega
        · omega
      rw [scanThrough, show horizon + 1 =
          (excursionFinish s outer inner horizon j + 1) +
            (horizon - excursionFinish s outer inner horizon j) by omega,
        scanSegment_add, hprefix]
      simp only [Nat.zero_add]
      rw [htail]
      simp [count, hjcount]

/-- A first-hit schedule fixes the complete scan state just after every
outer hit. -/
theorem scan_to_outerTime
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {horizon count : ℕ} (hdisjoint : Disjoint outer inner)
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    ∀ j, j ≤ count →
      scanSegment s outer inner 0 (schedule.outerTime j + 1) initialState =
        ⟨false, j⟩ := by
  intro j hj
  induction j with
  | zero =>
      simpa [initialState] using
        scanSegment_after_firstOuter s outer inner schedule.firstOuterZero
  | succ j ih =>
      have hjlt : j < count := by omega
      have hinner := schedule.firstInner j hjlt
      have houter := schedule.firstOuterSucc j hjlt
      have houterMem : s (schedule.outerTime j) ∈ outer := by
        by_cases hjzero : j = 0
        · simpa [hjzero] using schedule.firstOuterZero.2.2.1
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjzero
          exact (schedule.firstOuterSucc i (by omega)).2.2.1
      have hinnerStrict : schedule.outerTime j < schedule.innerTime j :=
        IsFirstHitSegment.lt_of_mem_disjoint hdisjoint houterMem hinner
      have hinnerMem : s (schedule.innerTime j) ∈ inner := hinner.2.2.1
      have houterStrict : schedule.innerTime j < schedule.outerTime (j + 1) :=
        IsFirstHitSegment.lt_of_mem_disjoint hdisjoint.symm hinnerMem houter
      rw [show schedule.outerTime (j + 1) + 1 =
          (schedule.outerTime j + 1) +
            (schedule.innerTime j - schedule.outerTime j) +
            (schedule.outerTime (j + 1) - schedule.innerTime j) by omega,
        scanSegment_add, scanSegment_add, ih (by omega)]
      simp only [Nat.zero_add]
      rw [scanSegment_after_firstInner_strict s outer inner hinner hinnerStrict]
      have hstartEq :
          schedule.outerTime j + 1 +
              (schedule.innerTime j - schedule.outerTime j) =
            schedule.innerTime j + 1 := by omega
      rw [hstartEq,
        scanSegment_after_firstOuter_strict s outer inner houter houterStrict]

/-- The executable automaton counter is exactly the iterated first-hit
completed-excursion count. -/
theorem scanThrough_completed_eq_completedExcursionCount_of_schedule
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {horizon count : ℕ} (hdisjoint : Disjoint outer inner)
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    (scanThrough s outer inner horizon).completed =
      completedExcursionCount s outer inner horizon := by
  have houter := scan_to_outerTime hdisjoint schedule count le_rfl
  have houterLe : schedule.outerTime count ≤ horizon := by
    by_cases hzero : count = 0
    · simpa [hzero] using schedule.firstOuterZero.2.1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      exact (schedule.firstOuterSucc j (by omega)).2.1
  have htail :
      scanSegment s outer inner (schedule.outerTime count + 1)
          (horizon - schedule.outerTime count) ⟨false, count⟩ =
        ⟨false, count⟩ := by
    apply scanSegment_seekingInner_of_avoids
    intro q hq
    apply schedule.noFinalInner (schedule.outerTime count + 1 + q)
    · omega
    · omega
  rw [scanThrough, show horizon + 1 =
      (schedule.outerTime count + 1) +
        (horizon - schedule.outerTime count) by omega,
    scanSegment_add, houter]
  simp only [Nat.zero_add]
  rw [htail, schedule.completedExcursionCount_eq]

/-- Consequently, equality of final scan states implies equality of the
first-hit counts even when the two horizons differ. -/
theorem completedExcursionCount_eq_of_scanThrough_eq_of_schedules
    {left right : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {leftHorizon rightHorizon leftCount rightCount : ℕ}
    (hdisjoint : Disjoint outer inner)
    (leftSchedule : FirstHitExcursionSchedule left outer inner
      leftHorizon leftCount)
    (rightSchedule : FirstHitExcursionSchedule right outer inner
      rightHorizon rightCount)
    (hscan : scanThrough left outer inner leftHorizon =
      scanThrough right outer inner rightHorizon) :
    completedExcursionCount left outer inner leftHorizon =
      completedExcursionCount right outer inner rightHorizon := by
  rw [← scanThrough_completed_eq_completedExcursionCount_of_schedule
      hdisjoint leftSchedule,
    ← scanThrough_completed_eq_completedExcursionCount_of_schedule
      hdisjoint rightSchedule,
    hscan]

/-- Equality of final scan states implies equality of first-hit counts, with
no schedule premise and with unrelated horizons. -/
theorem completedExcursionCount_eq_of_scanThrough_eq
    {left right : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {leftHorizon rightHorizon : ℕ}
    (hdisjoint : Disjoint outer inner)
    (hscan : scanThrough left outer inner leftHorizon =
      scanThrough right outer inner rightHorizon) :
    completedExcursionCount left outer inner leftHorizon =
      completedExcursionCount right outer inner rightHorizon := by
  rw [← scanThrough_completed_eq_completedExcursionCount
      left outer inner hdisjoint leftHorizon,
    ← scanThrough_completed_eq_completedExcursionCount
      right outer inner hdisjoint rightHorizon,
    hscan]

/-! ## Scanning finite direction words -/

/-- One direction-fold step, carrying both the current endpoint and the
boundary automaton state. -/
def directionStep (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (state : Point × BoundaryScanState) (d : Direction) :
    Point × BoundaryScanState :=
  let next := Annulus.neighbor state.1 d
  (next, visit outer inner state.2 next)

/-- Fold a finite direction word from an arbitrary boundary-scan state. -/
def scanDirections (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction) :
    Point × BoundaryScanState :=
  word.foldl (directionStep outer inner) (start, state)

/-- Scan a word including its initial vertex and every successive endpoint. -/
def scanWord (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (word : List Direction) : BoundaryScanState :=
  (scanDirections outer inner start
    (visit outer inner initialState start) word).2

@[simp] theorem scanDirections_nil (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) :
    scanDirections outer inner start state [] = (start, state) := rfl

@[simp] theorem scanDirections_cons (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (d : Direction)
    (word : List Direction) :
    scanDirections outer inner start state (d :: word) =
      scanDirections outer inner (Annulus.neighbor start d)
        (visit outer inner state (Annulus.neighbor start d)) word := by
  rfl

theorem scanDirections_append (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState)
    (left right : List Direction) :
    scanDirections outer inner start state (left ++ right) =
      scanDirections outer inner
        (scanDirections outer inner start state left).1
        (scanDirections outer inner start state left).2 right := by
  simp [scanDirections, List.foldl_append]

/-- The direction fold is precisely the path scan of the noninitial word
vertices. -/
theorem scanDirections_state_eq_scanSegment_wordWalk
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (state : BoundaryScanState) (word : List Direction) :
    (scanDirections outer inner start state word).2 =
      scanSegment (TerminalGlobalExitSplice.wordWalk start word)
        outer inner 1 word.length state := by
  induction word generalizing start state with
  | nil => rfl
  | cons d word ih =>
      rw [scanDirections_cons, ih]
      have hsplit := scanSegment_add
        (TerminalGlobalExitSplice.wordWalk start (d :: word))
        outer inner 1 1 word.length state
      rw [show (d :: word).length = 1 + word.length by simp only [List.length_cons]; omega,
        hsplit]
      simp only [scanSegment_succ, scanSegment_zero, Nat.add_zero]
      apply scanSegment_congr
      intro q hq
      unfold TerminalGlobalExitSplice.wordWalk
      change TerminalGlobalExitSplice.wordPosition (Annulus.neighbor start d) word (1 + q) =
        TerminalGlobalExitSplice.wordPosition start (d :: word) (2 + q)
      rw [show 2 + q = (1 + q) + 1 by omega]
      exact (TerminalGlobalExitSplice.wordPosition_cons_succ
        start d word (1 + q)).symm

/-- The explicit direction fold and the inclusive path-prefix scan agree. -/
theorem scanWord_eq_scanThrough_wordWalk
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start : Point) (word : List Direction) :
    scanWord outer inner start word =
      scanThrough (TerminalGlobalExitSplice.wordWalk start word)
        outer inner word.length := by
  rw [scanWord, scanDirections_state_eq_scanSegment_wordWalk]
  unfold scanThrough
  rw [show word.length + 1 = 1 + word.length by omega, scanSegment_add]
  simp [initialState, TerminalGlobalExitSplice.wordWalk_zero]

/-- At a scheduled finite word horizon, the direction fold computes the
first-hit completed-excursion count. -/
theorem scanWord_completed_eq_completedExcursionCount_of_schedule
    {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {start : Point} {word : List Direction} {count : ℕ}
    (hdisjoint : Disjoint outer inner)
    (schedule : FirstHitExcursionSchedule
      (TerminalGlobalExitSplice.wordWalk start word) outer inner
      word.length count) :
    (scanWord outer inner start word).completed =
      completedExcursionCount
        (TerminalGlobalExitSplice.wordWalk start word) outer inner word.length := by
  rw [scanWord_eq_scanThrough_wordWalk]
  exact scanThrough_completed_eq_completedExcursionCount_of_schedule
    hdisjoint schedule

/-- The direction fold computes the first-hit completed-excursion count at
every finite word horizon. -/
theorem scanWord_completed_eq_completedExcursionCount
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (start : Point)
    (word : List Direction) :
    (scanWord outer inner start word).completed =
      completedExcursionCount
        (TerminalGlobalExitSplice.wordWalk start word) outer inner word.length := by
  rw [scanWord_eq_scanThrough_wordWalk]
  exact scanThrough_completed_eq_completedExcursionCount
    _ _ _ hdisjoint word.length

end

end Erdos1165.TerminalBoundaryScan
