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

import ErdosProblems.Erdos1165.AppendixLocalTimeTransfer

/-!
# Pathwise terminal-excursion visit counts

This module closes the deterministic bookkeeping part of HLOZ Appendix A.7.
For the terminal scale, an inward excursion ends when the walk reaches
`∂D(x,n^6)`.  Its associated inner segment then runs until the next visit to
`∂D(x,n^9)`.  The visits to `x` in these half-open inner segments are
pairwise disjoint, and their sum is bounded by the full local time through
the stopping horizon.

Consequently every successful point canonically supplies the
`TerminalVisitRealization` consumed by `AppendixLocalTimeTransfer`; no
pathwise realization hypothesis is needed.  The remaining probabilistic
statement is the law of these visit counts conditional on their entrance
data.
-/

open Set
open scoped BigOperators

namespace Erdos1165.TerminalExcursionPathwise

noncomputable section

open ThickPoint

/-! ## Order properties of the truncated excursion clocks -/

lemma firstHitThrough_le_sentinel (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ) :
    firstHitThrough s A start horizon ≤ horizon + 1 := by
  by_cases h : (hitTimesThrough s A start horizon).Nonempty
  · have hm := firstHitThrough_mem_of_nonempty s A start horizon h
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2.trans (Nat.le_succ _)
  · rw [firstHitThrough_eq_sentinel_of_empty s A start horizon h]

lemma le_firstHitThrough (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ)
    (hstart : start ≤ horizon + 1) :
    start ≤ firstHitThrough s A start horizon := by
  by_cases h : (hitTimesThrough s A start horizon).Nonempty
  · have hm := firstHitThrough_mem_of_nonempty s A start horizon h
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  · rw [firstHitThrough_eq_sentinel_of_empty s A start horizon h]
    exact hstart

lemma excursionStep_le_sentinel (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon start : ℕ) :
    excursionStep s outer inner horizon start ≤ horizon + 1 := by
  exact firstHitThrough_le_sentinel s inner
    (firstHitThrough s outer start horizon) horizon

lemma iterate_excursionStep_le_sentinel (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    (excursionStep s outer inner horizon)^[j] 0 ≤ horizon + 1 := by
  induction j with
  | zero => simp
  | succ j _ih =>
      rw [Function.iterate_succ_apply']
      exact excursionStep_le_sentinel s outer inner horizon _

lemma iterate_excursionStep_le_succ (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    (excursionStep s outer inner horizon)^[j] 0 ≤
      (excursionStep s outer inner horizon)^[j + 1] 0 := by
  rw [Function.iterate_succ_apply']
  change (excursionStep s outer inner horizon)^[j] 0 ≤
    firstHitThrough s inner
      (firstHitThrough s outer
        ((excursionStep s outer inner horizon)^[j] 0) horizon) horizon
  exact (le_firstHitThrough s outer _ horizon
      (iterate_excursionStep_le_sentinel s outer inner horizon j)).trans
    (le_firstHitThrough s inner _ horizon
      (firstHitThrough_le_sentinel s outer _ horizon))

lemma monotone_iterate_excursionStep (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) :
    Monotone fun j ↦ (excursionStep s outer inner horizon)^[j] 0 := by
  exact monotone_nat_of_le_succ
    (iterate_excursionStep_le_succ s outer inner horizon)

lemma excursionFinish_eq_iterate_succ (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionFinish s outer inner horizon j =
      (excursionStep s outer inner horizon)^[j + 1] 0 := by
  rw [Function.iterate_succ_apply']
  rfl

lemma excursionFinish_le_next_start (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionFinish s outer inner horizon j ≤
      excursionStart s outer inner horizon (j + 1) := by
  rw [excursionFinish_eq_iterate_succ]
  unfold excursionStart
  apply le_firstHitThrough
  exact iterate_excursionStep_le_sentinel s outer inner horizon (j + 1)

lemma excursionFinish_mono (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) :
    Monotone fun j ↦ excursionFinish s outer inner horizon j := by
  intro i j hij
  simp only [excursionFinish_eq_iterate_succ]
  exact monotone_iterate_excursionStep s outer inner horizon
    (Nat.add_le_add_right hij 1)

lemma excursionStart_le_finish (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionStart s outer inner horizon j ≤
      excursionFinish s outer inner horizon j := by
  unfold excursionFinish
  exact le_firstHitThrough s inner _ horizon
    (firstHitThrough_le_sentinel s outer _ horizon)

lemma excursionFinish_le_start_of_lt (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) {i j : ℕ} (hij : i < j) :
    excursionFinish s outer inner horizon i ≤
      excursionStart s outer inner horizon j := by
  rw [excursionFinish_eq_iterate_succ]
  unfold excursionStart
  exact (monotone_iterate_excursionStep s outer inner horizon
      (Nat.succ_le_iff.mpr hij)).trans
    (le_firstHitThrough s outer _ horizon
      (iterate_excursionStep_le_sentinel s outer inner horizon j))

/-! ## The disjoint inner visit segments -/

/-- Times spent in the inner part following inward excursion `j`, stopping
just before the next visit to the outer terminal boundary. -/
def innerVisitTimes (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (x : Point) (j : ℕ) : Finset ℕ :=
  (Finset.Ico (excursionFinish s outer inner horizon j)
      (excursionStart s outer inner horizon (j + 1))).filter fun t ↦ s t = x

/-- Number of visits carried by the inner part following excursion `j`. -/
def innerVisitCount (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (x : Point) (j : ℕ) : ℕ :=
  (innerVisitTimes s outer inner horizon x j).card

lemma innerVisitTimes_pairwiseDisjoint (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (x : Point) :
    Set.PairwiseDisjoint Set.univ (innerVisitTimes s outer inner horizon x) := by
  intro i _hi j _hj hij
  change Disjoint (innerVisitTimes s outer inner horizon x i)
    (innerVisitTimes s outer inner horizon x j)
  rw [Finset.disjoint_left]
  intro t hti htj
  have hti' := Finset.mem_Ico.mp (Finset.mem_filter.mp hti).1
  have htj' := Finset.mem_Ico.mp (Finset.mem_filter.mp htj).1
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have horder : excursionStart s outer inner horizon (i + 1) ≤
        excursionFinish s outer inner horizon j :=
      (excursionStart_le_finish s outer inner horizon (i + 1)).trans
        (excursionFinish_mono s outer inner horizon (Nat.succ_le_iff.mpr hijlt))
    omega
  · have horder : excursionStart s outer inner horizon (j + 1) ≤
        excursionFinish s outer inner horizon i :=
      (excursionStart_le_finish s outer inner horizon (j + 1)).trans
        (excursionFinish_mono s outer inner horizon (Nat.succ_le_iff.mpr hjilt))
    omega

lemma innerVisitTimes_subset_localTime (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (x : Point) {j : ℕ} :
    innerVisitTimes s outer inner horizon x j ⊆
      (Finset.range (horizon + 1)).filter fun t ↦ s t = x := by
  intro t ht
  have ht' := Finset.mem_filter.mp ht
  have htIco := Finset.mem_Ico.mp ht'.1
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr ?_, ht'.2⟩
  exact htIco.2.trans_le
    (firstHitThrough_le_sentinel s outer
      ((excursionStep s outer inner horizon)^[j + 1] 0) horizon)

theorem sum_innerVisitCount_le_localTimeThrough
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) (x : Point) {m : ℕ} :
    ∑ j : Fin m, innerVisitCount s outer inner horizon x j ≤
      localTimeThrough s horizon x := by
  classical
  let visits : Fin m → Finset ℕ := fun j ↦
    innerVisitTimes s outer inner horizon x j
  have hdisjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint visits :=
    by
      intro i _hi j _hj hij
      exact innerVisitTimes_pairwiseDisjoint s outer inner horizon x
        (Set.mem_univ i) (Set.mem_univ j) fun hval ↦ hij (Fin.ext hval)
  have hsubset : (Finset.univ.biUnion visits) ⊆
      (Finset.range (horizon + 1)).filter fun t ↦ s t = x := by
    rw [Finset.biUnion_subset]
    intro j _hj
    exact innerVisitTimes_subset_localTime s outer inner horizon x
  calc
    ∑ j : Fin m, innerVisitCount s outer inner horizon x j =
        (Finset.univ.biUnion visits).card := by
          rw [Finset.card_biUnion hdisjoint]
          simp [innerVisitCount, visits]
    _ ≤ ((Finset.range (horizon + 1)).filter fun t ↦ s t = x).card :=
      Finset.card_le_card hsubset
    _ = localTimeThrough s horizon x := rfl

/-! ## Specialization to HLOZ's terminal radii -/

/-- The terminal outer boundary `∂D(x,r_{n,n}) = ∂D(x,n^9)`. -/
def terminalOuterBoundary (n : ℕ) (x : Point) : Set Point :=
  discBoundary x (scaleRadius n n)

/-- The terminal inner boundary `∂D(x,r_{n,n+1}) = ∂D(x,n^6)`. -/
def terminalInnerBoundary (n : ℕ) (x : Point) : Set Point :=
  discBoundary x (scaleRadius n (n + 1))

/-- Number of completed terminal inward excursions. -/
noncomputable def terminalCompletedExcursionCount
    (s : WalkPath) (n horizon : ℕ) (x : Point) : ℕ := by
  classical
  exact completedExcursionCount s (terminalOuterBoundary n x)
    (terminalInnerBoundary n x) horizon

/-- Actual visits to `x` made after the `j`-th terminal inward excursion and
before the next return to the terminal outer boundary. -/
def terminalExcursionVisits (s : WalkPath) (n horizon : ℕ) (x : Point)
    (j : ℕ) : ℕ := by
  classical
  exact innerVisitCount s (terminalOuterBoundary n x)
    (terminalInnerBoundary n x) horizon x j

/-- The next outer-boundary time ending the inner segment after excursion
`j`.  The wrapper fixes the classical decidable-predicate instances so later
statements do not expose implementation typeclasses. -/
noncomputable def terminalSegmentExitTime
    (s : WalkPath) (n horizon : ℕ) (x : Point) (j : ℕ) : ℕ := by
  classical
  exact excursionStart s (terminalOuterBoundary n x) (terminalInnerBoundary n x)
    horizon (j + 1)

/-- The deterministic vector of visits carried by the selected terminal
excursions.  The global outer-exit geometry below proves that even the final
selected inner-to-outer segment is complete before the stopping horizon. -/
def terminalVisitVector (s : WalkPath) (n horizon : ℕ) (profileDelta : ℝ)
    (x : Point) :
    Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → ℕ :=
  fun j ↦ terminalExcursionVisits s n horizon x j

lemma excursionProfile_terminal_eq_completedExcursionCount
    (s : WalkPath) (n horizon : ℕ) (x : Point) :
    excursionProfile s n horizon x ⟨n + 1, by omega⟩ =
      terminalCompletedExcursionCount s n horizon x := by
  classical
  simp [excursionProfile, terminalCompletedExcursionCount,
    terminalOuterBoundary, terminalInnerBoundary]

lemma finish_le_horizon_of_lt_completedExcursionCount
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) {j : ℕ}
    (hj : j < completedExcursionCount s outer inner horizon) :
    excursionFinish s outer inner horizon j ≤ horizon := by
  classical
  let completed := (Finset.range (horizon + 1)).filter fun i ↦
    excursionFinish s outer inner horizon i ≤ horizon
  have hcard : completed.card = completedExcursionCount s outer inner horizon := rfl
  by_contra hjnot
  have hsubset : completed ⊆ Finset.range j := by
    intro i hi
    have hiFinish := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_range]
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    have hmono := excursionFinish_mono s outer inner horizon hji
    exact hjnot (hmono.trans hiFinish)
  have hcardUpper : completed.card ≤ j := by
    simpa using Finset.card_le_card hsubset
  rw [hcard] at hcardUpper
  omega

/-! ## Completing the final inner-to-outer segment by global-exit geometry -/

/-- A nearest-neighbor path which is in `A` at `start` and outside `A` at
`horizon` hits the inner vertex boundary of `A` between those times. -/
lemma exists_innerBoundary_between_of_exit
    (s : WalkPath) (A : Set Point)
    (hstep : ∀ k, Adjacent (s k) (s (k + 1)))
    {start horizon : ℕ} (hstart : start ≤ horizon)
    (hin : s start ∈ A) (hout : s horizon ∉ A) :
    ∃ k, start ≤ k ∧ k ≤ horizon ∧ s k ∈ innerBoundary A := by
  classical
  let P : ℕ → Prop := fun t ↦ start ≤ t ∧ t ≤ horizon ∧ s t ∉ A
  have hP : ∃ t, P t := ⟨horizon, hstart, le_rfl, hout⟩
  let t := Nat.find hP
  have htP : P t := Nat.find_spec hP
  have hstartlt : start < t := by
    rcases lt_or_eq_of_le htP.1 with hlt | heq
    · exact hlt
    · exact (htP.2.2 (heq ▸ hin)).elim
  let k := t - 1
  have hkt : k < t := by omega
  have hstartk : start ≤ k := by omega
  have hkA : s k ∈ A := by
    by_contra hk
    have hkP : P k := ⟨hstartk, hkt.le.trans htP.2.1, hk⟩
    exact (Nat.not_le_of_gt hkt) (Nat.find_min' hP hkP)
  have hsucc : k + 1 = t := by omega
  refine ⟨k, hstartk, hkt.le.trans htP.2.1, hkA, s t, htP.2.2, ?_⟩
  simpa [hsucc] using hstep k

/-- Consequently the finite first-hit clock for the inner boundary is not a
sentinel. -/
lemma firstHitThrough_innerBoundary_le_of_exit
    (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ innerBoundary A)]
    (hstep : ∀ k, Adjacent (s k) (s (k + 1)))
    {start horizon : ℕ} (hstart : start ≤ horizon)
    (hin : s start ∈ A) (hout : s horizon ∉ A) :
    firstHitThrough s (innerBoundary A) start horizon ≤ horizon := by
  classical
  obtain ⟨k, hstartk, hkhorizon, hk⟩ :=
    exists_innerBoundary_between_of_exit s A hstep hstart hin hout
  apply (firstHitThrough_le_horizon_iff s (innerBoundary A) start horizon).2
  exact ⟨k, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hstartk, hkhorizon⟩, hk⟩⟩

lemma abs_fst_sub_le_latticeDistance (x y : Point) :
    |(((x.1 - y.1 : ℤ) : ℝ))| ≤ latticeDistance x y := by
  let a : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let b : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  have hsum : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq := Real.sq_sqrt hsum
  have ha0 : 0 ≤ |a| := abs_nonneg _
  have haSq : |a| ^ 2 = a ^ 2 := sq_abs a
  unfold latticeDistance squaredDistance
  change |a| ≤ Real.sqrt (a ^ 2 + b ^ 2)
  nlinarith [sq_nonneg b]

lemma abs_snd_sub_le_latticeDistance (x y : Point) :
    |(((x.2 - y.2 : ℤ) : ℝ))| ≤ latticeDistance x y := by
  let a : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let b : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  have hsum : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq := Real.sq_sqrt hsum
  have hb0 : 0 ≤ |b| := abs_nonneg _
  have hbSq : |b| ^ 2 = b ^ 2 := sq_abs b
  unfold latticeDistance squaredDistance
  change |b| ≤ Real.sqrt (a ^ 2 + b ^ 2)
  nlinarith [sq_nonneg a]

lemma scaleRadius_self_le_scaleRadius_zero (n : ℕ) :
    scaleRadius n n ≤ scaleRadius n 0 := by
  rw [scaleRadius_of_le le_rfl, regularRadius_self,
    scaleRadius_of_le (Nat.zero_le n), regularRadius]
  simp only [Nat.cast_zero, sub_zero]
  have hexp : 1 ≤ Real.exp (n : ℝ) := Real.one_le_exp (Nat.cast_nonneg n)
  have hpow : 0 ≤ (n : ℝ) ^ 9 := by positivity
  nlinarith

lemma one_le_scaleRadius_zero (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ scaleRadius n 0 := by
  simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
    Nat.cast_zero, sub_zero]
  have hexp : 1 ≤ Real.exp (n : ℝ) := Real.one_le_exp (Nat.cast_nonneg n)
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ 9 := one_le_pow₀ hnReal
  nlinarith

lemma candidate_coordinate_abs_le_three_radius
    {n : ℕ} {x : Point} (hx : x ∈ candidateBox n) :
    |(x.1 : ℝ)| ≤ 3 * scaleRadius n 0 ∧
      |(x.2 : ℝ)| ≤ 3 * scaleRadius n 0 := by
  have hr0 : 0 ≤ scaleRadius n 0 := by
    simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
      Nat.cast_zero, sub_zero]
    positivity
  have hxmem := mem_candidateBox.mp hx
  have hcoord (z : ℤ) (hz : z ∈ candidateInterval n) :
      |(z : ℝ)| ≤ 3 * scaleRadius n 0 := by
    have hzBounds := mem_candidateInterval.mp hz
    have hz0Int : (0 : ℤ) ≤ z :=
      (Int.ceil_nonneg (mul_nonneg (by norm_num) hr0)).trans hzBounds.1
    have hz0 : (0 : ℝ) ≤ z := by exact_mod_cast hz0Int
    have hzFloor : (z : ℝ) ≤ (⌊3 * scaleRadius n 0⌋ : ℤ) := by
      exact_mod_cast hzBounds.2
    rw [abs_of_nonneg hz0]
    exact hzFloor.trans (Int.floor_le _)
  exact ⟨hcoord x.1 hxmem.1, hcoord x.2 hxmem.2⟩

/-- The terminal disc around a candidate point has a full nearest-neighbor
buffer inside the global outer disc. -/
lemma adjacent_terminalDisc_mem_globalDisc
    {n : ℕ} (hn : 1 ≤ n) {x y z : Point}
    (hx : x ∈ candidateBox n)
    (hy : y ∈ disc x (scaleRadius n n)) (hyz : Adjacent y z) :
    z ∈ disc (0, 0) (outerScale n) := by
  let r : ℝ := scaleRadius n 0
  have hr1 : 1 ≤ r := one_le_scaleRadius_zero n hn
  have hr0 : 0 ≤ r := hr1.trans' zero_le_one
  have hterminal : scaleRadius n n ≤ r := scaleRadius_self_le_scaleRadius_zero n
  have hyDist : latticeDistance x y ≤ r := hy.trans hterminal
  have hxy1 : |(((x.1 - y.1 : ℤ) : ℝ))| ≤ r :=
    (abs_fst_sub_le_latticeDistance x y).trans hyDist
  have hxy2 : |(((x.2 - y.2 : ℤ) : ℝ))| ≤ r :=
    (abs_snd_sub_le_latticeDistance x y).trans hyDist
  have hxAbs := candidate_coordinate_abs_le_three_radius hx
  have hy1 : |(y.1 : ℝ)| ≤ 4 * r := by
    calc
      |(y.1 : ℝ)| = |(x.1 : ℝ) - ((x.1 - y.1 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(x.1 : ℝ)| + |(((x.1 - y.1 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 4 * r := by dsimp only [r] at *; linarith
  have hy2 : |(y.2 : ℝ)| ≤ 4 * r := by
    calc
      |(y.2 : ℝ)| = |(x.2 : ℝ) - ((x.2 - y.2 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(x.2 : ℝ)| + |(((x.2 - y.2 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 4 * r := by dsimp only [r] at *; linarith
  have hyz1Nat : (y.1 - z.1).natAbs ≤ 1 := by
    unfold Adjacent at hyz
    omega
  have hyz2Nat : (y.2 - z.2).natAbs ≤ 1 := by
    unfold Adjacent at hyz
    omega
  have hyz1 : |(((y.1 - z.1 : ℤ) : ℝ))| ≤ 1 := by
    have hsquareInt : (y.1 - z.1) ^ 2 ≤ (1 : ℤ) ^ 2 :=
      Int.natAbs_le_iff_sq_le.mp (by simpa using hyz1Nat)
    have hsquare : (((y.1 - z.1 : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      exact_mod_cast hsquareInt
    nlinarith [sq_abs (((y.1 - z.1 : ℤ) : ℝ)),
      abs_nonneg (((y.1 - z.1 : ℤ) : ℝ))]
  have hyz2 : |(((y.2 - z.2 : ℤ) : ℝ))| ≤ 1 := by
    have hsquareInt : (y.2 - z.2) ^ 2 ≤ (1 : ℤ) ^ 2 :=
      Int.natAbs_le_iff_sq_le.mp (by simpa using hyz2Nat)
    have hsquare : (((y.2 - z.2 : ℤ) : ℝ)) ^ 2 ≤ 1 := by
      exact_mod_cast hsquareInt
    nlinarith [sq_abs (((y.2 - z.2 : ℤ) : ℝ)),
      abs_nonneg (((y.2 - z.2 : ℤ) : ℝ))]
  have hz1 : |(z.1 : ℝ)| ≤ 5 * r := by
    calc
      |(z.1 : ℝ)| = |(y.1 : ℝ) - ((y.1 - z.1 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(y.1 : ℝ)| + |(((y.1 - z.1 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 5 * r := by linarith
  have hz2 : |(z.2 : ℝ)| ≤ 5 * r := by
    calc
      |(z.2 : ℝ)| = |(y.2 : ℝ) - ((y.2 - z.2 : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(y.2 : ℝ)| + |(((y.2 - z.2 : ℤ) : ℝ))| := abs_sub _ _
      _ ≤ 5 * r := by linarith
  change latticeDistance (0, 0) z ≤ outerScale n
  rw [outerScale_eq_sixteen_mul_radius_zero]
  unfold latticeDistance squaredDistance
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hz10 : 0 ≤ |(z.1 : ℝ)| := abs_nonneg _
    have hz20 : 0 ≤ |(z.2 : ℝ)| := abs_nonneg _
    have hz1sq : |(z.1 : ℝ)| ^ 2 = (z.1 : ℝ) ^ 2 := sq_abs _
    have hz2sq : |(z.2 : ℝ)| ^ 2 = (z.2 : ℝ) ^ 2 := sq_abs _
    push_cast
    nlinarith

/-- Hence a point of the terminal disc cannot lie on the global inner vertex
boundary: every one of its nearest neighbors remains in the global disc. -/
lemma terminalDisc_disjoint_globalBoundary
    {n : ℕ} (hn : 1 ≤ n) {x y : Point}
    (hx : x ∈ candidateBox n) (hy : y ∈ disc x (scaleRadius n n)) :
    y ∉ discBoundary (0, 0) (outerScale n) := by
  rintro ⟨_hyGlobal, z, hzOutside, hyz⟩
  exact hzOutside (adjacent_terminalDisc_mem_globalDisc hn hx hy hyz)

/-- Every selected terminal segment is complete once the path is known to be
outside the terminal outer disc at the global stopping horizon.  The final
coordinate uses the nearest-neighbor crossing argument rather than an extra
completed inward excursion. -/
lemma terminalVisitSegment_complete_of_success_of_exit
    {s : WalkPath} {n horizon : ℕ} {profileDelta : ℝ} {x : Point}
    (hn : 1 ≤ n)
    (hx : SuccessfulPoint s n horizon profileDelta x)
    (hstep : ∀ k, Adjacent (s k) (s (k + 1)))
    (hout : s horizon ∉ disc x (scaleRadius n n))
    (j : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta)) :
    terminalSegmentExitTime s n horizon x j ≤ horizon := by
  classical
  have hrequired : AppendixLocalTime.requiredTerminalCount n profileDelta ≤
      terminalCompletedExcursionCount s n horizon x := by
    simpa [AppendixLocalTime.terminalCount,
      excursionProfile_terminal_eq_completedExcursionCount] using
      (AppendixLocalTime.requiredTerminalCount_le_terminalCount hx.2)
  have hjltCompleted : (j : ℕ) <
      terminalCompletedExcursionCount s n horizon x :=
    j.isLt.trans_le hrequired
  have hfinish : excursionFinish s (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) horizon j ≤ horizon :=
    finish_le_horizon_of_lt_completedExcursionCount s
      (terminalOuterBoundary n x) (terminalInnerBoundary n x) horizon
      hjltCompleted
  have hinnerBoundary : s (excursionFinish s (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) horizon j) ∈ terminalInnerBoundary n x :=
    excursionFinish_mem_inner_of_le s (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) horizon j hfinish
  have hin : s (excursionFinish s (terminalOuterBoundary n x)
      (terminalInnerBoundary n x) horizon j) ∈ disc x (scaleRadius n n) := by
    have hinnerDisc : s (excursionFinish s (terminalOuterBoundary n x)
        (terminalInnerBoundary n x) horizon j) ∈
        disc x (scaleRadius n (n + 1)) := hinnerBoundary.1
    exact hinnerDisc.trans
      (terminalRadius_le_regularRadius_self n hn)
  have hcross := firstHitThrough_innerBoundary_le_of_exit s
    (disc x (scaleRadius n n)) hstep hfinish hin hout
  unfold terminalSegmentExitTime excursionStart
  rw [← excursionFinish_eq_iterate_succ s (terminalOuterBoundary n x)
    (terminalInnerBoundary n x) horizon j]
  exact hcross

/-- Literal stopped-event form: candidate-box geometry shows that the global
outer-boundary point is outside the candidate-centered terminal disc, so all
`requiredTerminalCount` inner-to-outer visit segments are complete. -/
lemma terminalVisitSegment_complete_of_stopped_success
    {s : WalkPath} {n horizon : ℕ} {profileDelta : ℝ} {x : Point}
    (hn : 1 ≤ n) (hexit : IsOuterExitTime s n horizon)
    (hx : SuccessfulPoint s n horizon profileDelta x)
    (hstep : ∀ k, Adjacent (s k) (s (k + 1)))
    (j : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta)) :
    terminalSegmentExitTime s n horizon x j ≤ horizon := by
  apply terminalVisitSegment_complete_of_success_of_exit hn hx hstep
  intro hterminal
  exact (terminalDisc_disjoint_globalBoundary hn hx.1 hterminal) hexit.1

/-- Every successful point canonically determines the first required number
of terminal visit counts, and their sum is bounded by its actual local time. -/
def terminalVisitRealizationOfSuccessfulPoint
    {s : WalkPath} {n horizon : ℕ} {profileDelta : ℝ} {x : Point}
    (_hx : SuccessfulPoint s n horizon profileDelta x) :
    AppendixLocalTimeTransfer.TerminalVisitRealization s horizon
      (AppendixLocalTime.requiredTerminalCount n profileDelta) x where
  visits := terminalVisitVector s n horizon profileDelta x
  contained := by
    classical
    apply sum_innerVisitCount_le_localTimeThrough

/-- Fully pathwise form of Appendix A.7: once the canonical terminal visit
vector crosses the threshold, the point is thick-successful. -/
theorem thickSuccessfulPoint_of_terminalExcursionVisits
    {s : WalkPath} {n horizon : ℕ} {profileDelta thickDelta : ℝ} {x : Point}
    (hx : SuccessfulPoint s n horizon profileDelta x)
    (hthick : thickThreshold n thickDelta ≤
      AppendixLocalTime.totalVisits
        (terminalVisitVector s n horizon profileDelta x)) :
    ThickSuccessfulPoint s n horizon profileDelta thickDelta x := by
  let R := terminalVisitRealizationOfSuccessfulPoint hx
  have hthickR : thickThreshold n thickDelta ≤
      AppendixLocalTime.totalVisits R.visits := by
    simpa [R, terminalVisitRealizationOfSuccessfulPoint] using hthick
  exact (AppendixLocalTimeTransfer.thickSuccessfulPoint_of_terminalRealization
    hx R hthickR).2

end

end Erdos1165.TerminalExcursionPathwise
