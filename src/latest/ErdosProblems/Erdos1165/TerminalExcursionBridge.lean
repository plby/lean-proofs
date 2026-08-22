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

import ErdosProblems.Erdos1165.TerminalKernelRadial
import ErdosProblems.Erdos1165.SpatialRecurrence
import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-!
# Unbounded stopped annular excursions

This file constructs the unbounded alternating entrance/exit clocks needed
to realize the terminal excursions in the HLOZ Appendix.  Unlike the finite
sentinel clocks in `ThickPoint`, these clocks take values in `WithTop ℕ` and
therefore record non-attainment honestly.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace Erdos1165.TerminalExcursionBridge

noncomputable section

/-! ## First hit of a set after a possibly-infinite stopping time -/

/-- Advance a possibly-infinite clock by one step. -/
def stoppingTimeSucc (tau : StepPath → WithTop ℕ) : StepPath → WithTop ℕ :=
  fun omega ↦ tau omega + 1

/-- Advancing a stopping time by one preserves the stopping-time property. -/
theorem isStoppingTime_succ
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) :
    IsStoppingTime incrementFiltration (stoppingTimeSucc tau) := by
  intro N
  cases N with
  | zero =>
      have heq : {omega : StepPath | stoppingTimeSucc tau omega ≤ 0} = ∅ := by
        ext omega
        simp [stoppingTimeSucc]
      have hempty : MeasurableSet[incrementFiltration 0] (∅ : Set StepPath) :=
        (incrementFiltration 0).measurableSet_empty
      exact heq.symm ▸ hempty
  | succ N =>
      have heq : {omega : StepPath | stoppingTimeSucc tau omega ≤ (N + 1 : ℕ)} =
          {omega | tau omega ≤ (N : WithTop ℕ)} := by
        ext omega
        simp [stoppingTimeSucc]
      have hmeas : MeasurableSet[incrementFiltration (N + 1)]
          {omega | tau omega ≤ (N : WithTop ℕ)} :=
        incrementFiltration.mono (Nat.le_succ N) _ (htau N)
      exact heq.symm ▸ hmeas

/-- The first time at or after `tau` at which the canonical walk enters `A`.
If `tau = ⊤`, or if no such time exists, the value is `⊤`. -/
noncomputable def firstHitSetAfter
    (tau : StepPath → WithTop ℕ) (A : Set Point) (omega : StepPath) : WithTop ℕ := by
  classical
  exact if h : ∃ n : ℕ, tau omega ≤ (n : WithTop ℕ) ∧ trajectory omega n ∈ A then
    (Nat.find h : WithTop ℕ)
  else ⊤

theorem firstHitSetAfter_le_iff
    (tau : StepPath → WithTop ℕ) (A : Set Point) (omega : StepPath) (N : ℕ) :
    firstHitSetAfter tau A omega ≤ N ↔
      ∃ n ≤ N, tau omega ≤ (n : WithTop ℕ) ∧ trajectory omega n ∈ A := by
  classical
  unfold firstHitSetAfter
  split_ifs with h
  · constructor
    · intro hle
      refine ⟨Nat.find h, ?_, (Nat.find_spec h).1, (Nat.find_spec h).2⟩
      exact WithTop.coe_le_coe.mp hle
    · rintro ⟨n, hnN, hnTau, hnA⟩
      exact_mod_cast (Nat.find_min' h ⟨hnTau, hnA⟩).trans hnN
  · constructor
    · intro hle
      simp at hle
    · rintro ⟨n, _hnN, hnTau, hnA⟩
      exact (h ⟨n, hnTau, hnA⟩).elim

theorem firstHitSetAfter_eq_coe_iff
    (tau : StepPath → WithTop ℕ) (A : Set Point) (omega : StepPath) (N : ℕ) :
    firstHitSetAfter tau A omega = N ↔
      tau omega ≤ (N : WithTop ℕ) ∧ trajectory omega N ∈ A ∧
        ∀ n < N, ¬(tau omega ≤ (n : WithTop ℕ) ∧ trajectory omega n ∈ A) := by
  constructor
  · intro hN
    have hle : firstHitSetAfter tau A omega ≤ N := by rw [hN]
    obtain ⟨n, hnN, hnTau, hnA⟩ :=
      (firstHitSetAfter_le_iff tau A omega N).mp hle
    have hnEq : n = N := by
      by_contra hne
      have hnlt : n < N := lt_of_le_of_ne hnN hne
      have hsmall : firstHitSetAfter tau A omega ≤ n :=
        (firstHitSetAfter_le_iff tau A omega n).mpr
          ⟨n, le_rfl, hnTau, hnA⟩
      rw [hN] at hsmall
      exact (not_le_of_gt hnlt) (WithTop.coe_le_coe.mp hsmall)
    subst n
    refine ⟨hnTau, hnA, ?_⟩
    intro n hn hhit
    have hsmall : firstHitSetAfter tau A omega ≤ n :=
      (firstHitSetAfter_le_iff tau A omega n).mpr
        ⟨n, le_rfl, hhit.1, hhit.2⟩
    rw [hN] at hsmall
    exact (not_le_of_gt hn) (WithTop.coe_le_coe.mp hsmall)
  · rintro ⟨hTau, hA, hminimal⟩
    apply le_antisymm
    · exact (firstHitSetAfter_le_iff tau A omega N).mpr
        ⟨N, le_rfl, hTau, hA⟩
    · by_contra hnot
      have hlt : firstHitSetAfter tau A omega < (N : WithTop ℕ) :=
        lt_of_not_ge hnot
      have htop : firstHitSetAfter tau A omega ≠ ⊤ :=
        WithTop.lt_top_iff_ne_top.mp (hlt.trans (WithTop.coe_lt_top N))
      lift firstHitSetAfter tau A omega to ℕ using htop with n hn
      have hnlt : n < N := by
        exact WithTop.coe_lt_coe.mp hlt
      have hle : firstHitSetAfter tau A omega ≤ n := by
        rw [← hn]
        exact le_rfl
      obtain ⟨q, hqn, hqTau, hqA⟩ :=
        (firstHitSetAfter_le_iff tau A omega n).mp hle
      exact hminimal q (hqn.trans_lt hnlt) ⟨hqTau, hqA⟩

theorem le_firstHitSetAfter
    (tau : StepPath → WithTop ℕ) (A : Set Point) (omega : StepPath) :
    tau omega ≤ firstHitSetAfter tau A omega := by
  classical
  unfold firstHitSetAfter
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_top

lemma measurableSet_trajectory_mem_incrementFiltration
    (n : ℕ) (A : Set Point) :
    MeasurableSet[incrementFiltration n] {omega : StepPath | trajectory omega n ∈ A} := by
  rw [incrementFiltration_apply]
  let C : Set (Fin n → Direction) := {u | markovBlockDisplacement u ∈ A}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath | trajectory omega n ∈ A} = stepPrefix n ⁻¹' C := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, C]
    rw [trajectory_eq_markovBlockDisplacement_stepPrefix]
  rw [heq]
  exact ⟨C, hC, rfl⟩

/-- First hitting a set after an arbitrary stopping time is again a stopping
time.  Countability of the lattice makes every target set measurable. -/
theorem isStoppingTime_firstHitSetAfter
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (A : Set Point) :
    IsStoppingTime incrementFiltration (firstHitSetAfter tau A) := by
  intro N
  have heq : {omega : StepPath | firstHitSetAfter tau A omega ≤ N} =
      ⋃ n : Fin (N + 1),
        {omega | tau omega ≤ (n : ℕ)} ∩
          {omega | trajectory omega n ∈ A} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [firstHitSetAfter_le_iff]
    constructor
    · rintro ⟨n, hnN, hnTau, hnA⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hnN⟩, hnTau, hnA⟩
    · rintro ⟨n, hnTau, hnA⟩
      exact ⟨n, Nat.le_of_lt_succ n.isLt, hnTau, hnA⟩
  have hmeas : MeasurableSet[incrementFiltration N]
      (⋃ n : Fin (N + 1),
        {omega | tau omega ≤ (n : ℕ)} ∩
          {omega | trajectory omega n ∈ A}) :=
    MeasurableSet.iUnion fun n ↦
    (incrementFiltration.mono (Nat.le_of_lt_succ n.isLt) _ (htau n)).inter
      (incrementFiltration.mono (Nat.le_of_lt_succ n.isLt) _
        (measurableSet_trajectory_mem_incrementFiltration n A))
  rw [← heq] at hmeas
  exact hmeas

theorem firstHitSetAfter_mem_of_eq
    {tau : StepPath → WithTop ℕ} {A : Set Point} {omega : StepPath} {n : ℕ}
    (h : firstHitSetAfter tau A omega = n) :
    trajectory omega n ∈ A :=
  (firstHitSetAfter_eq_coe_iff tau A omega n).mp h |>.2.1

/-! ## Alternating annular clock ladder -/

/-- Starting from `tau`, alternately hit `outer` and `inner`.  Thus clock
`2j+1` is the `j`-th outer hit and clock `2j+2` the following inner entrance. -/
noncomputable def alternatingAnnularClock
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point) :
    ℕ → StepPath → WithTop ℕ
  | 0 => tau
  | j + 1 => firstHitSetAfter (alternatingAnnularClock tau outer inner j)
      (if Even j then outer else inner)

@[simp] theorem alternatingAnnularClock_zero
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point) :
    alternatingAnnularClock tau outer inner 0 = tau := rfl

theorem alternatingAnnularClock_succ
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point) (j : ℕ) :
    alternatingAnnularClock tau outer inner (j + 1) =
      firstHitSetAfter (alternatingAnnularClock tau outer inner j)
        (if Even j then outer else inner) := rfl

theorem isStoppingTime_alternatingAnnularClock
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (outer inner : Set Point) :
    ∀ j, IsStoppingTime incrementFiltration
      (alternatingAnnularClock tau outer inner j) := by
  intro j
  induction j with
  | zero => exact htau
  | succ j ih =>
      rw [alternatingAnnularClock_succ]
      exact isStoppingTime_firstHitSetAfter ih _

theorem alternatingAnnularClock_mono_step
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point)
    (j : ℕ) (omega : StepPath) :
    alternatingAnnularClock tau outer inner j omega ≤
      alternatingAnnularClock tau outer inner (j + 1) omega := by
  rw [alternatingAnnularClock_succ]
  exact le_firstHitSetAfter _ _ _

/-- The inner-boundary entrance time of terminal excursion `j`. -/
noncomputable def terminalEntranceTime
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point) (j : ℕ) :
    StepPath → WithTop ℕ :=
  alternatingAnnularClock tau outer inner (2 * j + 2)

/-- The outer-boundary exit time following terminal entrance `j`. -/
noncomputable def terminalExitTime
    (tau : StepPath → WithTop ℕ) (outer inner : Set Point) (j : ℕ) :
    StepPath → WithTop ℕ :=
  alternatingAnnularClock tau outer inner (2 * j + 3)

theorem isStoppingTime_terminalEntranceTime
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (outer inner : Set Point) (j : ℕ) :
    IsStoppingTime incrementFiltration (terminalEntranceTime tau outer inner j) :=
  isStoppingTime_alternatingAnnularClock htau outer inner (2 * j + 2)

theorem isStoppingTime_terminalExitTime
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (outer inner : Set Point) (j : ℕ) :
    IsStoppingTime incrementFiltration (terminalExitTime tau outer inner j) :=
  isStoppingTime_alternatingAnnularClock htau outer inner (2 * j + 3)

theorem terminalEntranceTime_mem_inner_of_eq
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point}
    {j n : ℕ} {omega : StepPath}
    (h : terminalEntranceTime tau outer inner j omega = n) :
    trajectory omega n ∈ inner := by
  unfold terminalEntranceTime at h
  have hclock : alternatingAnnularClock tau outer inner (2 * j + 1 + 1) omega = n := by
    convert h using 1
  rw [alternatingAnnularClock_succ] at hclock
  have hodd : ¬Even (2 * j + 1) := by
    rintro ⟨q, hq⟩
    omega
  rw [if_neg hodd] at hclock
  exact firstHitSetAfter_mem_of_eq hclock

theorem terminalExitTime_mem_outer_of_eq
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point}
    {j n : ℕ} {omega : StepPath}
    (h : terminalExitTime tau outer inner j omega = n) :
    trajectory omega n ∈ outer := by
  unfold terminalExitTime at h
  have hclock : alternatingAnnularClock tau outer inner (2 * j + 2 + 1) omega = n := by
    convert h using 1
  rw [alternatingAnnularClock_succ] at hclock
  have heven : Even (2 * j + 2) := by
    exact ⟨j + 1, by omega⟩
  rw [if_pos heven] at hclock
  exact firstHitSetAfter_mem_of_eq hclock

/-! ## Exact restart and random-entrance disintegration -/

/-- Position of the canonical walk at a possibly-infinite clock, with the
same harmless time-zero convention as `postWithTopStoppingSteps` on the
infinite-value event. -/
def stoppedPosition (tau : StepPath → WithTop ℕ) (omega : StepPath) : Point :=
  trajectory omega ((tau omega).untopD 0)

theorem stoppedPosition_eq_of_eq
    {tau : StepPath → WithTop ℕ} {omega : StepPath} {n : ℕ}
    (h : tau omega = n) : stoppedPosition tau omega = trajectory omega n := by
  unfold stoppedPosition
  rw [h]
  exact congrArg (trajectory omega) (WithTop.untopD_coe (0 : ℕ) n)

/-- Every fibre of the position observed at a stopping time belongs to the
stopped sigma-algebra in the atomwise form used by the strong Markov API. -/
theorem isMeasurableAtWithTopStopping_stoppedPosition_fiber
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (x : Point) :
    IsMeasurableAtWithTopStopping tau {omega | stoppedPosition tau omega = x} := by
  intro n
  have heq :
      {omega : StepPath | stoppedPosition tau omega = x} ∩
          {omega | tau omega = (n : WithTop ℕ)} =
        {omega | trajectory omega n = x} ∩
          {omega | tau omega = (n : WithTop ℕ)} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpos, htime⟩
      exact ⟨(stoppedPosition_eq_of_eq htime).symm.trans hpos, htime⟩
    · rintro ⟨hpos, htime⟩
      exact ⟨(stoppedPosition_eq_of_eq htime).trans hpos, htime⟩
  rw [heq]
  have hpos : MeasurableSet[incrementFiltration n]
      {omega : StepPath | trajectory omega n = x} := by
    simpa using measurableSet_trajectory_mem_incrementFiltration n ({x} : Set Point)
  exact hpos.inter (htau.measurableSet_eq n)

theorem isMeasurableAtWithTopStopping_inter
    {tau : StepPath → WithTop ℕ} {A B : Set StepPath}
    (hA : IsMeasurableAtWithTopStopping tau A)
    (hB : IsMeasurableAtWithTopStopping tau B) :
    IsMeasurableAtWithTopStopping tau (A ∩ B) := by
  intro n
  have heq : (A ∩ B) ∩ {omega | tau omega = (n : WithTop ℕ)} =
      (A ∩ {omega | tau omega = (n : WithTop ℕ)}) ∩
        (B ∩ {omega | tau omega = (n : WithTop ℕ)}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact (hA n).inter (hB n)

/-- On a finite clock atom, the absolute future path is the stopped position
plus the fresh path generated by the post-clock increments. -/
theorem trajectory_eq_stoppedPosition_add_post
    {tau : StepPath → WithTop ℕ} {omega : StepPath} {n k : ℕ}
    (h : tau omega = n) :
    trajectory omega (n + k) = stoppedPosition tau omega +
      trajectory (postWithTopStoppingSteps tau omega) k := by
  have hpost : postWithTopStoppingSteps tau omega = shiftSteps n omega := by
    funext q
    unfold postWithTopStoppingSteps shiftSteps
    rw [h]
    have hu : WithTop.untopD 0 (n : WithTop ℕ) = n :=
      WithTop.untopD_coe (0 : ℕ) n
    rw [hu]
  rw [stoppedPosition_eq_of_eq h, hpost]
  simpa [add_comm] using
    (sub_eq_iff_eq_add.mp (trajectory_add_sub_trajectory omega n k))

/-- Exact full-tail disintegration over the random position at a possibly
infinite stopping time.  Each `K x` is an arbitrary measurable event of the
fresh post-clock increments for a walk whose absolute starting point is `x`.
This is the rigorous mixture identity supplied by strong Markov before any
annular Harnack comparison. -/
theorem strongMarkov_withTop_stoppedPosition_disintegration
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    (K : Point → Set StepPath) (hK : ∀ x, MeasurableSet (K x)) :
    fairSteps {omega | omega ∈ A ∧ tau omega < ⊤ ∧
        postWithTopStoppingSteps tau omega ∈ K (stoppedPosition tau omega)} =
      ∑' x : Point,
        fairSteps ((A ∩ {omega | stoppedPosition tau omega = x}) ∩
          {omega | tau omega < ⊤}) * fairSteps (K x) := by
  apply strongMarkov_withTop_fullTail_countable_partition_finiteEvent
    htau (stoppedPosition tau)
  · intro x
    exact isMeasurableAtWithTopStopping_inter hA
      (isMeasurableAtWithTopStopping_stoppedPosition_fiber htau x)
  · exact hK

/-- One-sided form of the random-entrance mixture.  Uniform lower and upper
bounds for every fresh entrance kernel survive arbitrary stopped-past
conditioning.  Iterating this statement at successive clocks is the valid
replacement for conditioning on a complete future entrance vector. -/
theorem strongMarkov_withTop_stoppedPosition_bounds
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    (K : Point → Set StepPath) (hK : ∀ x, MeasurableSet (K x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x, fairSteps (K x) ∈ Set.Icc lower upper) :
    fairSteps {omega | omega ∈ A ∧ tau omega < ⊤ ∧
        postWithTopStoppingSteps tau omega ∈ K (stoppedPosition tau omega)} ∈
      Set.Icc
        (fairSteps (A ∩ {omega | tau omega < ⊤}) * lower)
        (fairSteps (A ∩ {omega | tau omega < ⊤}) * upper) := by
  let fiberMass : Point → ℝ≥0∞ := fun x ↦
    fairSteps ((A ∩ {omega | stoppedPosition tau omega = x}) ∩
      {omega | tau omega < ⊤})
  have hlaw := strongMarkov_withTop_stoppedPosition_disintegration
    htau hA K hK
  have hmassLaw := strongMarkov_withTop_stoppedPosition_disintegration
    htau hA (fun _ ↦ (Set.univ : Set StepPath)) (fun _ ↦ MeasurableSet.univ)
  have hleft : {omega : StepPath | omega ∈ A ∧ tau omega < ⊤ ∧
      postWithTopStoppingSteps tau omega ∈ (Set.univ : Set StepPath)} =
      A ∩ {omega | tau omega < ⊤} := by
    ext omega
    simp
  rw [hleft] at hmassLaw
  simp only [measure_univ, mul_one] at hmassLaw
  have hmass : ∑' x, fiberMass x =
      fairSteps (A ∩ {omega | tau omega < ⊤}) := by
    exact hmassLaw.symm
  rw [hlaw]
  constructor
  · calc
      fairSteps (A ∩ {omega | tau omega < ⊤}) * lower =
          (∑' x, fiberMass x) * lower := by rw [hmass]
      _ = ∑' x, fiberMass x * lower := ENNReal.tsum_mul_right.symm
      _ ≤ ∑' x, fiberMass x * fairSteps (K x) :=
        ENNReal.tsum_le_tsum fun x ↦
          mul_le_mul_right (hprob x).1 (fiberMass x)
      _ = _ := rfl
  · calc
      (∑' x, fiberMass x * fairSteps (K x)) ≤
          ∑' x, fiberMass x * upper :=
        ENNReal.tsum_le_tsum fun x ↦
          mul_le_mul_right (hprob x).2 (fiberMass x)
      _ = (∑' x, fiberMass x) * upper := ENNReal.tsum_mul_right
      _ = fairSteps (A ∩ {omega | tau omega < ⊤}) * upper := by rw [hmass]

/-- Localized one-sided form of the random-position mixture.  It is enough
to bound the fresh kernel on a set `valid` containing every stopped position
which has nonzero mass in the stopped history.  This is the form needed at
an annular entrance: the entrance-point Harnack estimate is only stated on
the inner vertex boundary, while the stopping-clock geometry proves that the
current stopped position belongs to that boundary. -/
theorem strongMarkov_withTop_stoppedPosition_bounds_on
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    (valid : Set Point)
    (hsupport : ∀ omega, omega ∈ A → tau omega < ⊤ →
      stoppedPosition tau omega ∈ valid)
    (K : Point → Set StepPath) (hK : ∀ x, MeasurableSet (K x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x ∈ valid, fairSteps (K x) ∈ Set.Icc lower upper) :
    fairSteps {omega | omega ∈ A ∧ tau omega < ⊤ ∧
        postWithTopStoppingSteps tau omega ∈ K (stoppedPosition tau omega)} ∈
      Set.Icc
        (fairSteps (A ∩ {omega | tau omega < ⊤}) * lower)
        (fairSteps (A ∩ {omega | tau omega < ⊤}) * upper) := by
  let fiberMass : Point → ℝ≥0∞ := fun x ↦
    fairSteps ((A ∩ {omega | stoppedPosition tau omega = x}) ∩
      {omega | tau omega < ⊤})
  have hlaw := strongMarkov_withTop_stoppedPosition_disintegration
    htau hA K hK
  have hmassLaw := strongMarkov_withTop_stoppedPosition_disintegration
    htau hA (fun _ ↦ (Set.univ : Set StepPath)) (fun _ ↦ MeasurableSet.univ)
  have hleft : {omega : StepPath | omega ∈ A ∧ tau omega < ⊤ ∧
      postWithTopStoppingSteps tau omega ∈ (Set.univ : Set StepPath)} =
      A ∩ {omega | tau omega < ⊤} := by
    ext omega
    simp
  rw [hleft] at hmassLaw
  simp only [measure_univ, mul_one] at hmassLaw
  have hmass : ∑' x, fiberMass x =
      fairSteps (A ∩ {omega | tau omega < ⊤}) := hmassLaw.symm
  have hfiber_zero {x : Point} (hx : x ∉ valid) : fiberMass x = 0 := by
    have heq : ((A ∩ {omega | stoppedPosition tau omega = x}) ∩
        {omega | tau omega < ⊤} : Set StepPath) = ∅ := by
      ext omega
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨homega, hpos⟩, hfinite⟩
      exact hx (hpos ▸ hsupport omega homega hfinite)
    simp only [fiberMass, heq, measure_empty]
  have hfiber_lower (x : Point) :
      fiberMass x * lower ≤ fiberMass x * fairSteps (K x) := by
    by_cases hx : x ∈ valid
    · exact mul_le_mul_right (hprob x hx).1 (fiberMass x)
    · rw [hfiber_zero hx]
      simp
  have hfiber_upper (x : Point) :
      fiberMass x * fairSteps (K x) ≤ fiberMass x * upper := by
    by_cases hx : x ∈ valid
    · exact mul_le_mul_right (hprob x hx).2 (fiberMass x)
    · rw [hfiber_zero hx]
      simp
  rw [hlaw]
  constructor
  · calc
      fairSteps (A ∩ {omega | tau omega < ⊤}) * lower =
          (∑' x, fiberMass x) * lower := by rw [hmass]
      _ = ∑' x, fiberMass x * lower := ENNReal.tsum_mul_right.symm
      _ ≤ ∑' x, fiberMass x * fairSteps (K x) :=
        ENNReal.tsum_le_tsum hfiber_lower
      _ = _ := rfl
  · calc
      (∑' x, fiberMass x * fairSteps (K x)) ≤
          ∑' x, fiberMass x * upper := ENNReal.tsum_le_tsum hfiber_upper
      _ = (∑' x, fiberMass x) * upper := ENNReal.tsum_mul_right
      _ = fairSteps (A ∩ {omega | tau omega < ⊤}) * upper := by rw [hmass]

/-- The exact mixture identity at the `j`-th inner annular entrance. -/
theorem terminalEntrance_fullTail_disintegration
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (outer inner : Set Point) (j : ℕ)
    (hA : IsMeasurableAtWithTopStopping
      (terminalEntranceTime tau outer inner j) A)
    (K : Point → Set StepPath) (hK : ∀ x, MeasurableSet (K x)) :
    fairSteps {omega | omega ∈ A ∧
        terminalEntranceTime tau outer inner j omega < ⊤ ∧
        postWithTopStoppingSteps (terminalEntranceTime tau outer inner j) omega ∈
          K (stoppedPosition (terminalEntranceTime tau outer inner j) omega)} =
      ∑' x : Point,
        fairSteps ((A ∩ {omega |
            stoppedPosition (terminalEntranceTime tau outer inner j) omega = x}) ∩
          {omega | terminalEntranceTime tau outer inner j omega < ⊤}) *
            fairSteps (K x) := by
  exact strongMarkov_withTop_stoppedPosition_disintegration
    (isStoppingTime_terminalEntranceTime htau outer inner j) hA K hK

/-- A path visits a target set arbitrarily late. -/
def FrequentlyVisitsSet (A : Set Point) (omega : StepPath) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ trajectory omega n ∈ A

theorem frequentlyVisitsSet_of_frequently_atTop
    {A : Set Point} {omega : StepPath}
    (hfreq : ∃ᶠ n in atTop, trajectory omega n ∈ A) :
    FrequentlyVisitsSet A omega := by
  intro N
  obtain ⟨n, hnA, hnN⟩ :=
    (hfreq.and_eventually (eventually_ge_atTop N)).exists
  exact ⟨n, hnN, hnA⟩

/-- Every nonempty lattice set is visited arbitrarily late almost surely. -/
theorem ae_frequentlyVisitsSet_of_nonempty
    {A : Set Point} (hA : A.Nonempty) :
    ∀ᵐ omega ∂fairSteps, FrequentlyVisitsSet A omega := by
  filter_upwards
      [SpatialRecurrence.fairSteps_frequently_visits_nonempty_set hA]
      with omega homega
  exact frequentlyVisitsSet_of_frequently_atTop homega

theorem firstHitSetAfter_lt_top_of_frequently
    {tau : StepPath → WithTop ℕ} {A : Set Point} {omega : StepPath}
    (htau : tau omega < ⊤) (hfreq : FrequentlyVisitsSet A omega) :
    firstHitSetAfter tau A omega < ⊤ := by
  have htne : tau omega ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp htau
  lift tau omega to ℕ using htne with N hN
  obtain ⟨n, hNn, hnA⟩ := hfreq N
  have hle : firstHitSetAfter tau A omega ≤ n :=
    (firstHitSetAfter_le_iff tau A omega n).mpr
      ⟨n, le_rfl, by
        rw [← hN]
        exact WithTop.coe_le_coe.mpr hNn, hnA⟩
  exact hle.trans_lt (WithTop.coe_lt_top n)

/-- On a path which visits both annular boundaries arbitrarily late, every
clock in the alternating ladder is finite. -/
theorem alternatingAnnularClock_lt_top_of_frequently
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point} {omega : StepPath}
    (htau : tau omega < ⊤)
    (houter : FrequentlyVisitsSet outer omega)
    (hinner : FrequentlyVisitsSet inner omega) :
    ∀ j, alternatingAnnularClock tau outer inner j omega < ⊤ := by
  intro j
  induction j with
  | zero => simpa using htau
  | succ j ih =>
      rw [alternatingAnnularClock_succ]
      split_ifs with heven
      · exact firstHitSetAfter_lt_top_of_frequently ih houter
      · exact firstHitSetAfter_lt_top_of_frequently ih hinner

theorem ae_alternatingAnnularClock_lt_top
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point}
    (htau : ∀ᵐ omega ∂fairSteps, tau omega < ⊤)
    (houter : ∀ᵐ omega ∂fairSteps, FrequentlyVisitsSet outer omega)
    (hinner : ∀ᵐ omega ∂fairSteps, FrequentlyVisitsSet inner omega) :
    ∀ j, ∀ᵐ omega ∂fairSteps,
      alternatingAnnularClock tau outer inner j omega < ⊤ := by
  intro j
  filter_upwards [htau, houter, hinner] with omega hτ ho hi
  exact alternatingAnnularClock_lt_top_of_frequently hτ ho hi j

/-- If both annular boundaries are nonempty, spatial recurrence discharges
all recurrence hypotheses: every clock in the alternating ladder is almost
surely finite. -/
theorem ae_alternatingAnnularClock_lt_top_of_nonempty
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point}
    (htau : ∀ᵐ omega ∂fairSteps, tau omega < ⊤)
    (houter : outer.Nonempty) (hinner : inner.Nonempty) :
    ∀ j, ∀ᵐ omega ∂fairSteps,
      alternatingAnnularClock tau outer inner j omega < ⊤ := by
  exact ae_alternatingAnnularClock_lt_top htau
    (ae_frequentlyVisitsSet_of_nonempty houter)
    (ae_frequentlyVisitsSet_of_nonempty hinner)

/-- Simultaneous version: on one full-measure event, every clock in the
alternating ladder is finite. -/
theorem ae_all_alternatingAnnularClock_lt_top_of_nonempty
    {tau : StepPath → WithTop ℕ} {outer inner : Set Point}
    (htau : ∀ᵐ omega ∂fairSteps, tau omega < ⊤)
    (houter : outer.Nonempty) (hinner : inner.Nonempty) :
    ∀ᵐ omega ∂fairSteps, ∀ j,
      alternatingAnnularClock tau outer inner j omega < ⊤ := by
  exact ae_all_iff.2
    (ae_alternatingAnnularClock_lt_top_of_nonempty htau houter hinner)

end

end Erdos1165.TerminalExcursionBridge
