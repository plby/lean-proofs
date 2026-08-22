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

import ErdosProblems.Erdos1165.BoundaryVisitLaw
import ErdosProblems.Erdos1165.TerminalExcursionPathwise

/-!
# Literal sequential terminal-excursion visit atoms

This file connects the unbounded stopping clocks used by strong Markov with
the horizon-truncated excursion bookkeeping used in the definition of a
successful point.  The comparison is made only on complete segments.  It
also identifies each fresh Bernoulli--geometric atom with the literal number
of visits made before the corresponding boundary hit.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Erdos1165.TerminalSequentialVisitLaw

open ThickPoint TerminalExcursionPathwise TerminalExcursionBridge
open BoundaryVisitRegeneration BoundaryVisitLaw SequentialStoppedAtoms
open SequentialAnnularKernel BoundaryStoppedHarnack
open TerminalExcursionDisintegration

noncomputable section

/-! ## Truncated and unbounded first-hit clocks agree on complete hits -/

lemma firstHitThrough_spec_of_le
    (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    (start horizon : ℕ)
    (hcomplete : firstHitThrough s A start horizon ≤ horizon) :
    start ≤ firstHitThrough s A start horizon ∧
      s (firstHitThrough s A start horizon) ∈ A ∧
      ∀ q < firstHitThrough s A start horizon,
        start ≤ q → s q ∉ A := by
  have hnonempty :=
    (firstHitThrough_le_horizon_iff s A start horizon).mp hcomplete
  have hmem := firstHitThrough_mem_of_nonempty s A start horizon hnonempty
  have hinterval := Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1
  refine ⟨hinterval.1, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro q hq hstartq hqA
  have hqhorizon : q ≤ horizon := hq.le.trans hcomplete
  have hqmem : q ∈ hitTimesThrough s A start horizon :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hstartq, hqhorizon⟩, hqA⟩
  have hmin := Finset.min'_le _ _ hqmem
  have hhit : firstHitThrough s A start horizon =
      (hitTimesThrough s A start horizon).min' hnonempty := by
    simp only [firstHitThrough, dif_pos hnonempty]
  exact (Nat.not_le_of_gt hq) (by simpa only [hhit] using hmin)

lemma firstHitSetAfter_eq_firstHitThrough
    {tau : StepPath → WithTop ℕ} {omega : StepPath}
    (A : Set Point) [DecidablePred (· ∈ A)]
    {start horizon : ℕ} (htau : tau omega = start)
    (hcomplete : firstHitThrough (trajectory omega) A start horizon ≤ horizon) :
    firstHitSetAfter tau A omega =
      firstHitThrough (trajectory omega) A start horizon := by
  let hit := firstHitThrough (trajectory omega) A start horizon
  have hspec := firstHitThrough_spec_of_le
    (trajectory omega) A start horizon hcomplete
  apply (firstHitSetAfter_eq_coe_iff tau A omega hit).2
  refine ⟨?_, hspec.2.1, ?_⟩
  · rw [htau]
    exact_mod_cast hspec.1
  · intro q hq hcandidate
    have hstartq : start ≤ q := by
      rw [htau] at hcandidate
      exact WithTop.coe_le_coe.mp hcandidate.1
    exact hspec.2.2 q hq hstartq hcandidate.2

/-! ## Alternating clocks coincide with the finite excursion ladder -/

lemma excursionStart_succ_eq_firstHitThrough_finish
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) :
    excursionStart s outer inner horizon (j + 1) =
      firstHitThrough s outer (excursionFinish s outer inner horizon j) horizon := by
  unfold excursionStart
  rw [excursionFinish_eq_iterate_succ]

lemma alternatingAnnularClock_eq_excursionStart_finish
    (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) :
    ∀ j,
      excursionStart (trajectory omega) outer inner horizon (j + 1) ≤ horizon →
      alternatingAnnularClock zeroClock outer inner (2 * j + 1) omega =
          excursionStart (trajectory omega) outer inner horizon j ∧
        alternatingAnnularClock zeroClock outer inner (2 * j + 2) omega =
          excursionFinish (trajectory omega) outer inner horizon j := by
  intro j
  induction j with
  | zero =>
      intro hnext
      have hfinish : excursionFinish (trajectory omega) outer inner horizon 0 ≤
          horizon :=
        (excursionFinish_le_next_start (trajectory omega) outer inner horizon 0).trans
          hnext
      have hstart : excursionStart (trajectory omega) outer inner horizon 0 ≤
          horizon :=
        (excursionStart_le_finish (trajectory omega) outer inner horizon 0).trans
          hfinish
      have hclockOne :
          alternatingAnnularClock zeroClock outer inner 1 omega =
            excursionStart (trajectory omega) outer inner horizon 0 := by
        rw [alternatingAnnularClock_succ]
        have heven : Even 0 := ⟨0, rfl⟩
        rw [if_pos heven]
        simp only [alternatingAnnularClock_zero]
        apply firstHitSetAfter_eq_firstHitThrough outer rfl
        simpa [excursionStart] using hstart
      refine ⟨by simpa using hclockOne, ?_⟩
      have hclockTwo :
          alternatingAnnularClock zeroClock outer inner 2 omega =
            excursionFinish (trajectory omega) outer inner horizon 0 := by
        rw [show 2 = 1 + 1 by omega, alternatingAnnularClock_succ]
        have hodd : ¬ Even 1 := by
          rintro ⟨k, hk⟩
          omega
        rw [if_neg hodd]
        apply firstHitSetAfter_eq_firstHitThrough inner hclockOne
        exact hfinish
      simpa using hclockTwo
  | succ j ih =>
      intro hnext
      have hfinish :
          excursionFinish (trajectory omega) outer inner horizon (j + 1) ≤ horizon :=
        (excursionFinish_le_next_start (trajectory omega) outer inner horizon (j + 1)).trans
          hnext
      have hstart :
          excursionStart (trajectory omega) outer inner horizon (j + 1) ≤ horizon :=
        (excursionStart_le_finish (trajectory omega) outer inner horizon (j + 1)).trans
          hfinish
      have hprevNext :
          excursionStart (trajectory omega) outer inner horizon (j + 1) ≤ horizon :=
        hstart
      obtain ⟨_hprevStart, hprevFinish⟩ := ih hprevNext
      have hclockStart :
          alternatingAnnularClock zeroClock outer inner (2 * (j + 1) + 1) omega =
            excursionStart (trajectory omega) outer inner horizon (j + 1) := by
        rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by omega,
          alternatingAnnularClock_succ]
        have heven : Even (2 * j + 2) := ⟨j + 1, by omega⟩
        rw [if_pos heven]
        have houterComplete :
            firstHitThrough (trajectory omega) outer
                (excursionFinish (trajectory omega) outer inner horizon j) horizon ≤
              horizon := by
          rw [← excursionStart_succ_eq_firstHitThrough_finish
            (trajectory omega) outer inner horizon j]
          exact hstart
        have hfirst :
            firstHitSetAfter
                (alternatingAnnularClock zeroClock outer inner (2 * j + 2))
                outer omega =
              firstHitThrough (trajectory omega) outer
                (excursionFinish (trajectory omega) outer inner horizon j) horizon :=
          firstHitSetAfter_eq_firstHitThrough outer hprevFinish houterComplete
        rw [← excursionStart_succ_eq_firstHitThrough_finish
          (trajectory omega) outer inner horizon j] at hfirst
        exact hfirst
      refine ⟨hclockStart, ?_⟩
      rw [show 2 * (j + 1) + 2 = (2 * (j + 1) + 1) + 1 by omega,
        alternatingAnnularClock_succ]
      have hodd : ¬ Even (2 * (j + 1) + 1) := by
        rintro ⟨k, hk⟩
        omega
      rw [if_neg hodd]
      exact firstHitSetAfter_eq_firstHitThrough inner hclockStart hfinish

lemma terminalEntranceTime_eq_excursionFinish
    (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ)
    (hcomplete : excursionStart (trajectory omega) outer inner horizon (j + 1) ≤
      horizon) :
    terminalEntranceTime zeroClock outer inner j omega =
      excursionFinish (trajectory omega) outer inner horizon j := by
  exact (alternatingAnnularClock_eq_excursionStart_finish
    omega outer inner horizon j hcomplete).2

lemma terminalExitTime_eq_excursionStart
    (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ)
    (hcomplete : excursionStart (trajectory omega) outer inner horizon (j + 1) ≤
      horizon) :
    terminalExitTime zeroClock outer inner j omega =
      excursionStart (trajectory omega) outer inner horizon (j + 1) := by
  unfold terminalExitTime
  rw [show 2 * j + 3 = (2 * j + 2) + 1 by omega,
    alternatingAnnularClock_succ]
  have heven : Even (2 * j + 2) := ⟨j + 1, by omega⟩
  rw [if_pos heven]
  have hentrance := terminalEntranceTime_eq_excursionFinish
    omega outer inner horizon j hcomplete
  unfold terminalEntranceTime at hentrance
  have houterComplete :
      firstHitThrough (trajectory omega) outer
          (excursionFinish (trajectory omega) outer inner horizon j) horizon ≤
        horizon := by
    rw [← excursionStart_succ_eq_firstHitThrough_finish
      (trajectory omega) outer inner horizon j]
    exact hcomplete
  have hfirst :
      firstHitSetAfter
          (alternatingAnnularClock zeroClock outer inner (2 * j + 2))
          outer omega =
        firstHitThrough (trajectory omega) outer
          (excursionFinish (trajectory omega) outer inner horizon j) horizon :=
    firstHitSetAfter_eq_firstHitThrough outer hentrance houterComplete
  rw [← excursionStart_succ_eq_firstHitThrough_finish
    (trajectory omega) outer inner horizon j] at hfirst
  exact hfirst

/-! ## Positive regeneration atoms count literal visits -/

/-- A concrete time is the first visit to the relative killing boundary. -/
def BoundaryFirstAt (boundary : Set Point) (omega : StepPath) (N : ℕ) : Prop :=
  trajectory omega N ∈ boundary ∧
    ∀ q < N, trajectory omega q ∉ boundary

/-- Number of visits to the relative target `0` strictly before time `N`.
The sum form is convenient for splitting at a return time. -/
def zeroVisitSum (omega : StepPath) (N : ℕ) : ℕ :=
  ∑ q ∈ Finset.range N, if trajectory omega q = 0 then 1 else 0

lemma zeroVisitSum_eq_card (omega : StepPath) (N : ℕ) :
    zeroVisitSum omega N =
      ((Finset.range N).filter fun q ↦ trajectory omega q = 0).card := by
  simp only [zeroVisitSum, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma firstPositiveReturnTime_spec
    {omega : StepPath} {r : ℕ}
    (hr : firstPositiveReturnTime omega = r) :
    1 ≤ r ∧ trajectory omega r = 0 ∧
      ∀ q < r, 1 ≤ q → trajectory omega q ≠ 0 := by
  have hspec := (firstHitSetAfter_eq_coe_iff
    (stoppingTimeSucc zeroClock) ({0} : Set Point) omega r).mp hr
  refine ⟨?_, by simpa using hspec.2.1, ?_⟩
  · simpa [stoppingTimeSucc, zeroClock] using hspec.1
  · intro q hqr hq1 hqzero
    exact hspec.2.2 q hqr ⟨by simpa [stoppingTimeSucc, zeroClock] using hq1,
      by simpa using hqzero⟩

lemma zeroVisitSum_split_firstPositiveReturn
    {omega : StepPath} {r M : ℕ}
    (hr : firstPositiveReturnTime omega = r) :
    zeroVisitSum omega (r + M) =
      1 + zeroVisitSum (shiftSteps r omega) M := by
  have hrspec := firstPositiveReturnTime_spec hr
  unfold zeroVisitSum
  rw [Finset.sum_range_add]
  have hfirst :
      ∑ q ∈ Finset.range r, (if trajectory omega q = 0 then 1 else 0) = 1 := by
    calc
      ∑ q ∈ Finset.range r,
          (if trajectory omega q = 0 then 1 else 0) =
          ∑ q ∈ Finset.range r, (if q = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hq0 : q = 0
        · subst q
          simp [trajectory]
        · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
          have hqne : trajectory omega q ≠ 0 :=
            hrspec.2.2 q (Finset.mem_range.mp hq) hq1
          simp [hq0, hqne]
      _ = 1 := by
        rw [Finset.sum_ite_eq' (Finset.range r) 0 (fun _ ↦ (1 : ℕ))]
        have hr0 : r ≠ 0 := Nat.ne_of_gt hrspec.1
        simp [hr0]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  have hshift := trajectory_add_sub_trajectory omega r q
  rw [hrspec.2.1] at hshift
  have heq : trajectory omega (r + q) = trajectory (shiftSteps r omega) q := by
    simpa using hshift
  rw [heq]

lemma zeroVisitSum_pos_of_boundaryFirstAt
    {boundary : Set Point} (hzero : (0 : Point) ∉ boundary)
    {omega : StepPath} {N : ℕ} (hfirst : BoundaryFirstAt boundary omega N) :
    0 < zeroVisitSum omega N := by
  have hN : 0 < N := by
    by_contra hnot
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    exact hzero (by simpa [trajectory] using hfirst.1)
  unfold zeroVisitSum
  have hzeroMem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have hterm : (if trajectory omega 0 = 0 then 1 else 0) = 1 := by
    simp [trajectory]
  calc
    0 < (if trajectory omega 0 = 0 then 1 else 0) := by simp [trajectory]
    _ ≤ ∑ q ∈ Finset.range N,
        (if trajectory omega q = 0 then 1 else 0) :=
      Finset.single_le_sum
        (s := Finset.range N)
        (f := fun q ↦ if trajectory omega q = 0 then 1 else 0)
        (fun q _ ↦ Nat.zero_le _) hzeroMem

lemma positiveReturnBeforeBoundary_iff_exists_return_lt
    {boundary : Set Point} (hzero : (0 : Point) ∉ boundary)
    {omega : StepPath} {N : ℕ} (hfirst : BoundaryFirstAt boundary omega N) :
    omega ∈ positiveReturnBeforeBoundary boundary ↔
      ∃ r < N, firstPositiveReturnTime omega = r := by
  constructor
  · intro hreturn
    obtain ⟨r, hr, havoid⟩ := Set.mem_iUnion.mp hreturn
    refine ⟨r, ?_, hr⟩
    by_contra hnot
    have hNr : N ≤ r := Nat.le_of_not_gt hnot
    rcases hNr.eq_or_lt with hEq | hLt
    · subst r
      have hrzero := (firstPositiveReturnTime_spec hr).2.1
      exact hzero (hrzero ▸ hfirst.1)
    · exact havoid N hLt hfirst.1
  · rintro ⟨r, hrN, hr⟩
    refine Set.mem_iUnion.mpr ⟨r, hr, ?_⟩
    intro q hqr
    exact hfirst.2 q (hqr.trans hrN)

lemma boundaryFirstAt_shift_firstPositiveReturn
    {boundary : Set Point} {omega : StepPath} {N r : ℕ}
    (hfirst : BoundaryFirstAt boundary omega N)
    (hrN : r < N) (hr : firstPositiveReturnTime omega = r) :
    BoundaryFirstAt boundary (shiftSteps r omega) (N - r) := by
  have hrzero := (firstPositiveReturnTime_spec hr).2.1
  have hadd : r + (N - r) = N := Nat.add_sub_of_le hrN.le
  constructor
  · have hshift := trajectory_add_sub_trajectory omega r (N - r)
    rw [hadd, hrzero, sub_zero] at hshift
    rw [← hshift]
    exact hfirst.1
  · intro q hq
    have hrqN : r + q < N := by omega
    have hshift := trajectory_add_sub_trajectory omega r q
    rw [hrzero, sub_zero] at hshift
    rw [← hshift]
    exact hfirst.2 (r + q) hrqN

lemma zeroVisitSum_eq_one_of_no_positiveReturnBeforeBoundary
    {boundary : Set Point} (hzero : (0 : Point) ∉ boundary)
    {omega : StepPath} {N : ℕ} (hfirst : BoundaryFirstAt boundary omega N)
    (hreturn : omega ∉ positiveReturnBeforeBoundary boundary) :
    zeroVisitSum omega N = 1 := by
  have hN : 0 < N := by
    exact Nat.pos_of_ne_zero fun hN0 ↦
      hzero (by simpa [hN0, trajectory] using hfirst.1)
  unfold zeroVisitSum
  calc
    ∑ q ∈ Finset.range N,
        (if trajectory omega q = 0 then 1 else 0) =
        ∑ q ∈ Finset.range N, (if q = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        simp [trajectory]
      · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        by_cases hqzero : trajectory omega q = 0
        · have hle : firstPositiveReturnTime omega ≤ q :=
            (firstHitSetAfter_le_iff (stoppingTimeSucc zeroClock) ({0} : Set Point)
              omega q).2 ⟨q, le_rfl,
                by simpa [stoppingTimeSucc, zeroClock] using hq1,
                by simpa using hqzero⟩
          have hfinite : firstPositiveReturnTime omega ≠ ⊤ :=
            WithTop.lt_top_iff_ne_top.mp
              (hle.trans_lt (WithTop.coe_lt_top q))
          lift firstPositiveReturnTime omega to ℕ using hfinite with r hr
          have hrq : r ≤ q := by exact WithTop.coe_le_coe.mp hle
          have hrN : r < N := hrq.trans_lt (Finset.mem_range.mp hq)
          exact (hreturn ((positiveReturnBeforeBoundary_iff_exists_return_lt
            hzero hfirst).2 ⟨r, hrN, hr.symm⟩)).elim
        · simp [hq0, hqzero]
    _ = 1 := by
      rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ ↦ (1 : ℕ))]
      simp [hN]

lemma postWithTopStoppingSteps_eq_shiftSteps_of_eq
    {tau : StepPath → WithTop ℕ} {omega : StepPath} {n : ℕ}
    (h : tau omega = n) :
    postWithTopStoppingSteps tau omega = shiftSteps n omega := by
  funext q
  unfold postWithTopStoppingSteps shiftSteps
  rw [h]
  have hu : WithTop.untopD 0 (n : WithTop ℕ) = n :=
    WithTop.untopD_coe (0 : ℕ) n
  rw [hu]

/-- On a path whose first boundary hit is finite, the recursive regeneration
atom is exactly the literal number of visits to the target before that hit. -/
theorem mem_positiveVisitAtom_iff_zeroVisitSum
    (boundary : Set Point) (hzero : (0 : Point) ∉ boundary) :
    ∀ N omega k, BoundaryFirstAt boundary omega N →
      (omega ∈ positiveVisitAtom boundary k ↔ zeroVisitSum omega N = k) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro omega k hfirst
      by_cases hreturn : omega ∈ positiveReturnBeforeBoundary boundary
      · obtain ⟨r, hrN, hr⟩ :=
          (positiveReturnBeforeBoundary_iff_exists_return_lt hzero hfirst).1 hreturn
        have hrspec := firstPositiveReturnTime_spec hr
        have hshiftFirst := boundaryFirstAt_shift_firstPositiveReturn hfirst hrN hr
        have hrpos : 0 < r := hrspec.1
        have hsubLt : N - r < N := Nat.sub_lt (Nat.zero_lt_of_lt hrN) hrpos
        have hNadd : r + (N - r) = N := Nat.add_sub_of_le hrN.le
        have hsplit : zeroVisitSum omega N =
            1 + zeroVisitSum (shiftSteps r omega) (N - r) := by
          calc
            zeroVisitSum omega N = zeroVisitSum omega (r + (N - r)) := by
              rw [hNadd]
            _ = 1 + zeroVisitSum (shiftSteps r omega) (N - r) :=
              zeroVisitSum_split_firstPositiveReturn hr
        have hpost : postWithTopStoppingSteps firstPositiveReturnTime omega =
            shiftSteps r omega :=
          postWithTopStoppingSteps_eq_shiftSteps_of_eq hr
        have hshiftPos : 0 < zeroVisitSum (shiftSteps r omega) (N - r) :=
          zeroVisitSum_pos_of_boundaryFirstAt hzero hshiftFirst
        cases k with
        | zero =>
            constructor
            · intro hempty
              exact hempty.elim
            · intro hcountZero
              omega
        | succ k =>
            cases k with
            | zero =>
                constructor
                · intro hnotReturn
                  exact (hnotReturn hreturn).elim
                · intro hcountOne
                  omega
            | succ k =>
                rw [positiveVisitAtom_succ_succ]
                simp only [Set.mem_inter_iff, Set.mem_preimage, hreturn,
                  true_and, hpost]
                rw [ih (N - r) hsubLt (shiftSteps r omega) (k + 1)
                  hshiftFirst]
                omega
      · have hcount :=
          zeroVisitSum_eq_one_of_no_positiveReturnBeforeBoundary
            hzero hfirst hreturn
        cases k with
        | zero =>
            constructor
            · intro hempty
              exact hempty.elim
            · intro hcountZero
              omega
        | succ k =>
            cases k with
            | zero =>
                constructor
                · intro _hmember
                  exact hcount
                · intro _hcount
                  exact hreturn
            | succ k =>
                constructor
                · intro hmember
                  exact (hreturn hmember.1).elim
                · intro hcountSucc
                  omega

/-! ## Adding the first-hit Bernoulli factor -/

/-- The absolute walk started at `start` first reaches `boundary` at `N`. -/
def AbsoluteBoundaryFirstAt
    (boundary : Set Point) (start : Point) (omega : StepPath) (N : ℕ) : Prop :=
  PlanarPotential.trajectoryFrom start omega N ∈ boundary ∧
    ∀ q < N, PlanarPotential.trajectoryFrom start omega q ∉ boundary

/-- Literal number of visits to `target` before the boundary hit. -/
def targetVisitSum
    (start target : Point) (omega : StepPath) (N : ℕ) : ℕ :=
  ∑ q ∈ Finset.range N,
    if PlanarPotential.trajectoryFrom start omega q = target then 1 else 0

lemma targetVisitSum_eq_card
    (start target : Point) (omega : StepPath) (N : ℕ) :
    targetVisitSum start target omega N =
      ((Finset.range N).filter fun q ↦
        PlanarPotential.trajectoryFrom start omega q = target).card := by
  simp only [targetVisitSum, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma targetHitTime_lt_boundary_of_hit
    {boundary : Set Point} {start target : Point}
    (htarget : target ∉ boundary) {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N)
    (hhit : omega ∈ boundaryHitSteps boundary target start) :
    targetHitTime start target omega < N := by
  change PlanarPotential.trajectoryFrom start omega ∈
    walkHitBeforeBoundary boundary target at hhit
  rw [BoundaryStoppedHarnack.mem_walkHitBeforeBoundary_iff_exists] at hhit
  obtain ⟨m, hmTarget, hmAvoid⟩ := hhit
  have hmN : m < N := by
    by_contra hnot
    have hNm : N ≤ m := Nat.le_of_not_gt hnot
    rcases hNm.eq_or_lt with hEq | hLt
    · subst m
      exact htarget (hmTarget ▸ hfirst.1)
    · exact hmAvoid N hLt hfirst.1
  have hmRelative : trajectory omega m = target - start := by
    unfold PlanarPotential.trajectoryFrom at hmTarget
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hmTarget)
  have hle : targetHitTime start target omega ≤ m :=
    (firstHitSetAfter_le_iff zeroClock ({target - start} : Set Point)
      omega m).2 ⟨m, le_rfl, by simp [zeroClock], by simpa using hmRelative⟩
  exact hle.trans_lt (WithTop.coe_lt_coe.mpr hmN)

lemma targetVisitSum_eq_zero_of_not_boundaryHitSteps
    {boundary : Set Point} {start target : Point}
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N)
    (hhit : omega ∉ boundaryHitSteps boundary target start) :
    targetVisitSum start target omega N = 0 := by
  unfold targetVisitSum
  apply Finset.sum_eq_zero
  intro q hq
  have hqN := Finset.mem_range.mp hq
  have hqne : PlanarPotential.trajectoryFrom start omega q ≠ target := by
    intro hqTarget
    apply hhit
    change PlanarPotential.trajectoryFrom start omega ∈
      walkHitBeforeBoundary boundary target
    rw [BoundaryStoppedHarnack.mem_walkHitBeforeBoundary_iff_exists]
    exact ⟨q, hqTarget, fun t ht ↦ hfirst.2 t (ht.trans hqN)⟩
  simp [hqne]

lemma targetVisitSum_split_targetHit
    {start target : Point} {omega : StepPath} {N t : ℕ}
    (ht : targetHitTime start target omega = t) (htN : t < N) :
    targetVisitSum start target omega N =
      zeroVisitSum (shiftSteps t omega) (N - t) := by
  have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
    ({target - start} : Set Point) omega t).mp ht
  have htTarget := targetHitTime_eq_implies_trajectoryFrom ht
  have hNadd : t + (N - t) = N := Nat.add_sub_of_le htN.le
  unfold targetVisitSum zeroVisitSum
  calc
    ∑ q ∈ Finset.range N,
        (if PlanarPotential.trajectoryFrom start omega q = target then 1 else 0) =
        ∑ q ∈ Finset.range (t + (N - t)),
          (if PlanarPotential.trajectoryFrom start omega q = target then 1 else 0) := by
      rw [hNadd]
    _ = (∑ q ∈ Finset.range t,
          (if PlanarPotential.trajectoryFrom start omega q = target then 1 else 0)) +
        ∑ q ∈ Finset.range (N - t),
          (if PlanarPotential.trajectoryFrom start omega (t + q) = target
            then 1 else 0) := by
      rw [Finset.sum_range_add]
    _ = 0 + ∑ q ∈ Finset.range (N - t),
          (if PlanarPotential.trajectoryFrom start omega (t + q) = target
            then 1 else 0) := by
      congr 1
      apply Finset.sum_eq_zero
      intro q hq
      have hqne : PlanarPotential.trajectoryFrom start omega q ≠ target := by
        intro hqTarget
        have hrelative : trajectory omega q = target - start := by
          unfold PlanarPotential.trajectoryFrom at hqTarget
          exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hqTarget)
        exact hspec.2.2 q (Finset.mem_range.mp hq)
          ⟨by simp [zeroClock], by simpa using hrelative⟩
      simp [hqne]
    _ = ∑ q ∈ Finset.range (N - t),
          (if trajectory (shiftSteps t omega) q = 0 then 1 else 0) := by
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro q _hq
      have hshift := trajectory_add_sub_trajectory omega t q
      have htDisplacement : trajectory omega t = target - start := by
        unfold PlanarPotential.trajectoryFrom at htTarget
        exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using htTarget)
      have heq : PlanarPotential.trajectoryFrom start omega (t + q) = target ↔
          trajectory (shiftSteps t omega) q = 0 := by
        unfold PlanarPotential.trajectoryFrom
        rw [← hshift, htDisplacement]
        constructor <;> intro h
        · apply sub_eq_zero.mpr
          exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)
        · have hzeroEq := sub_eq_zero.mp h
          rw [hzeroEq]
          abel
      simp only [heq]
    _ = _ := rfl

lemma relativeBoundaryFirstAt_after_targetHit
    {boundary : Set Point} {start target : Point}
    {omega : StepPath} {N t : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N)
    (ht : targetHitTime start target omega = t) (htN : t < N) :
    BoundaryFirstAt (relativeBoundary boundary target)
      (shiftSteps t omega) (N - t) := by
  have htTarget := targetHitTime_eq_implies_trajectoryFrom ht
  have htDisplacement : trajectory omega t = target - start := by
    unfold PlanarPotential.trajectoryFrom at htTarget
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using htTarget)
  have hNadd : t + (N - t) = N := Nat.add_sub_of_le htN.le
  constructor
  · change target + trajectory (shiftSteps t omega) (N - t) ∈ boundary
    rw [← trajectory_add_sub_trajectory, hNadd, htDisplacement]
    unfold AbsoluteBoundaryFirstAt at hfirst
    unfold PlanarPotential.trajectoryFrom at hfirst
    have heq : target + (trajectory omega N - (target - start)) =
        start + trajectory omega N := by abel
    rw [heq]
    exact hfirst.1
  · intro q hq
    change target + trajectory (shiftSteps t omega) q ∉ boundary
    rw [← trajectory_add_sub_trajectory, htDisplacement]
    have htqN : t + q < N := by omega
    unfold AbsoluteBoundaryFirstAt at hfirst
    unfold PlanarPotential.trajectoryFrom at hfirst
    have heq : target + (trajectory omega (t + q) - (target - start)) =
        start + trajectory omega (t + q) := by abel
    rw [heq]
    exact hfirst.2 (t + q) htqN

/-- The Bernoulli--geometric atom from `BoundaryVisitLaw` is pathwise equal
to the literal number of target visits before the first boundary hit. -/
theorem mem_boundaryVisitAtom_iff_targetVisitSum
    {boundary : Set Point} {start target : Point}
    (htarget : target ∉ boundary) {omega : StepPath} {N k : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N) :
    omega ∈ boundaryVisitAtom boundary target start k ↔
      targetVisitSum start target omega N = k := by
  by_cases hhit : omega ∈ boundaryHitSteps boundary target start
  · have hfinite : targetHitTime start target omega ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp
        (boundaryHitSteps_subset_targetHitTime_finite boundary target start hhit)
    lift targetHitTime start target omega to ℕ using hfinite with t ht
    have ht' : targetHitTime start target omega = t := ht.symm
    have htNTop := targetHitTime_lt_boundary_of_hit htarget hfirst hhit
    rw [ht'] at htNTop
    have htN : t < N := WithTop.coe_lt_coe.mp htNTop
    have hrelative := relativeBoundaryFirstAt_after_targetHit hfirst ht' htN
    have hzeroRelative : (0 : Point) ∉ relativeBoundary boundary target := by
      simpa [relativeBoundary] using htarget
    have hsplit := targetVisitSum_split_targetHit ht' htN
    have hpost : postWithTopStoppingSteps (targetHitTime start target) omega =
        shiftSteps t omega := postWithTopStoppingSteps_eq_shiftSteps_of_eq ht'
    cases k with
    | zero =>
        have hpositive : 0 < zeroVisitSum (shiftSteps t omega) (N - t) :=
          zeroVisitSum_pos_of_boundaryFirstAt hzeroRelative hrelative
        constructor
        · intro hnotHit
          exact (hnotHit hhit).elim
        · intro hcountZero
          rw [hsplit] at hcountZero
          omega
    | succ k =>
        change (omega ∈ boundaryHitSteps boundary target start ∧
          postWithTopStoppingSteps (targetHitTime start target) omega ∈
            positiveVisitAtom (relativeBoundary boundary target) (k + 1)) ↔ _
        simp only [hhit, true_and, hpost]
        rw [mem_positiveVisitAtom_iff_zeroVisitSum
          (relativeBoundary boundary target) hzeroRelative (N - t)
          (shiftSteps t omega) (k + 1) hrelative]
        omega
  · have hcount := targetVisitSum_eq_zero_of_not_boundaryHitSteps hfirst hhit
    cases k with
    | zero =>
        change (omega ∉ boundaryHitSteps boundary target start) ↔ _
        simp [hhit, hcount]
    | succ k =>
        change (omega ∈ boundaryHitSteps boundary target start ∧
          postWithTopStoppingSteps (targetHitTime start target) omega ∈
            positiveVisitAtom (relativeBoundary boundary target) (k + 1)) ↔ _
        constructor
        · intro hmember
          exact (hhit hmember.1).elim
        · intro hcountSucc
          omega

/-! ## A complete stopped segment is a fresh boundary-stopped path -/

lemma trajectoryFrom_shiftSteps_eq
    (omega : StepPath) (t q : ℕ) :
    PlanarPotential.trajectoryFrom (trajectory omega t) (shiftSteps t omega) q =
      trajectory omega (t + q) := by
  unfold PlanarPotential.trajectoryFrom
  have hshift := trajectory_add_sub_trajectory omega t q
  rw [← hshift]
  abel

lemma absoluteBoundaryFirstAt_post_firstHitSetAfter
    {tau : StepPath → WithTop ℕ} {boundary : Set Point}
    {omega : StepPath} {t u : ℕ}
    (ht : tau omega = t) (hu : firstHitSetAfter tau boundary omega = u) :
    AbsoluteBoundaryFirstAt boundary (stoppedPosition tau omega)
      (postWithTopStoppingSteps tau omega) (u - t) := by
  have hspec := (firstHitSetAfter_eq_coe_iff tau boundary omega u).mp hu
  have htu : t ≤ u := by
    rw [ht] at hspec
    exact WithTop.coe_le_coe.mp hspec.1
  have hadd : t + (u - t) = u := Nat.add_sub_of_le htu
  have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq ht
  have hpos := stoppedPosition_eq_of_eq ht
  unfold AbsoluteBoundaryFirstAt
  constructor
  · rw [hpost, hpos, trajectoryFrom_shiftSteps_eq, hadd]
    exact hspec.2.1
  · intro q hq
    rw [hpost, hpos, trajectoryFrom_shiftSteps_eq]
    have htq : t ≤ t + q := Nat.le_add_right t q
    have htqu : t + q < u := by omega
    exact fun hmem ↦ hspec.2.2 (t + q) htqu
      ⟨by rw [ht]; exact_mod_cast htq, hmem⟩

lemma targetVisitSum_shift_eq_Ico_card
    (omega : StepPath) (target : Point) {t u : ℕ} (htu : t ≤ u) :
    targetVisitSum (trajectory omega t) target (shiftSteps t omega) (u - t) =
      ((Finset.Ico t u).filter fun q ↦ trajectory omega q = target).card := by
  rw [targetVisitSum_eq_card]
  let e : ℕ ↪ ℕ := ⟨fun q ↦ t + q, fun _ _ h ↦ Nat.add_left_cancel h⟩
  have heq :
      (((Finset.range (u - t)).filter fun q ↦
          PlanarPotential.trajectoryFrom (trajectory omega t)
            (shiftSteps t omega) q = target).map e) =
        (Finset.Ico t u).filter fun q ↦ trajectory omega q = target := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · rintro ⟨q, ⟨hq, hqTarget⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change t ≤ t + q
        exact Nat.le_add_right t q
      · change t + q < u
        omega
      · change trajectory omega (t + q) = target
        rw [← trajectoryFrom_shiftSteps_eq]
        exact hqTarget
    · rintro ⟨⟨hty, hyu⟩, hyTarget⟩
      refine ⟨y - t, ⟨?_, ?_⟩, ?_⟩
      · omega
      · rw [trajectoryFrom_shiftSteps_eq]
        rwa [Nat.add_sub_of_le hty]
      · change t + (y - t) = y
        exact Nat.add_sub_of_le hty
  have hcard := congrArg Finset.card heq
  simpa [e] using hcard

lemma terminalExitTime_eq_firstHitSetAfter
    (outer inner : Set Point) (j : ℕ) :
    terminalExitTime zeroClock outer inner j =
      firstHitSetAfter (terminalEntranceTime zeroClock outer inner j) outer := by
  funext omega
  unfold terminalExitTime terminalEntranceTime
  rw [show 2 * j + 3 = (2 * j + 2) + 1 by omega,
    alternatingAnnularClock_succ]
  have heven : Even (2 * j + 2) := ⟨j + 1, by omega⟩
  rw [if_pos heven]

/-- On a complete finite excursion segment, membership in the fresh
Bernoulli--geometric atom is equivalent to the literal `innerVisitCount`. -/
theorem terminalSegment_mem_boundaryVisitAtom_iff
    (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (target : Point) (htarget : target ∉ outer)
    (horizon j k : ℕ)
    (hcomplete : excursionStart (trajectory omega) outer inner horizon (j + 1) ≤
      horizon) :
    postWithTopStoppingSteps (terminalEntranceTime zeroClock outer inner j) omega ∈
        boundaryVisitAtom outer target
          (stoppedPosition (terminalEntranceTime zeroClock outer inner j) omega) k ↔
      innerVisitCount (trajectory omega) outer inner horizon target j = k := by
  let t := excursionFinish (trajectory omega) outer inner horizon j
  let u := excursionStart (trajectory omega) outer inner horizon (j + 1)
  have ht : terminalEntranceTime zeroClock outer inner j omega = t :=
    terminalEntranceTime_eq_excursionFinish omega outer inner horizon j hcomplete
  have hu : terminalExitTime zeroClock outer inner j omega = u :=
    terminalExitTime_eq_excursionStart omega outer inner horizon j hcomplete
  have htu : t ≤ u :=
    excursionFinish_le_next_start (trajectory omega) outer inner horizon j
  have hfirstEq : firstHitSetAfter
      (terminalEntranceTime zeroClock outer inner j) outer omega = u := by
    rw [← terminalExitTime_eq_firstHitSetAfter outer inner j]
    exact hu
  have hboundary := absoluteBoundaryFirstAt_post_firstHitSetAfter ht hfirstEq
  have hatom := mem_boundaryVisitAtom_iff_targetVisitSum
    (k := k) htarget hboundary
  have hpost : postWithTopStoppingSteps
      (terminalEntranceTime zeroClock outer inner j) omega = shiftSteps t omega :=
    postWithTopStoppingSteps_eq_shiftSteps_of_eq ht
  have hpos : stoppedPosition (terminalEntranceTime zeroClock outer inner j) omega =
      trajectory omega t := stoppedPosition_eq_of_eq ht
  rw [hpost, hpos] at hatom
  rw [targetVisitSum_shift_eq_Ico_card omega target htu] at hatom
  have hinner : innerVisitCount (trajectory omega) outer inner horizon target j =
      ((Finset.Ico t u).filter fun q ↦ trajectory omega q = target).card := by
    rfl
  rw [hpost, hpos, hinner]
  exact hatom

/-! ## Fixed literal visit-vector atoms -/

/-- Sequential atom specifying the visit count of each of the first `m`
complete `inner → outer` segments. -/
def visitVectorAtom
    (initial : Set StepPath) (outer inner : Set Point) (target : Point)
    (visits : ℕ → ℕ) (m : ℕ) : Set StepPath :=
  atomEvent initial
    (fun j ↦ terminalEntranceTime zeroClock outer inner j)
    (fun j start ↦ boundaryVisitAtom outer target start (visits j)) m

/-- The sequential stopped atom is exactly the indicated vector of literal
segment visit counts, provided all selected segments are complete. -/
theorem mem_visitVectorAtom_iff
    {initial : Set StepPath} (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (target : Point) (htarget : target ∉ outer)
    (horizon : ℕ) (visits : ℕ → ℕ) (m : ℕ)
    (hcomplete : ∀ j < m,
      excursionStart (trajectory omega) outer inner horizon (j + 1) ≤ horizon) :
    omega ∈ visitVectorAtom initial outer inner target visits m ↔
      omega ∈ initial ∧
        ∀ j < m,
          innerVisitCount (trajectory omega) outer inner horizon target j = visits j := by
  unfold visitVectorAtom
  rw [mem_atomEvent_iff]
  constructor
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    exact (terminalSegment_mem_boundaryVisitAtom_iff omega outer inner target htarget
      horizon j (visits j) (hcomplete j hj)).1 (hall j hj).2
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    have hclock := terminalEntranceTime_eq_excursionFinish
      omega outer inner horizon j (hcomplete j hj)
    refine ⟨?_, ?_⟩
    · rw [hclock]
      exact WithTop.coe_lt_top _
    · exact (terminalSegment_mem_boundaryVisitAtom_iff
        omega outer inner target htarget horizon j (visits j) (hcomplete j hj)).2
          (hall j hj)

lemma stoppedPosition_terminalEntrance_mem_inner
    (omega : StepPath) (outer inner : Set Point) (j : ℕ)
    (hfinite : terminalEntranceTime zeroClock outer inner j omega < ⊤) :
    stoppedPosition (terminalEntranceTime zeroClock outer inner j) omega ∈ inner := by
  have hne : terminalEntranceTime zeroClock outer inner j omega ≠ ⊤ :=
    WithTop.lt_top_iff_ne_top.mp hfinite
  lift terminalEntranceTime zeroClock outer inner j omega to ℕ using hne with t ht
  rw [stoppedPosition_eq_of_eq ht.symm]
  exact terminalEntranceTime_mem_inner_of_eq ht.symm

/-- Reusable sequential probability bound for a fixed literal visit vector.
The stopped-history premise is explicit; in particular it cannot silently be
instantiated by a future-dependent successful/profile event.  Recurrence
supplies finiteness of all clocks, and annular geometry localizes the kernel
bounds to starts on `inner`. -/
theorem visitVectorAtom_measure_mem_Icc_prod
    {initial : Set StepPath} (outer inner : Set Point)
    (houter : outer.Nonempty) (hinner : inner.Nonempty)
    (target : Point) (visits : ℕ → ℕ)
    (hhistory : ∀ j, IsMeasurableAtWithTopStopping
      (terminalEntranceTime zeroClock outer inner j)
      (visitVectorAtom initial outer inner target visits j))
    (lower upper : ℕ → ℝ≥0∞)
    (hprob : ∀ j start, start ∈ inner →
      fairSteps (boundaryVisitAtom outer target start (visits j)) ∈
        Set.Icc (lower j) (upper j)) :
    ∀ m, fairSteps (visitVectorAtom initial outer inner target visits m) ∈
      Set.Icc
        (fairSteps initial * ∏ j ∈ Finset.range m, lower j)
        (fairSteps initial * ∏ j ∈ Finset.range m, upper j) := by
  have hzeroFinite : ∀ᵐ omega ∂fairSteps, zeroClock omega < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by
      simp [zeroClock]
  have hallFinite := ae_all_alternatingAnnularClock_lt_top_of_nonempty
    hzeroFinite houter hinner
  have hfinite (j : ℕ) :
      ∀ᵐ omega ∂fairSteps, terminalEntranceTime zeroClock outer inner j omega < ⊤ := by
    filter_upwards [hallFinite] with omega homega
    exact homega (2 * j + 2)
  have hbound := atomEvent_measure_mem_Icc_prod_on
    (initial := initial)
    (tau := fun j ↦ terminalEntranceTime zeroClock outer inner j)
    (fresh := fun j start ↦ boundaryVisitAtom outer target start (visits j))
    (fun j ↦ isStoppingTime_terminalEntranceTime
      isStoppingTime_zeroClock outer inner j)
    (by simpa only [visitVectorAtom] using hhistory)
    hfinite (fun _ ↦ inner)
    (fun j omega _hmem hclock ↦
      stoppedPosition_terminalEntrance_mem_inner omega outer inner j hclock)
    (fun j start ↦ measurableSet_boundaryVisitAtom outer target start (visits j))
    lower upper hprob
  simpa only [visitVectorAtom] using hbound

/-- The actual finite-vector atom for HLOZ's required terminal segments. -/
def requiredTerminalVisitVectorAtom
    (initial : Set StepPath) (n : ℕ) (profileDelta : ℝ) (x : Point)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → ℕ) :
    Set StepPath :=
  visitVectorAtom initial (terminalOuterBoundary n x) (terminalInnerBoundary n x) x
    (fun j ↦ if hj : j < AppendixLocalTime.requiredTerminalCount n profileDelta
      then visits ⟨j, hj⟩ else 0)
    (AppendixLocalTime.requiredTerminalCount n profileDelta)

/-- On a stopped successful path, the fixed atom above is literally equality
of the canonical terminal visit vector.  This is pathwise only; using a
future-dependent successful event as `initial` in a probability product still
requires a separate stopped-data decomposition. -/
theorem mem_requiredTerminalVisitVectorAtom_iff
    {initial : Set StepPath} {omega : StepPath} {n horizon : ℕ}
    {profileDelta : ℝ} {x : Point}
    (htarget : x ∉ terminalOuterBoundary n x)
    (hn : 1 ≤ n) (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : SuccessfulPoint (trajectory omega) n horizon profileDelta x)
    (hstep : ∀ k, Adjacent (trajectory omega k) (trajectory omega (k + 1)))
    (visits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → ℕ) :
    omega ∈ requiredTerminalVisitVectorAtom initial n profileDelta x visits ↔
      omega ∈ initial ∧
        terminalVisitVector (trajectory omega) n horizon profileDelta x = visits := by
  classical
  let m := AppendixLocalTime.requiredTerminalCount n profileDelta
  have hcomplete : ∀ j < m,
      excursionStart (trajectory omega) (terminalOuterBoundary n x)
        (terminalInnerBoundary n x) horizon (j + 1) ≤ horizon := by
    intro j hj
    have hsegment := terminalVisitSegment_complete_of_stopped_success
      hn hexit hx hstep ⟨j, hj⟩
    simpa [terminalSegmentExitTime] using hsegment
  unfold requiredTerminalVisitVectorAtom
  rw [mem_visitVectorAtom_iff omega (terminalOuterBoundary n x)
    (terminalInnerBoundary n x) x htarget horizon _ m hcomplete]
  constructor
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, funext fun j ↦ ?_⟩
    simpa [terminalVisitVector, terminalExcursionVisits] using hall j j.isLt
  · rintro ⟨hinitial, hvector⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    have hjEq := congrFun hvector ⟨j, hj⟩
    rw [dif_pos hj]
    simpa [terminalVisitVector, terminalExcursionVisits] using hjEq

/-! ## Marking the outer endpoint -/

/-- Event that the first boundary hit of a fresh walk started at `start`
occurs at the specified endpoint. -/
def boundaryExitEndpointSteps
    (boundary : Set Point) (start endpoint : Point) : Set StepPath :=
  ⋃ N : ℕ, {omega | AbsoluteBoundaryFirstAt boundary start omega N ∧
    PlanarPotential.trajectoryFrom start omega N = endpoint}

lemma measurableSet_absoluteBoundaryFirstAt
    (boundary : Set Point) (start : Point) (N : ℕ) :
    MeasurableSet {omega : StepPath |
      AbsoluteBoundaryFirstAt boundary start omega N} := by
  have heq : {omega : StepPath |
      AbsoluteBoundaryFirstAt boundary start omega N} =
      {omega | PlanarPotential.trajectoryFrom start omega N ∈ boundary} ∩
        avoidsBoundaryFromBefore boundary start N := by
    ext omega
    rfl
  rw [heq]
  have heval : Measurable (fun omega : StepPath ↦
      PlanarPotential.trajectoryFrom start omega N) :=
    (measurable_pi_apply N).comp (PlanarPotential.measurable_trajectoryFrom start)
  exact (heval (Set.to_countable boundary).measurableSet).inter
    (incrementFiltration.le N _
      (measurableSet_avoidsBoundaryFromBefore_filtration boundary start N))

theorem measurableSet_boundaryExitEndpointSteps
    (boundary : Set Point) (start endpoint : Point) :
    MeasurableSet (boundaryExitEndpointSteps boundary start endpoint) := by
  apply MeasurableSet.iUnion
  intro N
  apply (measurableSet_absoluteBoundaryFirstAt boundary start N).inter
  have heval : Measurable (fun omega : StepPath ↦
      PlanarPotential.trajectoryFrom start omega N) :=
    (measurable_pi_apply N).comp (PlanarPotential.measurable_trajectoryFrom start)
  exact heval (Set.to_countable ({endpoint} : Set Point)).measurableSet

lemma mem_boundaryExitEndpointSteps_iff_of_firstAt
    {boundary : Set Point} {start endpoint : Point}
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N) :
    omega ∈ boundaryExitEndpointSteps boundary start endpoint ↔
      PlanarPotential.trajectoryFrom start omega N = endpoint := by
  constructor
  · intro hendpoint
    obtain ⟨M, hMfirst, hMendpoint⟩ := Set.mem_iUnion.mp hendpoint
    have hMN : M = N := by
      rcases lt_trichotomy M N with hlt | heq | hgt
      · exact (hfirst.2 M hlt hMfirst.1).elim
      · exact heq
      · exact (hMfirst.2 N hgt hfirst.1).elim
    subst M
    exact hMendpoint
  · intro hendpoint
    exact Set.mem_iUnion.mpr ⟨N, hfirst, hendpoint⟩

/-- Joint visit-count/outer-endpoint atom for one fresh complete segment. -/
def boundaryVisitExitAtom
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point) :
    Set StepPath :=
  boundaryVisitAtom boundary target start k ∩
    boundaryExitEndpointSteps boundary start endpoint

theorem measurableSet_boundaryVisitExitAtom
    (boundary : Set Point) (target start : Point) (k : ℕ) (endpoint : Point) :
    MeasurableSet (boundaryVisitExitAtom boundary target start k endpoint) :=
  (measurableSet_boundaryVisitAtom boundary target start k).inter
    (measurableSet_boundaryExitEndpointSteps boundary start endpoint)

/-- Marked version of `terminalSegment_mem_boundaryVisitAtom_iff`: the fresh
atom records both the literal visit count and the actual next outer endpoint. -/
theorem terminalSegment_mem_boundaryVisitExitAtom_iff
    (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (target : Point) (htarget : target ∉ outer)
    (horizon j k : ℕ) (endpoint : Point)
    (hcomplete : excursionStart (trajectory omega) outer inner horizon (j + 1) ≤
      horizon) :
    postWithTopStoppingSteps (terminalEntranceTime zeroClock outer inner j) omega ∈
        boundaryVisitExitAtom outer target
          (stoppedPosition (terminalEntranceTime zeroClock outer inner j) omega) k endpoint ↔
      innerVisitCount (trajectory omega) outer inner horizon target j = k ∧
        trajectory omega
          (excursionStart (trajectory omega) outer inner horizon (j + 1)) = endpoint := by
  let t := excursionFinish (trajectory omega) outer inner horizon j
  let u := excursionStart (trajectory omega) outer inner horizon (j + 1)
  have ht : terminalEntranceTime zeroClock outer inner j omega = t :=
    terminalEntranceTime_eq_excursionFinish omega outer inner horizon j hcomplete
  have hu : terminalExitTime zeroClock outer inner j omega = u :=
    terminalExitTime_eq_excursionStart omega outer inner horizon j hcomplete
  have hfirstEq : firstHitSetAfter
      (terminalEntranceTime zeroClock outer inner j) outer omega = u := by
    rw [← terminalExitTime_eq_firstHitSetAfter outer inner j]
    exact hu
  have hboundary := absoluteBoundaryFirstAt_post_firstHitSetAfter ht hfirstEq
  have hcount := terminalSegment_mem_boundaryVisitAtom_iff
    omega outer inner target htarget horizon j k hcomplete
  have hendpoint := mem_boundaryExitEndpointSteps_iff_of_firstAt
    (endpoint := endpoint) hboundary
  have hfutureEndpoint :
      PlanarPotential.trajectoryFrom
          (stoppedPosition (terminalEntranceTime zeroClock outer inner j) omega)
          (postWithTopStoppingSteps (terminalEntranceTime zeroClock outer inner j) omega)
          (u - t) = trajectory omega u := by
    have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq ht
    have hpos := stoppedPosition_eq_of_eq ht
    have htu : t ≤ u :=
      excursionFinish_le_next_start (trajectory omega) outer inner horizon j
    rw [hpost, hpos, trajectoryFrom_shiftSteps_eq, Nat.add_sub_of_le htu]
  unfold boundaryVisitExitAtom
  rw [Set.mem_inter_iff, hcount, hendpoint, hfutureEndpoint]

/-- Sequential atom specifying both the visit count and the next outer
endpoint of every selected complete segment. -/
def visitExitVectorAtom
    (initial : Set StepPath) (outer inner : Set Point) (target : Point)
    (visits : ℕ → ℕ) (exits : ℕ → Point) (m : ℕ) : Set StepPath :=
  atomEvent initial
    (fun j ↦ terminalEntranceTime zeroClock outer inner j)
    (fun j start ↦ boundaryVisitExitAtom outer target start (visits j) (exits j)) m

theorem mem_visitExitVectorAtom_iff
    {initial : Set StepPath} (omega : StepPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (target : Point) (htarget : target ∉ outer)
    (horizon : ℕ) (visits : ℕ → ℕ) (exits : ℕ → Point) (m : ℕ)
    (hcomplete : ∀ j < m,
      excursionStart (trajectory omega) outer inner horizon (j + 1) ≤ horizon) :
    omega ∈ visitExitVectorAtom initial outer inner target visits exits m ↔
      omega ∈ initial ∧
        ∀ j < m,
          innerVisitCount (trajectory omega) outer inner horizon target j = visits j ∧
            trajectory omega
              (excursionStart (trajectory omega) outer inner horizon (j + 1)) = exits j := by
  unfold visitExitVectorAtom
  rw [mem_atomEvent_iff]
  constructor
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    exact (terminalSegment_mem_boundaryVisitExitAtom_iff
      omega outer inner target htarget horizon j (visits j) (exits j)
        (hcomplete j hj)).1 (hall j hj).2
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    have hclock := terminalEntranceTime_eq_excursionFinish
      omega outer inner horizon j (hcomplete j hj)
    refine ⟨?_, ?_⟩
    · rw [hclock]
      exact WithTop.coe_lt_top _
    · exact (terminalSegment_mem_boundaryVisitExitAtom_iff
        omega outer inner target htarget horizon j (visits j) (exits j)
          (hcomplete j hj)).2 (hall j hj)

/-- Sequential shell-local product bounds for marked visit/exit atoms. -/
theorem visitExitVectorAtom_measure_mem_Icc_prod
    {initial : Set StepPath} (outer inner : Set Point)
    (houter : outer.Nonempty) (hinner : inner.Nonempty)
    (target : Point) (visits : ℕ → ℕ) (exits : ℕ → Point)
    (hhistory : ∀ j, IsMeasurableAtWithTopStopping
      (terminalEntranceTime zeroClock outer inner j)
      (visitExitVectorAtom initial outer inner target visits exits j))
    (lower upper : ℕ → ℝ≥0∞)
    (hprob : ∀ j start, start ∈ inner →
      fairSteps (boundaryVisitExitAtom outer target start (visits j) (exits j)) ∈
        Set.Icc (lower j) (upper j)) :
    ∀ m, fairSteps (visitExitVectorAtom initial outer inner target visits exits m) ∈
      Set.Icc
        (fairSteps initial * ∏ j ∈ Finset.range m, lower j)
        (fairSteps initial * ∏ j ∈ Finset.range m, upper j) := by
  have hzeroFinite : ∀ᵐ omega ∂fairSteps, zeroClock omega < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp [zeroClock]
  have hallFinite := ae_all_alternatingAnnularClock_lt_top_of_nonempty
    hzeroFinite houter hinner
  have hfinite (j : ℕ) :
      ∀ᵐ omega ∂fairSteps, terminalEntranceTime zeroClock outer inner j omega < ⊤ := by
    filter_upwards [hallFinite] with omega homega
    exact homega (2 * j + 2)
  have hbound := atomEvent_measure_mem_Icc_prod_on
    (initial := initial)
    (tau := fun j ↦ terminalEntranceTime zeroClock outer inner j)
    (fresh := fun j start ↦
      boundaryVisitExitAtom outer target start (visits j) (exits j))
    (fun j ↦ isStoppingTime_terminalEntranceTime
      isStoppingTime_zeroClock outer inner j)
    (by simpa only [visitExitVectorAtom] using hhistory)
    hfinite (fun _ ↦ inner)
    (fun j omega _hmem hclock ↦
      stoppedPosition_terminalEntrance_mem_inner omega outer inner j hclock)
    (fun j start ↦
      measurableSet_boundaryVisitExitAtom outer target start (visits j) (exits j))
    lower upper hprob
  simpa only [visitExitVectorAtom] using hbound

/-- HLOZ specialization of the marked vector atom to all required terminal
segments. -/
def requiredTerminalVisitExitVectorAtom
    (initial : Set StepPath) (n : ℕ) (profileDelta : ℝ) (x : Point)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → ℕ)
    (exits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → Point) :
    Set StepPath :=
  visitExitVectorAtom initial (terminalOuterBoundary n x) (terminalInnerBoundary n x) x
    (fun j ↦ if hj : j < AppendixLocalTime.requiredTerminalCount n profileDelta
      then visits ⟨j, hj⟩ else 0)
    (fun j ↦ if hj : j < AppendixLocalTime.requiredTerminalCount n profileDelta
      then exits ⟨j, hj⟩ else 0)
    (AppendixLocalTime.requiredTerminalCount n profileDelta)

theorem mem_requiredTerminalVisitExitVectorAtom_iff
    {initial : Set StepPath} {omega : StepPath} {n horizon : ℕ}
    {profileDelta : ℝ} {x : Point}
    (htarget : x ∉ terminalOuterBoundary n x)
    (hn : 1 ≤ n) (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : SuccessfulPoint (trajectory omega) n horizon profileDelta x)
    (hstep : ∀ k, Adjacent (trajectory omega k) (trajectory omega (k + 1)))
    (visits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → ℕ)
    (exits : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → Point) :
    omega ∈ requiredTerminalVisitExitVectorAtom
        initial n profileDelta x visits exits ↔
      omega ∈ initial ∧
        terminalVisitVector (trajectory omega) n horizon profileDelta x = visits ∧
        ∀ j : Fin (AppendixLocalTime.requiredTerminalCount n profileDelta),
          trajectory omega
            (terminalSegmentExitTime (trajectory omega) n horizon x j) = exits j := by
  classical
  let m := AppendixLocalTime.requiredTerminalCount n profileDelta
  have hcomplete : ∀ j < m,
      excursionStart (trajectory omega) (terminalOuterBoundary n x)
        (terminalInnerBoundary n x) horizon (j + 1) ≤ horizon := by
    intro j hj
    have hsegment := terminalVisitSegment_complete_of_stopped_success
      hn hexit hx hstep ⟨j, hj⟩
    simpa [terminalSegmentExitTime] using hsegment
  unfold requiredTerminalVisitExitVectorAtom
  rw [mem_visitExitVectorAtom_iff omega (terminalOuterBoundary n x)
    (terminalInnerBoundary n x) x htarget horizon _ _ m hcomplete]
  constructor
  · rintro ⟨hinitial, hall⟩
    refine ⟨hinitial, funext fun j ↦ ?_, ?_⟩
    · simpa [terminalVisitVector, terminalExcursionVisits] using
        (hall j j.isLt).1
    · intro j
      simpa [terminalSegmentExitTime] using (hall j j.isLt).2
  · rintro ⟨hinitial, hvector, hexits⟩
    refine ⟨hinitial, ?_⟩
    intro j hj
    have hjEq := congrFun hvector ⟨j, hj⟩
    refine ⟨?_, ?_⟩
    · rw [dif_pos hj]
      simpa [terminalVisitVector, terminalExcursionVisits] using hjEq
    · rw [dif_pos hj]
      simpa [terminalSegmentExitTime] using hexits ⟨j, hj⟩

end

end Erdos1165.TerminalSequentialVisitLaw
