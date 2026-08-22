/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZGapCandidateMeasurability
import ErdosProblems.Erdos1165.HLOZGapStoppedCandidate

/-!
# A fixed-point local-time tail from the stopped return ladder

The one-step recentering used for the checker source has one genuine
obstruction: the discarded origin may already have reached the current
level.  This file converts that fixed-site event into the existing checked
geometric-return estimate.  The deadline is enlarged by one so a visit at
the original cutoff is strictly before the return-ladder deadline.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZFixedPointLocalTimeTail

open HLOZGapCandidateMeasurability HLOZGapEstimate HLOZGapReturn
open HLOZGapStoppedCandidate

/-- The origin has accumulated at least `k` visits by time `cutoff`. -/
def originLocalTimeEvent (cutoff k : ℕ) : Set WalkPath :=
  {s | k ≤ localTime s cutoff 0}

theorem measurableSet_originLocalTimeEvent (cutoff k : ℕ) :
    MeasurableSet (originLocalTimeEvent cutoff k) := by
  exact measurableSet_le measurable_const (measurable_localTime_fixed cutoff 0)

/-- The constant time-zero location is observable at its constant stopping
time. -/
theorem stoppedLocation_zero_observable (x : Point) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ 0)
      {w | stoppedLocation (fun _ : StepPath ↦ 0) w = x} := by
  exact stoppedLocation_fiber_observable (isFiniteStoppingTime_const 0) x

/-- A strict visit schedule after a clock bounds the corresponding positive
levels of the return ladder based at that clock.  Unlike the first-hit
adapter, this keeps the already-present visit at the base clock. -/
theorem returnLadder_succ_le_visitTime_from_base
    {start : StepPath → ℕ} {target : StepPath → Point}
    {deadline visits : ℕ} {w : StepPath}
    (times : Fin visits → ℕ) (hmono : StrictMono times)
    (hafter : ∀ i, start w < times i)
    (hbefore : ∀ i, times i < deadline)
    (hvisit : ∀ i, trajectory w (times i) = target w)
    (i : Fin visits) :
    returnLadder start target deadline (i + 1) w ≤ times i := by
  have hle : ∀ n : ℕ, ∀ hn : n < visits,
      returnLadder start target deadline (n + 1) w ≤ times ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        rw [returnLadder_succ, returnLadder_zero]
        apply (nextVisitBefore_le_iff (hbefore ⟨0, hn⟩) w).2
        exact ⟨times ⟨0, hn⟩, le_rfl, hafter ⟨0, hn⟩, hvisit ⟨0, hn⟩⟩
    | succ n ih =>
        intro hn
        have hnprev : n < visits := lt_trans (Nat.lt_succ_self n) hn
        have hprev := ih hnprev
        have hstrict : times ⟨n, hnprev⟩ < times ⟨n + 1, hn⟩ := by
          apply hmono
          exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self n)
        rw [show n + 1 + 1 = (n + 1) + 1 by omega, returnLadder_succ]
        apply (nextVisitBefore_le_iff (hbefore ⟨n + 1, hn⟩) w).2
        exact ⟨times ⟨n + 1, hn⟩, le_rfl, hprev.trans_lt hstrict,
          hvisit ⟨n + 1, hn⟩⟩
  exact hle i i.isLt

/-- A nonempty strict schedule after the base clock forces the matching
positive return-ladder stage. -/
theorem returnLadderStage_of_strictVisitSchedule_from_base
    {start : StepPath → ℕ} {target : StepPath → Point}
    {deadline returns : ℕ} {w : StepPath} (hreturns : 0 < returns)
    (h : HasStrictVisitSchedule start target deadline returns w) :
    w ∈ returnLadderStage start target deadline returns := by
  cases returns with
  | zero => omega
  | succ r =>
      rcases h with ⟨times, hmono, hafter, hbefore, hvisit⟩
      let i : Fin (r + 1) := ⟨r, by omega⟩
      have hle := returnLadder_succ_le_visitTime_from_base
        times hmono hafter hbefore hvisit i
      change returnLadder start target deadline (r + 1) w < deadline
      simpa only [i] using hle.trans_lt (hbefore i)

/-- At least `k` visits through `cutoff` give `k-1` strict visits after the
automatic time-zero visit.  In the stopped-candidate convention the first
strict visit initializes the target and the remaining `k-2` visits are the
geometric-return exponent. -/
noncomputable def originLocalTimeWitness
    (cutoff k : ℕ) (hk : 2 ≤ k) :
    StoppedCandidateLocalTimeWitness
      (originLocalTimeEvent cutoff k) (cutoff + 1) (k - 2) where
  past := fun _ ↦ 0
  candidate := stoppedLocation (fun _ ↦ 0)
  past_isStopping := isFiniteStoppingTime_const 0
  past_lt_deadline := fun _ ↦ by omega
  candidate_observable := stoppedLocation_fiber_observable
    (isFiniteStoppingTime_const 0)
  event_gain := by
    intro w hw
    change k ≤ localTime (trajectory w) cutoff 0 at hw
    change localTime (trajectory w) 0
        (stoppedLocation (fun _ : StepPath ↦ 0) w) + (k - 2 + 1) ≤
      localTime (trajectory w) cutoff
        (stoppedLocation (fun _ : StepPath ↦ 0) w)
    have hlocation : stoppedLocation (fun _ : StepPath ↦ 0) w = 0 := by
      simp [stoppedLocation, trajectory_zero]
    rw [hlocation]
    have hzero : localTime (trajectory w) 0 0 = 1 := by
      simp [localTime, localTimePrefix, pathPrefix, trajectory_zero]
    rw [hzero]
    omega

/-- Direct time-zero return witness.  The automatic visit at time zero is
the ladder base, so `k` visits by the cutoff produce exactly `k-1` strict
returns before the enlarged deadline. -/
noncomputable def originLocalTimeTargetWitness
    (cutoff k : ℕ) (hk : 2 ≤ k) :
    StoppedTargetReturnWitness
      (originLocalTimeEvent cutoff k) (cutoff + 1) (k - 1) where
  start := fun _ ↦ 0
  target := stoppedLocation (fun _ ↦ 0)
  start_isStopping := isFiniteStoppingTime_const 0
  start_le_deadline := fun _ ↦ by omega
  target_observable := stoppedLocation_fiber_observable
    (isFiniteStoppingTime_const 0)
  start_at_target := fun _ ↦ rfl
  event_subset := by
    intro w hw
    apply returnLadderStage_of_strictVisitSchedule_from_base (by omega)
    apply hasStrictVisitSchedule_of_localTime_gain (by omega)
    change localTime (trajectory w) 0
        (stoppedLocation (fun _ : StepPath ↦ 0) w) + (k - 1) ≤
      localTime (trajectory w) cutoff
        (stoppedLocation (fun _ : StepPath ↦ 0) w)
    have hlocation : stoppedLocation (fun _ : StepPath ↦ 0) w = 0 := by
      simp [stoppedLocation, trajectory_zero]
    rw [hlocation]
    have hzero : localTime (trajectory w) 0 0 = 1 := by
      simp [localTime, localTimePrefix, pathPrefix, trajectory_zero]
    rw [hzero]
    change k ≤ localTime (trajectory w) cutoff 0 at hw
    omega

/-- The checked finite-horizon logarithmic avoidance estimate gives the
origin local-time tail with the sharp exponent `k-1`. -/
theorem simpleRandomWalk_originLocalTimeEvent_le
    {cutoff k : ℕ} (hcutoff : 1 ≤ cutoff) (hk : 2 ≤ k) :
    simpleRandomWalk (originLocalTimeEvent cutoff k) ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log ((cutoff + 1 : ℕ) : ℝ))) (k - 1) := by
  exact @measure_le_geometricReturnCost_of_stoppedTarget
    (originLocalTimeEvent cutoff k) (cutoff + 1) (k - 1)
    (measurableSet_originLocalTimeEvent cutoff k)
    (by omega : 2 ≤ cutoff + 1) (originLocalTimeTargetWitness cutoff k hk)

end Erdos1165.HLOZFixedPointLocalTimeTail
