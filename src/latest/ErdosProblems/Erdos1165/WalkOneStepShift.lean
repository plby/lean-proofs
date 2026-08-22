/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.Markov

/-!
# The one-step recentered planar walk

The odd-parity screening argument in HLOZ applies the even-parity estimate
after deleting the first increment and recentering at the new starting point.
This file records that operation directly on `WalkPath` and proves that it
preserves the canonical simple-random-walk law.  Event-specific stopping-clock
identities belong in their screening modules; no screening estimate is used
here.
-/

open MeasureTheory

namespace Erdos1165

/-- Delete time zero and recenter the remaining path at its time-one point. -/
def oneStepRecenter (s : WalkPath) : WalkPath :=
  fun n ↦ s (n + 1) - s 1

lemma measurable_oneStepRecenter : Measurable oneStepRecenter := by
  unfold oneStepRecenter
  fun_prop

@[simp] lemma oneStepRecenter_zero (s : WalkPath) :
    oneStepRecenter s 0 = 0 := by
  simp [oneStepRecenter]

/-- Recentring a trajectory is exactly deleting its first increment. -/
lemma oneStepRecenter_trajectory (omega : StepPath) :
    oneStepRecenter (trajectory omega) = trajectory (shiftSteps 1 omega) := by
  funext n
  rw [oneStepRecenter]
  have h := trajectory_add_sub_trajectory omega 1 n
  rw [show 1 + n = n + 1 by omega] at h
  exact h

/-- The one-step recentered path again has the canonical planar-walk law. -/
theorem simpleRandomWalk_map_oneStepRecenter :
    simpleRandomWalk.map oneStepRecenter = simpleRandomWalk := by
  calc
    simpleRandomWalk.map oneStepRecenter =
        fairSteps.map (oneStepRecenter ∘ trajectory) := by
      rw [simpleRandomWalk, Measure.map_map measurable_oneStepRecenter
        measurable_trajectory]
    _ = fairSteps.map (trajectory ∘ shiftSteps 1) := by
      congr 1
      funext omega
      exact oneStepRecenter_trajectory omega
    _ = (fairSteps.map (shiftSteps 1)).map trajectory := by
      rw [Measure.map_map measurable_trajectory (measurable_shiftSteps 1)]
    _ = fairSteps.map trajectory := by rw [fairSteps_map_shiftSteps]
    _ = simpleRandomWalk := rfl

/-- Pulling a measurable event back by the one-step recentering does not
change its probability. -/
theorem simpleRandomWalk_preimage_oneStepRecenter
    {A : Set WalkPath} (hA : MeasurableSet A) :
    simpleRandomWalk (oneStepRecenter ⁻¹' A) = simpleRandomWalk A := by
  rw [← Measure.map_apply_of_aemeasurable
      measurable_oneStepRecenter.aemeasurable hA,
    simpleRandomWalk_map_oneStepRecenter]

end Erdos1165
