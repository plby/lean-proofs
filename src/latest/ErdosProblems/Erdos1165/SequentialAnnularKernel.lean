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

import ErdosProblems.Erdos1165.TerminalExcursionBridge
import ErdosProblems.Erdos1165.TerminalExcursionDisintegration

/-!
# Sequential annular boundary kernels

This file identifies the literal one-coordinate event after an annular
entrance clock.  The path starts at the random stopped position and hits a
target before its next visit to a designated vertex boundary.  Strong Markov
then gives an exact entrance mixture and uniform one-sided bounds.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.SequentialAnnularKernel

open TerminalExcursionBridge TerminalExcursionDisintegration

noncomputable section

/-- Pull the literal boundary-stopped walk event back to fresh increments
started at `start`. -/
def boundaryHitSteps (boundary : Set Point) (target start : Point) : Set StepPath :=
  PlanarPotential.trajectoryFrom start ⁻¹'
    walkHitBeforeBoundary boundary target

lemma measurableSet_boundaryHitSteps
    (boundary : Set Point) (target start : Point) :
    MeasurableSet (boundaryHitSteps boundary target start) := by
  exact (measurableSet_walkHitBeforeBoundary boundary target).preimage
    (PlanarPotential.measurable_trajectoryFrom start)

/-- The fresh increment probability is exactly the literal
`boundaryStoppedHitKernel`. -/
theorem fairSteps_boundaryHitSteps_toReal
    (boundary : Set Point) (target start : Point) :
    (fairSteps (boundaryHitSteps boundary target start)).toReal =
      boundaryStoppedHitKernel boundary target start := by
  unfold boundaryHitSteps boundaryStoppedHitKernel
    PlanarPotential.simpleRandomWalkFrom
  rw [Measure.map_apply (PlanarPotential.measurable_trajectoryFrom start)
    (measurableSet_walkHitBeforeBoundary boundary target)]

/-- Exact random-entrance mixture for hitting `target` before the next visit
to `boundary` after the `j`-th inner entrance. -/
theorem terminalEntrance_boundaryHit_disintegration
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (outer inner boundary : Set Point) (target : Point) (j : ℕ)
    (hA : IsMeasurableAtWithTopStopping
      (terminalEntranceTime tau outer inner j) A) :
    fairSteps {omega | omega ∈ A ∧
        terminalEntranceTime tau outer inner j omega < ⊤ ∧
        postWithTopStoppingSteps (terminalEntranceTime tau outer inner j) omega ∈
          boundaryHitSteps boundary target
            (stoppedPosition (terminalEntranceTime tau outer inner j) omega)} =
      ∑' start : Point,
        fairSteps ((A ∩ {omega |
            stoppedPosition (terminalEntranceTime tau outer inner j) omega = start}) ∩
          {omega | terminalEntranceTime tau outer inner j omega < ⊤}) *
            fairSteps (boundaryHitSteps boundary target start) := by
  exact terminalEntrance_fullTail_disintegration htau outer inner j hA
    (boundaryHitSteps boundary target) fun start ↦
      measurableSet_boundaryHitSteps boundary target start

/-- Uniform entrance-wise bounds for the literal boundary-stopped hit event.
This is the one-coordinate statement to iterate over the corrected complete
terminal segments. -/
theorem terminalEntrance_boundaryHit_bounds
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (outer inner boundary : Set Point) (target : Point) (j : ℕ)
    (hA : IsMeasurableAtWithTopStopping
      (terminalEntranceTime tau outer inner j) A)
    (lower upper : ℝ≥0∞)
    (hkernel : ∀ start, fairSteps (boundaryHitSteps boundary target start) ∈
      Set.Icc lower upper) :
    fairSteps {omega | omega ∈ A ∧
        terminalEntranceTime tau outer inner j omega < ⊤ ∧
        postWithTopStoppingSteps (terminalEntranceTime tau outer inner j) omega ∈
          boundaryHitSteps boundary target
            (stoppedPosition (terminalEntranceTime tau outer inner j) omega)} ∈
      Set.Icc
        (fairSteps (A ∩ {omega |
          terminalEntranceTime tau outer inner j omega < ⊤}) * lower)
        (fairSteps (A ∩ {omega |
          terminalEntranceTime tau outer inner j omega < ⊤}) * upper) := by
  exact strongMarkov_withTop_stoppedPosition_bounds
    (isStoppingTime_terminalEntranceTime htau outer inner j) hA
    (boundaryHitSteps boundary target)
    (fun start ↦ measurableSet_boundaryHitSteps boundary target start)
    lower upper hkernel

end

end Erdos1165.SequentialAnnularKernel
