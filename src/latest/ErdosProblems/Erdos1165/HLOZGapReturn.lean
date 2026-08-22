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

import ErdosProblems.Erdos1165.HLOZGapEstimate

/-!
# The stopped two-point-return certificate in HLOZ Lemma 4.10

`HLOZGapEstimate` proves the geometric iteration from an abstract sequence of
stopping times.  This module constructs that sequence canonically.  Starting
from one stopped visit to a random candidate, `returnLadder` lists its strict
successive revisits before a deterministic deadline.  Each revisit forces the
fresh block following the preceding clock to fail the checked logarithmic
avoidance event.  Thus an application supplies only the genuine pathwise
input: the exceptional candidate event entails the required number of
revisits.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapReturn

open HLOZGapEstimate

theorem returnLadder_eq_target_of_stage
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hbase : ∀ w, trajectory w (σ w) = target w)
    (r : ℕ) {w : StepPath}
    (hw : w ∈ returnLadderStage σ target deadline r) :
    trajectory w (returnLadder σ target deadline r w) = target w := by
  cases r with
  | zero => exact hbase w
  | succ r =>
      have hlt : returnLadder σ target deadline (r + 1) w < deadline := hw
      rw [returnLadder_succ] at hlt ⊢
      have hex := (nextVisitBefore_lt_deadline_iff w).mp hlt
      unfold nextVisitBefore
      rw [dif_pos hex]
      exact (Nat.find_spec hex).2.2

theorem returnLadderStage_succ_subset
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline r : ℕ}
    (hσle : ∀ w, σ w ≤ deadline) :
    returnLadderStage σ target deadline (r + 1) ⊆
      returnLadderStage σ target deadline r := by
  intro w hw
  cases r with
  | zero => trivial
  | succ r =>
      change returnLadder σ target deadline (r + 2) w < deadline at hw
      change returnLadder σ target deadline (r + 1) w < deadline
      exact (returnLadder_mono_step (r := r + 1) hσle w).trans_lt hw

theorem returnLadderStage_succ_subset_avoidance_compl
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline r : ℕ}
    (hσle : ∀ w, σ w ≤ deadline)
    (hbase : ∀ w, trajectory w (σ w) = target w) :
    returnLadderStage σ target deadline (r + 1) ⊆
      {w | w ∈ returnLadderStage σ target deadline r ∧
        postStoppingBlock (returnLadder σ target deadline r) deadline w ∈
          (TwoPointLogAvoidance.avoidingBlocks (0 : Point) deadline)ᶜ} := by
  intro w hw
  have hwPrev : w ∈ returnLadderStage σ target deadline r :=
    returnLadderStage_succ_subset hσle hw
  refine ⟨hwPrev, ?_⟩
  intro havoid
  have havoidShift : shiftSteps (returnLadder σ target deadline r w) w ∈
      TwoPointLogAvoidance.avoidsPair (0 : Point) deadline := by
    apply (TwoPointLogAvoidance.mem_avoidingBlocks_stepPrefix_iff
      (0 : Point) deadline _).mp
    change postStoppingBlock (returnLadder σ target deadline r) deadline w ∈
      TwoPointLogAvoidance.avoidingBlocks (0 : Point) deadline
    exact havoid
  have hnextLt : returnLadder σ target deadline (r + 1) w < deadline := hw
  have hex : ∃ j, j < deadline ∧
      returnLadder σ target deadline r w < j ∧
        trajectory w j = target w := by
    rw [returnLadder_succ] at hnextLt
    exact (nextVisitBefore_lt_deadline_iff w).mp hnextLt
  have hnextSpec :
      returnLadder σ target deadline r w <
          returnLadder σ target deadline (r + 1) w ∧
        trajectory w (returnLadder σ target deadline (r + 1) w) = target w := by
    rw [returnLadder_succ]
    unfold nextVisitBefore
    rw [dif_pos hex]
    exact ⟨(Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2⟩
  let d := returnLadder σ target deadline (r + 1) w -
    returnLadder σ target deadline r w
  have hdpos : 0 < d := Nat.sub_pos_of_lt hnextSpec.1
  have hdle : d ≤ deadline := by
    dsimp only [d]
    exact (Nat.sub_le _ _).trans (returnLadder_le_deadline hσle (r + 1) w)
  have hprevTarget :
      trajectory w (returnLadder σ target deadline r w) = target w :=
    returnLadder_eq_target_of_stage hbase r hwPrev
  have hnextTarget :
      trajectory w (returnLadder σ target deadline (r + 1) w) = target w :=
    hnextSpec.2
  have hadd : returnLadder σ target deadline r w + d =
      returnLadder σ target deadline (r + 1) w := by
    dsimp only [d]
    exact Nat.add_sub_of_le hnextSpec.1.le
  have hzero :
      trajectory (shiftSteps (returnLadder σ target deadline r w) w) d =
        (0 : Point) := by
    rw [← trajectory_add_sub_trajectory, hadd, hnextTarget, hprevTarget, sub_self]
  exact (havoidShift d hdpos hdle).1 hzero

/-- The minimal stopped-candidate data needed to turn a path event into the
geometric return cost.  In the HLOZ application, `start` is the first visit to
one enumerated candidate and `event_subset` is the deterministic local-time
deficit calculation. -/
structure StoppedTargetReturnWitness
    (event : Set WalkPath) (deadline returns : ℕ) where
  start : StepPath → ℕ
  target : StepPath → Point
  start_isStopping : IsFiniteStoppingTime start
  start_le_deadline : ∀ w, start w ≤ deadline
  target_observable : ∀ x,
    IsMeasurableAtStopping start {w | target w = x}
  start_at_target : ∀ w, trajectory w (start w) = target w
  event_subset : trajectory ⁻¹' event ⊆
    returnLadderStage start target deadline returns

/-- The canonical stopped return ladder is a complete
`TwoPointReturnCertificate`; no per-return stopping or measurability premise
remains. -/
noncomputable def StoppedTargetReturnWitness.toTwoPointReturnCertificate
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedTargetReturnWitness event deadline returns) :
    TwoPointReturnCertificate event deadline returns where
  stage := returnLadderStage h.start h.target deadline
  stop := returnLadder h.start h.target deadline
  relativePoint := fun _ _ ↦ 0
  event_subset := h.event_subset
  stage_zero := returnLadderStage_zero _ _ _
  stop_isStopping := fun r _ ↦
    returnLadder_isFiniteStoppingTime h.start_isStopping h.start_le_deadline
      h.target_observable r
  spatial_observable := fun _r _ x ↦
    returnLadderStage_targetFiber_observable h.start_isStopping
      h.start_le_deadline h.target_observable x
  next_subset := fun _r _ ↦
    returnLadderStage_succ_subset_avoidance_compl
      h.start_le_deadline h.start_at_target

/-- Strong Markov and the logarithmic avoidance theorem now consume only a
single stopped-candidate witness. -/
theorem measure_le_geometricReturnCost_of_stoppedTarget
    {event : Set WalkPath} {deadline returns : ℕ}
    (hevent : MeasurableSet event) (hdeadline : 2 ≤ deadline)
    (h : StoppedTargetReturnWitness event deadline returns) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log deadline)) returns :=
  measure_le_geometricReturnCost_of_twoPointCertificate hevent hdeadline
    h.toTwoPointReturnCertificate

section FiniteScreen

variable {Band Site : Type*}

/-- One stopped-target witness per enumerated slot discharges the complete
per-candidate geometric premise of the finite `Gap` engine. -/
theorem perCandidateGeometricReturnBound_of_stoppedTargets
    (bands : Finset Band) (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hdeadline : ∀ band ∈ bands, 2 ≤ deadline band)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedTargetReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band)) :
    Gap.PerCandidateGeometricReturnBound simpleRandomWalk bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes)
      (fun band ↦ 1 / (100 * Real.log (deadline band))) returns := by
  intro band hband i hi
  exact measure_le_geometricReturnCost_of_stoppedTarget
    (hmeas band i) (hdeadline band hband) (hwitness band hband i hi)

/-- Full finite-screen estimate with the strong-Markov return ladder already
constructed.  The remaining hypotheses are deterministic event coverage,
measurability of the slot events, and one initial stopped visit per slot. -/
theorem measure_gapDeficitExceptionalEvent_le_overflow_add_stoppedGeometric
    (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness (HLOZPathEvents.gapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hdeadline : ∀ band ∈ bands, 2 ≤ deadline band)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedTargetReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band)) :
    simpleRandomWalk (HLOZPathEvents.gapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (deadline band))) (returns band) := by
  apply measure_gapDeficitExceptionalEvent_le_overflow_add_geometric
    t m bands sites budget deadline returns realizes hpath hmeas hdeadline
  intro band hband i hi
  exact (hwitness band hband i hi).toTwoPointReturnCertificate

end FiniteScreen

end Erdos1165.HLOZGapReturn
