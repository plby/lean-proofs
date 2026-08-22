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

import ErdosProblems.Erdos1165.BoundaryVisitRegeneration
import ErdosProblems.Erdos1165.SequentialAnnularKernel
import ErdosProblems.Erdos1165.BoundaryStoppedHarnack

/-!
# The one-excursion Bernoulli--geometric visit law

This file combines the first hit of a target from an annular entrance with
the positive-geometric regeneration law after that hit.  The resulting atom
is the literal number of target visits before the next hit of the designated
vertex boundary.  Strong Markov is applied only at the first target hit.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.BoundaryVisitLaw

open BoundaryVisitRegeneration SequentialAnnularKernel
open TerminalExcursionBridge TerminalExcursionDisintegration

noncomputable section

/-- The killing boundary in coordinates relative to `target`. -/
def relativeBoundary (boundary : Set Point) (target : Point) : Set Point :=
  {z | target + z ∈ boundary}

/-- First time the increment trajectory, started at `start`, reaches
`target`. -/
noncomputable def targetHitTime (start target : Point) :
    StepPath → WithTop ℕ :=
  firstHitSetAfter zeroClock ({target - start} : Set Point)

theorem isStoppingTime_targetHitTime (start target : Point) :
    IsStoppingTime incrementFiltration (targetHitTime start target) :=
  isStoppingTime_firstHitSetAfter isStoppingTime_zeroClock _

/-- Avoid the absolute boundary before time `n` for a walk started at
`start`. -/
def avoidsBoundaryFromBefore
    (boundary : Set Point) (start : Point) (n : ℕ) : Set StepPath :=
  {omega | ∀ k < n, PlanarPotential.trajectoryFrom start omega k ∉ boundary}

theorem measurableSet_avoidsBoundaryFromBefore_filtration
    (boundary : Set Point) (start : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n]
      (avoidsBoundaryFromBefore boundary start n) := by
  have heq : avoidsBoundaryFromBefore boundary start n =
      ⋂ k : Fin n,
        {omega : StepPath |
          PlanarPotential.trajectoryFrom start omega k ∉ boundary} := by
    ext omega
    simp only [avoidsBoundaryFromBefore, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h k
      exact h k k.isLt
    · intro h k hk
      exact h ⟨k, hk⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  let shifted : Set Point := {z | start + z ∈ boundary}
  have htrajectory :
      {omega : StepPath |
          PlanarPotential.trajectoryFrom start omega k ∈ boundary} =
        {omega : StepPath | trajectory omega k ∈ shifted} := by
    ext omega
    simp only [mem_ofPred_eq, shifted, PlanarPotential.trajectoryFrom]
  rw [← compl_ofPred, htrajectory]
  exact (incrementFiltration.mono (Nat.le_of_lt k.isLt) _
    (measurableSet_trajectory_mem_incrementFiltration k shifted)).compl

lemma targetHitTime_eq_implies_trajectoryFrom
    {start target : Point} {omega : StepPath} {n : ℕ}
    (h : targetHitTime start target omega = n) :
    PlanarPotential.trajectoryFrom start omega n = target := by
  have hmem : trajectory omega n ∈
      ({target - start} : Set Point) :=
    firstHitSetAfter_mem_of_eq h
  change trajectory omega n = target - start at hmem
  unfold PlanarPotential.trajectoryFrom
  rw [hmem]
  abel

/-- On a target-clock atom, the literal first-hit event is exactly avoidance
of the boundary before that clock. -/
lemma boundaryHitSteps_inter_targetHitTime_eq
    (boundary : Set Point) (target start : Point) (n : ℕ) :
    boundaryHitSteps boundary target start ∩
        {omega | targetHitTime start target omega = (n : WithTop ℕ)} =
      {omega | targetHitTime start target omega = (n : WithTop ℕ)} ∩
        avoidsBoundaryFromBefore boundary start n := by
  ext omega
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hhit, htime⟩
    change PlanarPotential.trajectoryFrom start omega ∈
      walkHitBeforeBoundary boundary target at hhit
    rw [BoundaryStoppedHarnack.mem_walkHitBeforeBoundary_iff_exists] at hhit
    obtain ⟨m, hmTarget, hmAvoid⟩ := hhit
    have hmRelative : trajectory omega m = target - start := by
      unfold PlanarPotential.trajectoryFrom at hmTarget
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hmTarget)
    have hclockLe : targetHitTime start target omega ≤ m :=
      (firstHitSetAfter_le_iff zeroClock ({target - start} : Set Point)
        omega m).2 ⟨m, le_rfl, by simp [zeroClock], by simpa using hmRelative⟩
    have hnm : n ≤ m := by simpa [htime] using hclockLe
    refine ⟨htime, ?_⟩
    intro k hk
    exact hmAvoid k (hk.trans_le hnm)
  · rintro ⟨htime, havoid⟩
    refine ⟨?_, htime⟩
    change PlanarPotential.trajectoryFrom start omega ∈
      walkHitBeforeBoundary boundary target
    rw [BoundaryStoppedHarnack.mem_walkHitBeforeBoundary_iff_exists]
    exact ⟨n, targetHitTime_eq_implies_trajectoryFrom htime, havoid⟩

theorem isMeasurableAtWithTopStopping_boundaryHitSteps
    (boundary : Set Point) (target start : Point) :
    IsMeasurableAtWithTopStopping (targetHitTime start target)
      (boundaryHitSteps boundary target start) := by
  intro n
  rw [boundaryHitSteps_inter_targetHitTime_eq]
  exact ((isStoppingTime_targetHitTime start target).measurableSet_eq n).inter
    (measurableSet_avoidsBoundaryFromBefore_filtration boundary start n)

theorem boundaryHitSteps_subset_targetHitTime_finite
    (boundary : Set Point) (target start : Point) :
    boundaryHitSteps boundary target start ⊆
      {omega | targetHitTime start target omega < ⊤} := by
  intro omega hhit
  change PlanarPotential.trajectoryFrom start omega ∈
    walkHitBeforeBoundary boundary target at hhit
  rw [BoundaryStoppedHarnack.mem_walkHitBeforeBoundary_iff_exists] at hhit
  obtain ⟨m, hmTarget, _hmAvoid⟩ := hhit
  have hmRelative : trajectory omega m = target - start := by
    unfold PlanarPotential.trajectoryFrom at hmTarget
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hmTarget)
  have hle : targetHitTime start target omega ≤ m :=
    (firstHitSetAfter_le_iff zeroClock ({target - start} : Set Point)
      omega m).2 ⟨m, le_rfl, by simp [zeroClock], by simpa using hmRelative⟩
  exact hle.trans_lt (WithTop.coe_lt_top m)

/-- Atom of paths making exactly `k` visits to `target` before the next
boundary hit.  For a positive atom, the first-hit Bernoulli event is followed
by the regenerative positive-geometric atom in target-relative coordinates.
-/
def boundaryVisitAtom
    (boundary : Set Point) (target start : Point) : ℕ → Set StepPath
  | 0 => (boundaryHitSteps boundary target start)ᶜ
  | k + 1 => boundaryHitSteps boundary target start ∩
      postWithTopStoppingSteps (targetHitTime start target) ⁻¹'
        positiveVisitAtom (relativeBoundary boundary target) (k + 1)

theorem measurableSet_boundaryVisitAtom
    (boundary : Set Point) (target start : Point) :
    ∀ k, MeasurableSet (boundaryVisitAtom boundary target start k) := by
  intro k
  cases k with
  | zero => exact (measurableSet_boundaryHitSteps boundary target start).compl
  | succ k =>
      exact (measurableSet_boundaryHitSteps boundary target start).inter
        ((measurableSet_positiveVisitAtom
          (relativeBoundary boundary target) (k + 1)).preimage
            (measurable_postWithTopStoppingSteps
              (isStoppingTime_targetHitTime start target)))

theorem measure_boundaryVisitAtom_succ
    (boundary : Set Point) (target start : Point) (k : ℕ) :
    fairSteps (boundaryVisitAtom boundary target start (k + 1)) =
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveVisitAtom
          (relativeBoundary boundary target) (k + 1)) := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_targetHitTime start target)
    (isMeasurableAtWithTopStopping_boundaryHitSteps boundary target start)
    (measurableSet_positiveVisitAtom (relativeBoundary boundary target) (k + 1))
  have hfinite : boundaryHitSteps boundary target start ∩
      {omega | targetHitTime start target omega < ⊤} =
        boundaryHitSteps boundary target start := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega,
      boundaryHitSteps_subset_targetHitTime_finite boundary target start homega⟩
  rw [hfinite] at hmarkov
  simpa only [boundaryVisitAtom] using hmarkov

/-- Exact Bernoulli--positive-geometric law for one literal
boundary-stopped excursion. -/
theorem measureReal_boundaryVisitAtom_eq_visitMass
    (boundary : Set Point) (target start : Point) (k : ℕ) :
    fairSteps.real (boundaryVisitAtom boundary target start k) =
      AppendixLocalTime.visitMass
        (boundaryStoppedHitKernel boundary target start)
        (escapeBeforePositiveReturnProbability
          (relativeBoundary boundary target)) k := by
  cases k with
  | zero =>
      have hcompl := probReal_compl_eq_one_sub
        (μ := fairSteps) (measurableSet_boundaryHitSteps boundary target start)
      rw [boundaryVisitAtom, hcompl, AppendixLocalTime.visitMass_zero]
      simpa only [measureReal_def] using congrArg (fun z : ℝ ↦ 1 - z)
        (fairSteps_boundaryHitSteps_toReal boundary target start)
  | succ k =>
      have hpositive :=
        BoundaryVisitRegeneration.measureReal_positiveVisitAtom
          (relativeBoundary boundary target) k
      change (fairSteps
        (positiveVisitAtom (relativeBoundary boundary target) (k + 1))).toReal =
          escapeBeforePositiveReturnProbability (relativeBoundary boundary target) *
            (1 - escapeBeforePositiveReturnProbability
              (relativeBoundary boundary target)) ^ k at hpositive
      rw [measureReal_def, measure_boundaryVisitAtom_succ,
        ENNReal.toReal_mul, hpositive,
        fairSteps_boundaryHitSteps_toReal,
        AppendixLocalTime.visitMass_succ_formula]
      ring

end

end Erdos1165.BoundaryVisitLaw
