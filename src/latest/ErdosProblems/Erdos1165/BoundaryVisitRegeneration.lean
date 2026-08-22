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

import ErdosProblems.Erdos1165.SequentialStoppedAtoms
import ErdosProblems.Erdos1165.AppendixLocalTime

/-!
# Regeneration of visits before a boundary hit

Starting at the target (the origin in relative coordinates), let `rho` be
the first strictly positive return time.  A trial succeeds when `rho` occurs
before the path has visited the killing boundary.  Strong Markov at `rho`
then makes successive trials independent.  The recursively defined atoms
below are therefore exactly the positive-geometric visit atoms.

This is the regenerative core of the Bernoulli--geometric terminal-excursion
law.  A separate first-hit factor supplies the Bernoulli parameter when the
annular entrance is not the target.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.BoundaryVisitRegeneration

open TerminalExcursionBridge

noncomputable section

/-- The deterministic zero clock, as a `WithTop`-valued stopping time. -/
def zeroClock : StepPath → WithTop ℕ := fun _ ↦ 0

theorem isStoppingTime_zeroClock :
    IsStoppingTime incrementFiltration zeroClock := by
  intro n
  have hu : MeasurableSet[incrementFiltration n]
      (Set.univ : Set StepPath) := MeasurableSet.univ
  simpa only [zeroClock, zero_le, Set.ofPred_true] using hu

/-- First strictly positive return to the origin. -/
noncomputable def firstPositiveReturnTime : StepPath → WithTop ℕ :=
  firstHitSetAfter (stoppingTimeSucc zeroClock) ({0} : Set Point)

theorem isStoppingTime_firstPositiveReturnTime :
    IsStoppingTime incrementFiltration firstPositiveReturnTime :=
  isStoppingTime_firstHitSetAfter (isStoppingTime_succ isStoppingTime_zeroClock) _

/-- Avoid `boundary` at every time strictly before `n`. -/
def avoidsBoundaryBefore (boundary : Set Point) (n : ℕ) : Set StepPath :=
  {omega | ∀ k < n, trajectory omega k ∉ boundary}

theorem measurableSet_avoidsBoundaryBefore_filtration
    (boundary : Set Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n] (avoidsBoundaryBefore boundary n) := by
  have heq : avoidsBoundaryBefore boundary n =
      ⋂ k : Fin n, {omega : StepPath | trajectory omega k ∉ boundary} := by
    ext omega
    simp only [avoidsBoundaryBefore, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h k
      exact h k k.isLt
    · intro h k hk
      exact h ⟨k, hk⟩
  rw [heq]
  exact MeasurableSet.iInter fun k ↦
    (incrementFiltration.mono (Nat.le_of_lt k.isLt) _
      (measurableSet_trajectory_mem_incrementFiltration k boundary)).compl

theorem measurableSet_avoidsBoundaryBefore
    (boundary : Set Point) (n : ℕ) :
    MeasurableSet (avoidsBoundaryBefore boundary n) :=
  incrementFiltration.le n _
    (measurableSet_avoidsBoundaryBefore_filtration boundary n)

/-- The first positive return occurs before any visit to `boundary`.
Writing the event as a union over the return-time atom makes both ordinary
and stopped measurability explicit. -/
def positiveReturnBeforeBoundary (boundary : Set Point) : Set StepPath :=
  ⋃ n : ℕ, {omega | firstPositiveReturnTime omega = (n : WithTop ℕ)} ∩
    avoidsBoundaryBefore boundary n

theorem measurableSet_positiveReturnBeforeBoundary (boundary : Set Point) :
    MeasurableSet (positiveReturnBeforeBoundary boundary) := by
  exact MeasurableSet.iUnion fun n ↦
    (incrementFiltration.le n _
      (isStoppingTime_firstPositiveReturnTime.measurableSet_eq n)).inter
        (measurableSet_avoidsBoundaryBefore boundary n)

theorem positiveReturnBeforeBoundary_subset_finite (boundary : Set Point) :
    positiveReturnBeforeBoundary boundary ⊆
      {omega | firstPositiveReturnTime omega < ⊤} := by
  intro omega homega
  obtain ⟨n, hn, _⟩ := Set.mem_iUnion.mp homega
  change firstPositiveReturnTime omega < ⊤
  change firstPositiveReturnTime omega = (n : WithTop ℕ) at hn
  rw [hn]
  exact WithTop.coe_lt_top n

/-- The return-before-boundary event belongs to the stopped sigma algebra at
the first positive return time. -/
theorem isMeasurableAtWithTopStopping_positiveReturnBeforeBoundary
    (boundary : Set Point) :
    IsMeasurableAtWithTopStopping firstPositiveReturnTime
      (positiveReturnBeforeBoundary boundary) := by
  intro n
  have heq : positiveReturnBeforeBoundary boundary ∩
      {omega | firstPositiveReturnTime omega = (n : WithTop ℕ)} =
      {omega | firstPositiveReturnTime omega = (n : WithTop ℕ)} ∩
        avoidsBoundaryBefore boundary n := by
    ext omega
    simp only [positiveReturnBeforeBoundary, mem_inter_iff, mem_iUnion,
      mem_ofPred_eq]
    constructor
    · rintro ⟨⟨m, hm, hav⟩, hn⟩
      have hmn : m = n := WithTop.coe_eq_coe.mp (hm.symm.trans hn)
      subst m
      exact ⟨hn, hav⟩
    · rintro ⟨hn, hav⟩
      exact ⟨⟨n, hn, hav⟩, hn⟩
  rw [heq]
  exact (isStoppingTime_firstPositiveReturnTime.measurableSet_eq n).inter
    (measurableSet_avoidsBoundaryBefore_filtration boundary n)

/-- Regenerative atoms for a positive number of visits to the target before
the boundary.  Atom `1` is escape before a positive return.  Atom `k+2`
first makes a return-before-boundary trial and then realizes atom `k+1` in
the fresh tail after that return. -/
def positiveVisitAtom (boundary : Set Point) : ℕ → Set StepPath
  | 0 => ∅
  | 1 => (positiveReturnBeforeBoundary boundary)ᶜ
  | k + 2 => positiveReturnBeforeBoundary boundary ∩
      postWithTopStoppingSteps firstPositiveReturnTime ⁻¹'
        positiveVisitAtom boundary (k + 1)

@[simp] theorem positiveVisitAtom_zero (boundary : Set Point) :
    positiveVisitAtom boundary 0 = ∅ := rfl

@[simp] theorem positiveVisitAtom_one (boundary : Set Point) :
    positiveVisitAtom boundary 1 =
      (positiveReturnBeforeBoundary boundary)ᶜ := rfl

theorem positiveVisitAtom_succ_succ (boundary : Set Point) (k : ℕ) :
    positiveVisitAtom boundary (k + 2) =
      positiveReturnBeforeBoundary boundary ∩
        postWithTopStoppingSteps firstPositiveReturnTime ⁻¹'
          positiveVisitAtom boundary (k + 1) := rfl

theorem measurableSet_positiveVisitAtom (boundary : Set Point) :
    ∀ k, MeasurableSet (positiveVisitAtom boundary k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => exact (measurableSet_positiveReturnBeforeBoundary boundary).compl
  | more k _ ih =>
      rw [positiveVisitAtom_succ_succ]
      exact (measurableSet_positiveReturnBeforeBoundary boundary).inter
        (ih.preimage
          (measurable_postWithTopStoppingSteps
            isStoppingTime_firstPositiveReturnTime))

/-- One regeneration step factors exactly. -/
theorem measure_positiveVisitAtom_succ_succ
    (boundary : Set Point) (k : ℕ) :
    fairSteps (positiveVisitAtom boundary (k + 2)) =
      fairSteps (positiveReturnBeforeBoundary boundary) *
        fairSteps (positiveVisitAtom boundary (k + 1)) := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    isStoppingTime_firstPositiveReturnTime
    (isMeasurableAtWithTopStopping_positiveReturnBeforeBoundary boundary)
    (measurableSet_positiveVisitAtom boundary (k + 1))
  have hfinite : positiveReturnBeforeBoundary boundary ∩
      {omega | firstPositiveReturnTime omega < ⊤} =
      positiveReturnBeforeBoundary boundary := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega,
      positiveReturnBeforeBoundary_subset_finite boundary homega⟩
  rw [hfinite] at hmarkov
  simpa only [positiveVisitAtom_succ_succ] using hmarkov

/-- Escape probability for one target-to-boundary trial. -/
def escapeBeforePositiveReturnProbability (boundary : Set Point) : ℝ :=
  1 - fairSteps.real (positiveReturnBeforeBoundary boundary)

theorem escapeBeforePositiveReturnProbability_nonneg (boundary : Set Point) :
    0 ≤ escapeBeforePositiveReturnProbability boundary := by
  unfold escapeBeforePositiveReturnProbability
  exact sub_nonneg.mpr measureReal_le_one

theorem one_sub_escapeBeforePositiveReturnProbability (boundary : Set Point) :
    1 - escapeBeforePositiveReturnProbability boundary =
      fairSteps.real (positiveReturnBeforeBoundary boundary) := by
  unfold escapeBeforePositiveReturnProbability
  ring

/-- The regenerative atoms have the exact positive-geometric masses. -/
theorem measureReal_positiveVisitAtom (boundary : Set Point) (k : ℕ) :
    fairSteps.real (positiveVisitAtom boundary (k + 1)) =
      escapeBeforePositiveReturnProbability boundary *
        (1 - escapeBeforePositiveReturnProbability boundary) ^ k := by
  induction k with
  | zero =>
      rw [positiveVisitAtom_one,
        probReal_compl_eq_one_sub
          (measurableSet_positiveReturnBeforeBoundary boundary)]
      simp only [pow_zero, mul_one]
      rfl
  | succ k ih =>
      have hmeasure := congrArg ENNReal.toReal
        (measure_positiveVisitAtom_succ_succ boundary k)
      rw [ENNReal.toReal_mul] at hmeasure
      change fairSteps.real (positiveVisitAtom boundary (k + 2)) =
        fairSteps.real (positiveReturnBeforeBoundary boundary) *
          fairSteps.real (positiveVisitAtom boundary (k + 1)) at hmeasure
      rw [show k + 1 + 1 = k + 2 by omega, hmeasure, ih,
        one_sub_escapeBeforePositiveReturnProbability]
      ring

/-- Identification with the positive part of `AppendixLocalTime.visitMass`.
This is the geometric factor used after a terminal excursion has first hit
its centre. -/
theorem measureReal_positiveVisitAtom_eq_visitMass_one
    (boundary : Set Point) (k : ℕ) :
    fairSteps.real (positiveVisitAtom boundary (k + 1)) =
      AppendixLocalTime.visitMass 1
        (escapeBeforePositiveReturnProbability boundary) (k + 1) := by
  rw [measureReal_positiveVisitAtom,
    AppendixLocalTime.visitMass_succ_formula]
  ring

end

end Erdos1165.BoundaryVisitRegeneration
