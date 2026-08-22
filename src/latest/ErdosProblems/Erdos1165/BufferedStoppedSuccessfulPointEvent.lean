/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms
import ErdosProblems.Erdos1165.AnnularRadialSequentialUpperFamily
import ErdosProblems.Erdos1165.BufferedSuccessfulProfile

/-!
# Stopped successful-point events with a three-scale profile buffer

This file partitions the stopped buffered-success event by the exact
internal excursion profile.  Unlike an ordinary successful-point event, the
coordinates in the erased interval are unrestricted.  Keeping them as exact
profile coordinates in the partition permits the fixed-profile sequential
upper bound to be applied before those coordinates are summed out.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.BufferedStoppedSuccessfulPointEvent

noncomputable section

open AppendixFirstMoment Proposition13Assembly
open AnnularProfileLiteralAtoms BufferedSuccessfulProfile
open AnnularRadialProfileWords
open AnnularRadialSequentialUpperFamily
open TerminalNegativeBinomialWindow

/-- The retained-coordinate conditions on an exact internal profile. -/
def IsBufferedInternalProfile {n : ℕ} (low high : ℕ) (delta : ℝ)
    (m : Profile n) : Prop :=
  ∀ i : Fin (n - 1), RetainedCoordinate low high (scaleIndex i) →
    |(m i : ℝ) - 2 * (scaleIndex i : ℝ) ^ 2| ≤
      (scaleIndex i : ℝ) ^ (1 + delta)

lemma isBufferedSuccessfulProfile_of_fixedSuccessfulProfile
    {n low high : ℕ} {delta : ℝ} {m : Profile n}
    {N : Fin (n + 2) → ℕ}
    (hfixed : FixedSuccessfulProfile n delta m N)
    (hm : IsBufferedInternalProfile low high delta m) :
    IsBufferedSuccessfulProfile n low high delta N := by
  refine ⟨fun _ ↦ hfixed.1, ?_, hfixed.2.2⟩
  intro k hk2 hkn hkretained
  let i : Fin (n - 1) := ⟨k.1 - 2, by omega⟩
  have hscale : scaleIndex i = k.1 := by
    dsimp only [i, scaleIndex]
    omega
  have hentry : N k = m i := by
    have := hfixed.2.1 i
    simpa only [hscale, Fin.eta] using this
  rw [hentry, ← hscale]
  exact hm i (by simpa only [hscale] using hkretained)

lemma fixedSuccessfulProfile_internalProfile_of_buffered
    {n low high : ℕ} {delta : ℝ} {N : Fin (n + 2) → ℕ}
    (hlow : 1 ≤ low)
    (hN : IsBufferedSuccessfulProfile n low high delta N) :
    FixedSuccessfulProfile n delta (internalProfile N) N := by
  refine ⟨hN.1 hlow, fun _ ↦ rfl, hN.2.2⟩

lemma internalProfile_isBuffered
    {n low high : ℕ} {delta : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : IsBufferedSuccessfulProfile n low high delta N) :
    IsBufferedInternalProfile low high delta (internalProfile N) := by
  intro i hiretained
  have hiLower : 2 ≤ scaleIndex i := by simp [scaleIndex]
  have hiUpper : scaleIndex i ≤ n := by
    unfold scaleIndex
    omega
  simpa only [internalProfile_apply] using
    hN.2.1 ⟨scaleIndex i, by
      unfold scaleIndex
      omega⟩ hiLower hiUpper hiretained

/-- The measurable stopped event obtained by allowing arbitrary internal
profile coordinates in the erased interval. -/
def stoppedBufferedSuccessfulPointEvent
    (start scale low high : ℕ) (profileDelta : ℝ) (x : Point) : Set StepPath :=
  ⋃ m : {m : Profile scale //
      IsBufferedInternalProfile low high profileDelta m},
    stoppedFixedProfileEvent start scale profileDelta x m.1

lemma measurableSet_stoppedBufferedSuccessfulPointEvent
    (start scale low high : ℕ) (profileDelta : ℝ) (x : Point) :
    MeasurableSet
      (stoppedBufferedSuccessfulPointEvent start scale low high profileDelta x) := by
  exact MeasurableSet.iUnion fun m ↦
    measurableSet_stoppedFixedProfileEvent start scale profileDelta x m.1

theorem mem_stoppedBufferedSuccessfulPointEvent_iff
    {start scale low high : ℕ} {profileDelta : ℝ} {x : Point}
    (hlow : 1 ≤ low) (omega : StepPath) :
    omega ∈ stoppedBufferedSuccessfulPointEvent
        start scale low high profileDelta x ↔
      ∃ horizon : ℕ,
        ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
          BufferedSuccessfulPoint
            (shiftedWalk start omega) scale low high horizon profileDelta x := by
  constructor
  · intro homega
    obtain ⟨m, hm⟩ := mem_iUnion.mp homega
    obtain ⟨horizon, hexit, hx, hfixed⟩ := mem_iUnion.mp hm
    exact ⟨horizon, hexit, hx,
      isBufferedSuccessfulProfile_of_fixedSuccessfulProfile hfixed m.2⟩
  · rintro ⟨horizon, hexit, hx, hbuffered⟩
    let N := ThickPoint.excursionProfile
      (shiftedWalk start omega) scale horizon x
    let m := internalProfile N
    apply mem_iUnion.mpr
    refine ⟨⟨m, internalProfile_isBuffered hbuffered⟩, ?_⟩
    exact mem_iUnion.mpr ⟨horizon, hexit, hx,
      fixedSuccessfulProfile_internalProfile_of_buffered hlow hbuffered⟩

theorem stoppedSuccessfulPointEvent_subset_stoppedBuffered
    {start scale low high : ℕ} {profileDelta : ℝ} {x : Point}
    (hlow : 1 ≤ low) :
    stoppedSuccessfulPointEvent start scale profileDelta x ⊆
      stoppedBufferedSuccessfulPointEvent
        start scale low high profileDelta x := by
  intro omega homega
  obtain ⟨horizon, hexit, hx, hsuccessful⟩ := homega
  rw [mem_stoppedBufferedSuccessfulPointEvent_iff hlow]
  exact ⟨horizon, hexit, hx,
    of_successfulProfile hsuccessful⟩

/-- Countable subadditivity transfers any exact-profile row bound to the
buffered stopped event. -/
theorem fairSteps_stoppedBufferedSuccessfulPointEvent_le_tsum
    {start scale low high : ℕ} {profileDelta : ℝ} {x : Point}
    (cost : Profile scale → ℝ≥0∞)
    (hcost : ∀ m : Profile scale,
      IsBufferedInternalProfile low high profileDelta m →
        fairSteps (stoppedFixedProfileEvent
          start scale profileDelta x m) ≤ cost m) :
    fairSteps (stoppedBufferedSuccessfulPointEvent
        start scale low high profileDelta x) ≤
      ∑' m : {m : Profile scale //
          IsBufferedInternalProfile low high profileDelta m}, cost m.1 := by
  unfold stoppedBufferedSuccessfulPointEvent
  calc
    fairSteps (⋃ m : {m : Profile scale //
        IsBufferedInternalProfile low high profileDelta m},
      stoppedFixedProfileEvent start scale profileDelta x m.1) ≤
        ∑' m : {m : Profile scale //
            IsBufferedInternalProfile low high profileDelta m},
          fairSteps (stoppedFixedProfileEvent
            start scale profileDelta x m.1) :=
      measure_iUnion_le (μ := fairSteps) _
    _ ≤ ∑' m : {m : Profile scale //
          IsBufferedInternalProfile low high profileDelta m}, cost m.1 := by
      exact ENNReal.tsum_le_tsum fun m ↦ hcost m.1 m.2

/-- The chronological radial-word estimate, summed over all exact profiles
compatible with the retained buffered coordinates. -/
theorem eventually_fairSteps_stoppedBufferedSuccessfulPointEvent_le_exactCostTsum :
    ∀ᶠ scale : ℕ in Filter.atTop, ∀ (hscale : 2 ≤ scale)
      (start low high : ℕ) (profileDelta : ℝ) (x : Point),
      0 < ThickPoint.terminalLower scale profileDelta →
      fairSteps (stoppedBufferedSuccessfulPointEvent
          start scale low high profileDelta x) ≤
        ∑' m : {m : Profile scale //
            IsBufferedInternalProfile low high profileDelta m},
          ENNReal.ofReal
            ((1 + 1 / (scale : ℝ) ^ 4) ^
                exactProfileRadialWordMaxTransitions m.1 *
              (firstProfileTransitionMass hscale m.1 *
                TerminalNegativeBinomialWindow.terminalWindowMass
                  scale profileDelta (terminalProfileCount hscale m.1) *
                profileWeight m.1)) := by
  filter_upwards
      [eventually_fairSteps_stoppedFixedProfileEvent_le_exact_profile_cost]
      with scale hrow
  intro hscale start low high profileDelta x hlower
  apply fairSteps_stoppedBufferedSuccessfulPointEvent_le_tsum
    (fun m ↦ ENNReal.ofReal
      ((1 + 1 / (scale : ℝ) ^ 4) ^
          exactProfileRadialWordMaxTransitions m *
        (firstProfileTransitionMass hscale m *
          terminalWindowMass scale profileDelta
            (terminalProfileCount hscale m) * profileWeight m)))
  intro m _hm
  rw [fairSteps_stoppedFixedProfileEvent_eq_zero]
  exact hrow hscale profileDelta x m hlower

end

end Erdos1165.BufferedStoppedSuccessfulPointEvent
