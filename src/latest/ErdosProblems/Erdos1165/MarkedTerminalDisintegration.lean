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

/-!
# Marked stopped-data disintegration for the terminal excursions

Conditioning a successful point only on its terminal entrance vector is not
valid: the future excursion profile and the global exit event also see the
outer endpoints of the omitted inner-to-outer pieces.  This file keeps those
endpoints as marks and leaves the complete complementary skeleton as an
arbitrary nonnegative weight.

For coordinate `j`, `skeletonKernel j u z` is the mass of the unmarked bridge
from entrance `u` to exit mark `z`, while `markedKernel j u k z` is the joint
mass of making exactly `k` visits and exiting at `z`.  The only local input is
the honest marked comparison

`loss j * referenceMass j k * skeletonKernel j u z ≤ markedKernel j u k z`.

The theorem below sums this inequality over every entrance vector, exit
vector, and visit vector without altering the skeleton weight.  Thus the
weight may encode the exact outer-exit horizon, the entire multiscale profile,
and all future constraints.  No event is asserted measurable at the first
inner entrance and no coarse conditional product law is used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.MarkedTerminalDisintegration

noncomputable section

/-! ## Marked kernels and complete skeleton weights -/

/-- Pointwise comparison of the joint visit-count/exit-mark kernel with an
unmarked skeleton kernel and an entrance-independent reference visit law. -/
def MarkedKernelLower
    {Entrance Exit : Type*} {m : ℕ}
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞) : Prop :=
  ∀ j u k z,
    loss j * referenceMass j k * skeletonKernel j u z ≤
      markedKernel j u k z

/-- Product of the unmarked bridge masses along a fixed complementary
skeleton. -/
def skeletonProduct
    {Entrance Exit : Type*} {m : ℕ}
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (entrance : Fin m → Entrance) (exit : Fin m → Exit) : ℝ≥0∞ :=
  ∏ j, skeletonKernel j (entrance j) (exit j)

/-- Product of the joint marked bridge masses along a fixed skeleton and a
fixed terminal visit vector. -/
def markedProduct
    {Entrance Exit : Type*} {m : ℕ}
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (entrance : Fin m → Entrance) (exit : Fin m → Exit)
    (visits : Fin m → ℕ) : ℝ≥0∞ :=
  ∏ j, markedKernel j (entrance j) (visits j) (exit j)

/-- Product mass of the entrance-independent reference visit vector. -/
def referenceProduct {m : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visits : Fin m → ℕ) : ℝ≥0∞ :=
  ∏ j, referenceMass j (visits j)

/-- Reference product restricted to a visit-vector event. -/
def restrictedReferenceProduct {m : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ)) (visits : Fin m → ℕ) : ℝ≥0∞ := by
  classical
  exact if visits ∈ visitEvent then referenceProduct referenceMass visits else 0

/-- Reference probability mass of an arbitrary terminal visit-vector event.
This is a `tsum`, since visit counts are unbounded. -/
def referenceEventMass {m : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ)) : ℝ≥0∞ := by
  classical
  exact ∑' visits, restrictedReferenceProduct referenceMass visitEvent visits

/-- Marked path product restricted to a visit-vector event. -/
def restrictedMarkedProduct
    {Entrance Exit : Type*} {m : ℕ}
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (weight : ℝ≥0∞) (entrance : Fin m → Entrance) (exit : Fin m → Exit)
    (visits : Fin m → ℕ) : ℝ≥0∞ := by
  classical
  exact if visits ∈ visitEvent then
    weight * markedProduct markedKernel entrance exit visits else 0

/-- Mass of the successful complementary skeleton.  `skeletonWeight` is
deliberately arbitrary: it retains all future/profile constraints and all
dependence between the exposed entrance and exit endpoint vectors. -/
def successfulSkeletonMass
    {Data Entrance Exit : Type*} {m : ℕ}
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' data, ∑' entrance, ∑' exit,
    skeletonWeight data entrance exit *
      skeletonProduct skeletonKernel entrance exit

/-- Mass obtained by inserting marked terminal pieces and retaining only the
desired terminal visit vectors. -/
def markedVisitEventMass
    {Data Entrance Exit : Type*} {m : ℕ}
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ)) : ℝ≥0∞ := by
  classical
  exact ∑' data, ∑' entrance, ∑' exit, ∑' visits,
    restrictedMarkedProduct markedKernel visitEvent
      (skeletonWeight data entrance exit) entrance exit visits

/-- Exact event-level bookkeeping for a complete stopped skeleton.  The
successful event is decomposed exactly into unmarked bridge atoms.  The
marked sum only has to be a lower subevent of `terminalEvent`; this is the
direction supplied by the pathwise selected-visit containment theorem. -/
structure MarkedStoppedDataLowerDecomposition
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega] {m : ℕ}
    (mu : Measure Omega) (successful terminalEvent : Set Omega)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ)) : Prop where
  successful_eq :
    mu successful = successfulSkeletonMass skeletonWeight skeletonKernel
  marked_le_terminal :
    markedVisitEventMass skeletonWeight markedKernel visitEvent ≤
      mu terminalEvent

/-! ## Finite-product marked comparison -/

theorem loss_reference_skeleton_le_markedProduct
    {Entrance Exit : Type*} {m : ℕ}
    {loss : Fin m → ℝ≥0∞}
    {referenceMass : Fin m → ℕ → ℝ≥0∞}
    {skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞}
    {markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞}
    (hlower : MarkedKernelLower loss referenceMass skeletonKernel markedKernel)
    (entrance : Fin m → Entrance) (exit : Fin m → Exit)
    (visits : Fin m → ℕ) :
    (∏ j, loss j) * referenceProduct referenceMass visits *
        skeletonProduct skeletonKernel entrance exit ≤
      markedProduct markedKernel entrance exit visits := by
  rw [referenceProduct, skeletonProduct, markedProduct]
  calc
    (∏ j, loss j) * (∏ j, referenceMass j (visits j)) *
          ∏ j, skeletonKernel j (entrance j) (exit j) =
        ∏ j, (loss j * referenceMass j (visits j) *
          skeletonKernel j (entrance j) (exit j)) := by
            simp only [Finset.prod_mul_distrib]
    _ ≤ ∏ j, markedKernel j (entrance j) (visits j) (exit j) :=
      Finset.prod_le_prod' fun j _hj ↦
        hlower j (entrance j) (visits j) (exit j)

private theorem fixedSkeleton_marked_lower
    {Entrance Exit : Type*} {m : ℕ}
    {loss : Fin m → ℝ≥0∞}
    {referenceMass : Fin m → ℕ → ℝ≥0∞}
    {skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞}
    {markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞}
    (hlower : MarkedKernelLower loss referenceMass skeletonKernel markedKernel)
    (visitEvent : Set (Fin m → ℕ))
    (weight : ℝ≥0∞) (entrance : Fin m → Entrance) (exit : Fin m → Exit) :
    (∏ j, loss j) * referenceEventMass referenceMass visitEvent *
        (weight * skeletonProduct skeletonKernel entrance exit) ≤
      ∑' visits, restrictedMarkedProduct markedKernel visitEvent
        weight entrance exit visits := by
  classical
  rw [referenceEventMass, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro visits
  by_cases hvisits : visits ∈ visitEvent
  · rw [restrictedReferenceProduct, restrictedMarkedProduct,
      if_pos hvisits, if_pos hvisits]
    have hproduct := loss_reference_skeleton_le_markedProduct
      hlower entrance exit visits
    calc
      (∏ j, loss j) * referenceProduct referenceMass visits *
          (weight * skeletonProduct skeletonKernel entrance exit) =
        weight * ((∏ j, loss j) * referenceProduct referenceMass visits *
          skeletonProduct skeletonKernel entrance exit) := by ac_rfl
      _ ≤ weight * markedProduct markedKernel entrance exit visits :=
        mul_le_mul le_rfl hproduct bot_le bot_le
  · rw [restrictedReferenceProduct, restrictedMarkedProduct,
      if_neg hvisits, if_neg hvisits]
    simp

/-! ## Summation over the full stopped skeleton -/

/-- The marked comparison survives summation over an arbitrary nonnegative
complementary-skeleton weight.  This is the backward-disintegration step
needed in Appendix A.7: all future and profile dependence remains inside
`skeletonWeight`. -/
theorem markedVisitEventMass_lower
    {Data Entrance Exit : Type*} {m : ℕ}
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hlower : MarkedKernelLower loss referenceMass skeletonKernel markedKernel) :
    (∏ j, loss j) * referenceEventMass referenceMass visitEvent *
        successfulSkeletonMass skeletonWeight skeletonKernel ≤
      markedVisitEventMass skeletonWeight markedKernel visitEvent := by
  rw [successfulSkeletonMass, markedVisitEventMass,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro data
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro entrance
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro exit
  exact fixedSkeleton_marked_lower hlower visitEvent
    (skeletonWeight data entrance exit) entrance exit

/-! ## Identification of the iid reference mass -/

theorem iidVisitMeasure_singleton
    (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (visits : Fin m → ℕ) :
    AppendixLocalTime.iidVisitMeasure m q p hq0 hq1 hp0 hp1 {visits} =
      referenceProduct
        (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
        visits := by
  rw [AppendixLocalTime.iidVisitMeasure, Measure.pi_singleton,
    referenceProduct]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact AppendixLocalTime.visitLaw_apply q p hq0 hq1 hp0 hp1 (visits j)

private theorem measure_eq_tsum_singletons_of_countable
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (mu : Measure α) (s : Set α) :
    mu s = ∑' x : s, mu {x.1} := by
  symm
  simpa only [preimage_id] using
    (MeasureTheory.tsum_measure_preimage_singleton (μ := mu) (f := id)
      (Set.to_countable s) (fun _ _ ↦ measurableSet_singleton _))

/-- `referenceEventMass` is exactly the canonical iid
Bernoulli--positive-geometric product measure on any visit-vector event. -/
theorem referenceEventMass_visitMass_eq_iidVisitMeasure
    (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (visitEvent : Set (Fin m → ℕ)) :
    referenceEventMass
        (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
        visitEvent =
      AppendixLocalTime.iidVisitMeasure m q p hq0 hq1 hp0 hp1 visitEvent := by
  let mu := AppendixLocalTime.iidVisitMeasure m q p hq0 hq1 hp0 hp1
  calc
    referenceEventMass
        (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
        visitEvent =
        ∑' visits : visitEvent,
          referenceProduct
            (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
            visits.1 := by
              rw [referenceEventMass, tsum_subtype]
              congr 1
    _ = ∑' visits : visitEvent, mu {visits.1} := by
      congr 1
      funext visits
      exact (iidVisitMeasure_singleton m q p hq0 hq1 hp0 hp1 visits.1).symm
    _ = mu visitEvent :=
      (measure_eq_tsum_singletons_of_countable mu visitEvent).symm

/-- Product of a constant `ofReal (1-eta)` loss over `m` coordinates. -/
theorem toReal_prod_const_one_sub
    (m : ℕ) (eta : ℝ) (_heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (∏ _ : Fin m, ENNReal.ofReal (1 - eta)).toReal = (1 - eta) ^ m := by
  rw [ENNReal.toReal_prod]
  simp [ENNReal.toReal_ofReal (sub_nonneg.mpr heta1)]

/-- Event-level stopped-data conclusion.  Unlike an entrance-only
conditional-product interface, this theorem remains valid when `successful`
depends on the whole future profile and on every outer exit endpoint. -/
theorem event_lower_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {m : ℕ} (mu : Measure Omega) (successful terminalEvent : Set Omega)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hlower : MarkedKernelLower loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataLowerDecomposition mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel visitEvent) :
    ((∏ j, loss j) * referenceEventMass referenceMass visitEvent) *
        mu successful ≤ mu terminalEvent := by
  rw [hdecompose.successful_eq]
  exact (markedVisitEventMass_lower loss referenceMass skeletonWeight
    skeletonKernel markedKernel visitEvent hlower).trans
      hdecompose.marked_le_terminal

/-- Real-probability form of `event_lower_of_markedStoppedData`. -/
theorem event_real_lower_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {m : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful terminalEvent : Set Omega)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hlower : MarkedKernelLower loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataLowerDecomposition mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel visitEvent) :
    (((∏ j, loss j) * referenceEventMass referenceMass visitEvent).toReal) *
        mu.real successful ≤ mu.real terminalEvent := by
  have h := event_lower_of_markedStoppedData mu successful terminalEvent loss
    referenceMass skeletonWeight skeletonKernel markedKernel visitEvent hlower
    hdecompose
  have hreal := ENNReal.toReal_mono (measure_ne_top mu terminalEvent) h
  simpa only [Measure.real, ENNReal.toReal_mul] using hreal

/-- Constant-loss specialization with the exact iid
Bernoulli--positive-geometric reference law. -/
theorem event_real_lower_of_constant_visitLaw
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {m : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful terminalEvent : Set Omega)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hlower : MarkedKernelLower
      (fun _ ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataLowerDecomposition mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel visitEvent) :
    ((1 - eta) ^ m *
        (AppendixLocalTime.iidVisitMeasure m q p hq0 hq1 hp0 hp1).real
          visitEvent) * mu.real successful ≤ mu.real terminalEvent := by
  have h := event_real_lower_of_markedStoppedData mu successful terminalEvent
    (fun _ : Fin m ↦ ENNReal.ofReal (1 - eta))
    (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
    skeletonWeight skeletonKernel markedKernel visitEvent hlower hdecompose
  rw [ENNReal.toReal_mul,
    toReal_prod_const_one_sub m eta heta0 heta1,
    referenceEventMass_visitMass_eq_iidVisitMeasure
      m q p hq0 hq1 hp0 hp1 visitEvent] at h
  exact h

/-- Exact HLOZ terminal-threshold specialization.  This is the marked
replacement for the entrance-only disintegration premise in Appendix A.7. -/
theorem hlozTerminal_event_real_lower_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful terminalEvent : Set Omega)
    (n : ℕ) (profileDelta thickDelta q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (skeletonWeight : Data →
      (Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → Entrance) →
      (Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) → Exit) → ℝ≥0∞)
    (skeletonKernel :
      Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) →
        Entrance → Exit → ℝ≥0∞)
    (markedKernel :
      Fin (AppendixLocalTime.requiredTerminalCount n profileDelta) →
        Entrance → ℕ → Exit → ℝ≥0∞)
    (hlower : MarkedKernelLower
      (fun _ ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataLowerDecomposition mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel
      {visits | ThickPoint.thickThreshold n thickDelta ≤
        AppendixLocalTime.totalVisits visits}) :
    ((1 - eta) ^ (AppendixLocalTime.requiredTerminalCount n profileDelta) *
      AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        n profileDelta q p hq0 hq1 hp0 hp1 thickDelta) *
        mu.real successful ≤ mu.real terminalEvent := by
  exact event_real_lower_of_constant_visitLaw mu successful terminalEvent
    q p hq0 hq1 hp0 hp1 eta heta0 heta1 skeletonWeight skeletonKernel
    markedKernel
    {visits | ThickPoint.thickThreshold n thickDelta ≤
      AppendixLocalTime.totalVisits visits}
    hlower hdecompose

end

end Erdos1165.MarkedTerminalDisintegration
