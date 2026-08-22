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

import ErdosProblems.Erdos1165.PointBeforeReturn
import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-!
# Spatial recurrence of planar simple random walk

Origin recurrence is upgraded here to simultaneous recurrence at every
lattice point.  A positive-probability excursion from the origin reaches any
fixed nonzero point before returning.  Regeneration at the first return then
shows that avoiding that point forever has probability zero.  Deterministic
tail stationarity upgrades one visit to infinitely many visits.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.SpatialRecurrence

open PointBeforeReturn PlanarPotential

/-- The walk never visits `x`, including at time zero. -/
def avoidsPointForever (x : Point) : Set StepPath :=
  {omega | ∀ n, trajectory omega n ≠ x}

/-- The walk visits `x` infinitely often. -/
def infinitePointVisitEvent (x : Point) : Set StepPath :=
  {omega | ∃ᶠ n in atTop, trajectory omega n = x}

/-- Time `m` is the final visit to `x`. -/
def lastPointVisitEvent (x : Point) (m : ℕ) : Set StepPath :=
  {omega | trajectory omega m = x ∧
    ∀ k, 0 < k → trajectory omega (m + k) ≠ x}

lemma measurableSet_avoidsPointForever (x : Point) :
    MeasurableSet (avoidsPointForever x) := by
  have heq : avoidsPointForever x =
      ⋂ n : ℕ, {omega : StepPath | trajectory omega n = x}ᶜ := by
    ext omega
    simp [avoidsPointForever]
  rw [heq]
  exact MeasurableSet.iInter fun n ↦
    (measurableSet_trajectory_eq_filtration n x |> incrementFiltration.le n _).compl

lemma pointBeforeReturnProbability_pos {x : Point} (hx : x ≠ 0) :
    0 < pointBeforeReturnProbability x := by
  rw [pointBeforeReturnProbability_eq hx]
  exact one_div_pos.mpr (mul_pos (by norm_num) (planarPotentialKernel_pos_of_ne hx))

private def avoidAfterFirstPairZero (x : Point) (k : ℕ) : Set StepPath :=
  firstPairZeroAt x k ∩ shiftSteps k ⁻¹' avoidsPointForever x

private lemma avoidAfterFirstPairZero_pairwiseDisjoint (x : Point) :
    Pairwise fun i j ↦ Disjoint (avoidAfterFirstPairZero x i)
      (avoidAfterFirstPairZero x j) := by
  intro i j hij
  exact (firstPairZeroAt_pairwiseDisjoint x hij).mono inter_subset_left inter_subset_left

private lemma measurableSet_avoidAfterFirstPairZero (x : Point) (k : ℕ) :
    MeasurableSet (avoidAfterFirstPairZero x k) :=
  (measurableSet_firstPairZeroAt x k).inter
    ((measurableSet_avoidsPointForever x).preimage (measurable_shiftSteps k))

private lemma avoidsPointForever_inter_positiveReturnEvent {x : Point} (hx : x ≠ 0) :
    avoidsPointForever x ∩ positiveReturnEvent =
      ⋃ k, avoidAfterFirstPairZero x k := by
  ext omega
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨havoid, n, hn, hnzero⟩
    have hpair := positiveReturnEvent_subset_firstPairEvent x ⟨n, hn, hnzero⟩
    rcases hpair with hzero | htarget
    · obtain ⟨k, hkzero⟩ := mem_iUnion.mp hzero
      refine ⟨k, hkzero, ?_⟩
      intro t ht
      apply havoid (k + t)
      have hadd := trajectory_add_sub_trajectory omega k t
      rw [hkzero.2.1] at hadd
      simpa only [sub_zero] using hadd.trans ht
    · obtain ⟨k, hkx⟩ := mem_iUnion.mp htarget
      exact (havoid k hkx.2.1).elim
  · rintro ⟨k, hkfirst, htail⟩
    refine ⟨?_, ⟨k, hkfirst.1, hkfirst.2.1⟩⟩
    intro n hn
    rcases lt_trichotomy n k with hnk | rfl | hkn
    · by_cases hnzero : n = 0
      · subst n
        apply hx
        exact hn.symm.trans (trajectory_zero omega)
      · exact hkfirst.2.2 n (Nat.pos_of_ne_zero hnzero) hnk |>.2 hn
    · exact hx (hn.symm.trans hkfirst.2.1)
    · let t := n - k
      have htpos : 0 < t := by dsimp [t]; omega
      have htime : k + t = n := by dsimp [t]; omega
      apply htail t
      have hadd := trajectory_add_sub_trajectory omega k t
      rw [hkfirst.2.1, htime] at hadd
      have hshift : trajectory omega n = trajectory (shiftSteps k omega) t := by
        simpa only [sub_zero] using hadd
      exact hshift.symm.trans hn

private lemma measure_avoidAfterFirstPairZero (x : Point) (k : ℕ) :
    fairSteps (avoidAfterFirstPairZero x k) =
      fairSteps (firstPairZeroAt x k) * fairSteps (avoidsPointForever x) := by
  exact strongMarkov_fullTail (isFiniteStoppingTime_const k)
    (isMeasurableAtStopping_firstPairZeroAt_const x k)
    (measurableSet_avoidsPointForever x)

private theorem measure_avoidsPointForever_fixedPoint {x : Point} (hx : x ≠ 0) :
    fairSteps (avoidsPointForever x) =
      fairSteps (firstPairZeroEvent x) * fairSteps (avoidsPointForever x) := by
  have hreturnAE : ∀ᵐ omega ∂fairSteps, omega ∈ positiveReturnEvent := by
    rw [ae_mem_iff_measure_eq measurableSet_positiveReturnEvent.nullMeasurableSet,
      fairSteps_positiveReturnEvent, measure_univ]
  calc
    fairSteps (avoidsPointForever x) =
        fairSteps (avoidsPointForever x ∩ positiveReturnEvent) := by
      rw [inter_comm]
      exact (Measure.measure_inter_eq_of_ae hreturnAE).symm
    _ = fairSteps (⋃ k, avoidAfterFirstPairZero x k) := by
      rw [avoidsPointForever_inter_positiveReturnEvent hx]
    _ = ∑' k, fairSteps (avoidAfterFirstPairZero x k) :=
      measure_iUnion (avoidAfterFirstPairZero_pairwiseDisjoint x)
        (measurableSet_avoidAfterFirstPairZero x)
    _ = ∑' k, fairSteps (firstPairZeroAt x k) *
        fairSteps (avoidsPointForever x) := by
      apply tsum_congr
      intro k
      exact measure_avoidAfterFirstPairZero x k
    _ = (∑' k, fairSteps (firstPairZeroAt x k)) *
        fairSteps (avoidsPointForever x) := ENNReal.tsum_mul_right
    _ = fairSteps (firstPairZeroEvent x) * fairSteps (avoidsPointForever x) := by
      rw [firstPairZeroEvent,
        measure_iUnion (firstPairZeroAt_pairwiseDisjoint x)
          (measurableSet_firstPairZeroAt x)]

/-- Every fixed nonzero point is hit almost surely. -/
theorem fairSteps_avoidsPointForever_eq_zero {x : Point} (hx : x ≠ 0) :
    fairSteps (avoidsPointForever x) = 0 := by
  have heq := congrArg ENNReal.toReal (measure_avoidsPointForever_fixedPoint hx)
  rw [ENNReal.toReal_mul] at heq
  have hmass := firstPairZeroProbability_add_targetProbability hx
  have hp := pointBeforeReturnProbability_pos hx
  have hq : fairSteps.real (firstPairZeroEvent x) < 1 := by
    linarith
  have havoidReal : (fairSteps (avoidsPointForever x)).toReal = 0 := by
    have hnonneg : 0 ≤ (fairSteps (avoidsPointForever x)).toReal := ENNReal.toReal_nonneg
    change (fairSteps (avoidsPointForever x)).toReal =
      fairSteps.real (firstPairZeroEvent x) *
        (fairSteps (avoidsPointForever x)).toReal at heq
    nlinarith
  rcases (ENNReal.toReal_eq_zero_iff _).mp havoidReal with hzero | htop
  · exact hzero
  · exact (measure_ne_top fairSteps (avoidsPointForever x) htop).elim

lemma measurableSet_infinitePointVisitEvent (x : Point) :
    MeasurableSet (infinitePointVisitEvent x) := by
  rw [infinitePointVisitEvent, show
    {omega : StepPath | ∃ᶠ n in atTop, trajectory omega n = x} =
      limsup (fun n ↦ {omega : StepPath | trajectory omega n = x}) atTop by
        ext omega
        simpa only [mem_ofPred_eq] using
          (mem_limsup_iff_frequently_mem
            (s := fun n ↦ {omega : StepPath | trajectory omega n = x})
            (𝓕 := atTop) (a := omega)).symm]
  exact MeasurableSet.measurableSet_limsup fun n ↦
    measurableSet_trajectory_eq_filtration n x |> incrementFiltration.le n _

private lemma not_infinitePointVisitEvent_subset
    (x : Point) :
    (infinitePointVisitEvent x)ᶜ ⊆
      avoidsPointForever x ∪ ⋃ m, lastPointVisitEvent x m := by
  intro omega homega
  have hnot : ¬ ∃ᶠ n in atTop, trajectory omega n = x := by
    simpa [infinitePointVisitEvent] using homega
  have hev : ∀ᶠ n in atTop, trajectory omega n ≠ x :=
    (not_frequently).mp hnot
  by_cases hvisit : ∃ m, trajectory omega m = x
  · obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨m0, hm0⟩ := hvisit
    let M := max N (m0 + 1)
    let R : Finset ℕ := (Finset.range M).filter fun n ↦ trajectory omega n = x
    have hR : R.Nonempty := by
      refine ⟨m0, ?_⟩
      simp [R, M, hm0]
    let m : ℕ := R.max' hR
    have hmR : m ∈ R := Finset.max'_mem R hR
    have hmVisit : trajectory omega m = x := (Finset.mem_filter.mp hmR).2
    right
    refine mem_iUnion.mpr ⟨m, hmVisit, ?_⟩
    intro k hk hmkVisit
    by_cases hmkM : m + k < M
    · have hmkR : m + k ∈ R :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmkM, hmkVisit⟩
      have hle : m + k ≤ m := Finset.le_max' R (m + k) hmkR
      omega
    · have hMN : N ≤ M := le_max_left _ _
      exact hN (m + k) (hMN.trans (Nat.le_of_not_gt hmkM)) hmkVisit
  · left
    exact fun n hn ↦ hvisit ⟨n, hn⟩

private lemma lastPointVisitEvent_subset_shift_noPositiveReturn (x : Point) (m : ℕ) :
    lastPointVisitEvent x m ⊆ shiftSteps m ⁻¹' positiveReturnEventᶜ := by
  intro omega homega
  rw [mem_preimage, mem_compl_iff]
  intro htail
  obtain ⟨k, hk, hkzero⟩ := htail
  apply homega.2 k hk
  have hadd := trajectory_add_sub_trajectory omega m k
  rw [homega.1] at hadd
  have h := congrArg (fun z : Point ↦ z + x) (hadd.trans hkzero)
  rw [sub_add_cancel] at h
  change trajectory omega (m + k) = (0 : Point) + x at h
  simpa only [zero_add] using h

private lemma fairSteps_lastPointVisitEvent_eq_zero (x : Point) (m : ℕ) :
    fairSteps (lastPointVisitEvent x m) = 0 := by
  have hnoReturn : fairSteps positiveReturnEventᶜ = 0 := by
    rw [measure_compl measurableSet_positiveReturnEvent
      (measure_ne_top fairSteps positiveReturnEvent), fairSteps_positiveReturnEvent, measure_univ]
    norm_num
  apply measure_mono_null (lastPointVisitEvent_subset_shift_noPositiveReturn x m)
  rw [← Measure.map_apply (measurable_shiftSteps m)
    measurableSet_positiveReturnEvent.compl, fairSteps_map_shiftSteps, hnoReturn]

private lemma fairSteps_avoidsPointForever_eq_zero_all (x : Point) :
    fairSteps (avoidsPointForever x) = 0 := by
  by_cases hx : x = 0
  · subst x
    have hempty : avoidsPointForever 0 = ∅ := by
      ext omega
      simp only [avoidsPointForever, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact h 0 (trajectory_zero omega)
    rw [hempty, measure_empty]
  · exact fairSteps_avoidsPointForever_eq_zero hx

/-- Planar simple random walk visits every fixed lattice point infinitely
often almost surely. -/
theorem fairSteps_frequently_visits_point (x : Point) :
    ∀ᵐ omega ∂fairSteps, ∃ᶠ n in atTop, trajectory omega n = x := by
  have hcompl : fairSteps (infinitePointVisitEvent x)ᶜ = 0 := by
    apply le_zero_iff.mp
    calc
      fairSteps (infinitePointVisitEvent x)ᶜ ≤
          fairSteps (avoidsPointForever x ∪ ⋃ m, lastPointVisitEvent x m) :=
        measure_mono (not_infinitePointVisitEvent_subset x)
      _ ≤ fairSteps (avoidsPointForever x) +
          fairSteps (⋃ m, lastPointVisitEvent x m) := measure_union_le _ _
      _ = 0 := by
        rw [fairSteps_avoidsPointForever_eq_zero_all,
          measure_iUnion_null (fairSteps_lastPointVisitEvent_eq_zero x)]
        simp
  rw [ae_iff]
  change fairSteps (infinitePointVisitEvent x)ᶜ = 0
  exact hcompl

/-- A single full-measure event on which every lattice point is visited
infinitely often. -/
theorem fairSteps_frequently_visits_every_point :
    ∀ᵐ omega ∂fairSteps, ∀ x : Point,
      ∃ᶠ n in atTop, trajectory omega n = x := by
  exact ae_all_iff.2 fairSteps_frequently_visits_point

/-- Every nonempty set of lattice points is visited arbitrarily late almost
surely. -/
theorem fairSteps_frequently_visits_nonempty_set
    {A : Set Point} (hA : A.Nonempty) :
    ∀ᵐ omega ∂fairSteps, ∃ᶠ n in atTop, trajectory omega n ∈ A := by
  obtain ⟨x, hxA⟩ := hA
  filter_upwards [fairSteps_frequently_visits_point x] with omega homega
  exact homega.mono fun n hn ↦ by simpa only [hn] using hxA

/-- On one full-measure event, every nonempty set of lattice points is
visited arbitrarily late.  This pathwise form permits simultaneous use for
any finite family of annular boundaries. -/
theorem fairSteps_frequently_visits_every_nonempty_set :
    ∀ᵐ omega ∂fairSteps, ∀ A : Set Point, A.Nonempty →
      ∃ᶠ n in atTop, trajectory omega n ∈ A := by
  filter_upwards [fairSteps_frequently_visits_every_point] with omega homega
  intro A hA
  obtain ⟨x, hxA⟩ := hA
  exact (homega x).mono fun n hn ↦ by simpa only [hn] using hxA

/-- Finite-boundary specialization. -/
theorem fairSteps_frequently_visits_nonempty_finset
    {B : Finset Point} (hB : B.Nonempty) :
    ∀ᵐ omega ∂fairSteps, ∃ᶠ n in atTop, trajectory omega n ∈ B := by
  exact fairSteps_frequently_visits_nonempty_set
    (Set.nonempty_def.mpr ⟨hB.choose, hB.choose_spec⟩)

/-- Simultaneous finite-family form, useful for collections of annular
boundaries. -/
theorem fairSteps_frequently_visits_finset (B : Finset Point) :
    ∀ᵐ omega ∂fairSteps, ∀ x ∈ B,
      ∃ᶠ n in atTop, trajectory omega n = x := by
  filter_upwards [fairSteps_frequently_visits_every_point] with omega homega
  exact fun x _ ↦ homega x

end Erdos1165.SpatialRecurrence
