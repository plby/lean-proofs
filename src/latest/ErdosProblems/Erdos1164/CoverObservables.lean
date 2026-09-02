import ErdosProblems.Erdos1164.CoverClocks
import ErdosProblems.Erdos1165.HLOZGapPointReturn

/-! # Observability of the partial-cover state -/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1164

open Erdos1165 Erdos1165.HLOZGapEstimate Erdos1165.HLOZGapPointReturn
open Erdos1165.HLOZGapStoppedCandidate

/-- A stopping time's own value is observable at that time. -/
theorem stopping_value_observable {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) (a : ℕ) :
    IsMeasurableAtStopping τ {w | τ w = a} := by
  intro n
  by_cases hna : n = a
  · subst a
    simpa only [Set.inter_self] using hτ.measurableSet_eq n
  · have he : {w | τ w = a} ∩ {w | τ w = n} = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ha, hn⟩
      exact hna (hn.symm.trans ha)
    rw [he]
    exact (incrementFiltration n).measurableSet_empty

/-- At `τ` it is known whether another stopping time has already occurred. -/
theorem stopping_comparison_observable {τ σ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) (hσ : IsFiniteStoppingTime σ) :
    IsMeasurableAtStopping τ {w | τ w < σ w} := by
  intro n
  have he : {w | τ w < σ w} ∩ {w | τ w = n} =
      {w | n < σ w} ∩ {w | τ w = n} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hl, he⟩ <;> exact ⟨by simpa only [he] using hl, he⟩
  rw [he]
  have hs : MeasurableSet[incrementFiltration n] {w : StepPath | σ w ≤ n} := by simpa using hσ n
  have hs' : MeasurableSet[incrementFiltration n] {w : StepPath | n < σ w} := by
    simpa only [Set.compl_ofPred, not_le] using hs.compl
  exact hs'.inter (hτ.measurableSet_eq n)

/-- Indicators of stopped events are countable-valued stopped observables. -/
theorem stopped_indicator_observable {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A : Set StepPath} (hA : IsMeasurableAtStopping τ A) (a : ℕ) :
    IsMeasurableAtStopping τ {w | (A.indicator (fun _ ↦ (1 : ℕ))) w = a} := by
  intro n
  have he : {w | A.indicator (fun _ ↦ (1 : ℕ)) w = a} ∩ {w | τ w = n} =
      (if 1 = a then A ∩ {w | τ w = n} else ∅) ∪
        (if 0 = a then Aᶜ ∩ {w | τ w = n} else ∅) := by
    classical
    ext w
    by_cases hw : w ∈ A <;> simp [hw, and_comm]
  rw [he]
  have hc := isMeasurableAtStopping_compl hτ hA
  have hempty : MeasurableSet[incrementFiltration n] (∅ : Set StepPath) :=
    (incrementFiltration n).measurableSet_empty
  split_ifs <;> first | exact (hA n).union (hc n) |
    exact (hA n).union hempty | exact hempty.union (hc n) | exact hempty.union hempty

theorem coverExtension_observable (v : ℕ → Point) (N k : ℕ) :
    IsMeasurableAtStopping (prefixCoverClock v N k) (coverExtension v N k) :=
  stopping_comparison_observable (prefixCoverClock_stopping v N k)
    (pointHitClock_stopping 0 (v k) N)

/-- Deterministic-time origin local time uses only the available increments. -/
theorem measurable_originVisits_filtration (n : ℕ) :
    @Measurable StepPath ℕ (incrementFiltration n) inferInstance
      (fun w ↦ originVisits (trajectory w) n) := by
  classical
  have he : (fun w ↦ originVisits (trajectory w) n) =
      fun w ↦ ∑ j ∈ Finset.range n, if trajectory w j = 0 then (1 : ℕ) else 0 := by
    funext w
    simp only [originVisits, Finset.sum_boole, Nat.cast_id]
  rw [he]
  apply Finset.measurable_sum
  intro j hj
  have hjn : j ≤ n := (Finset.mem_range.mp hj).le
  have hm : @Measurable StepPath Point (incrementFiltration n) inferInstance
      (fun w ↦ trajectory w j) :=
    (measurable_trajectory_at_incrementFiltration j).mono (incrementFiltration.mono hjn) le_rfl
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const measurable_const

theorem originVisits_at_stopping_observable {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) (a : ℕ) :
    IsMeasurableAtStopping τ {w | originVisits (trajectory w) (τ w) = a} := by
  intro n
  have he : {w | originVisits (trajectory w) (τ w) = a} ∩ {w | τ w = n} =
      {w | originVisits (trajectory w) n = a} ∩ {w | τ w = n} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hl, he⟩ <;> exact ⟨by simpa only [he] using hl, he⟩
  rw [he]
  exact (measurableSet_eq_fun (measurable_originVisits_filtration n) measurable_const).inter
    (hτ.measurableSet_eq n)

/-- The record count of already listed targets is known at the current
partial-cover time. -/
theorem coverRecordCount_observable (v : ℕ → Point) (N k : ℕ) (a : ℕ) :
    IsMeasurableAtStopping (prefixCoverClock v N k) {w | coverRecordCount v N k w = a} := by
  classical
  induction k generalizing a with
  | zero =>
    change IsMeasurableAtStopping (fun _ : StepPath ↦ 0) _
    simpa only [coverRecordCount_zero] using
      stopping_value_observable (isFiniteStoppingTime_const 0) a
  | succ k ih =>
    have hs := prefixCoverClock_stopping v N (k + 1)
    have hmono : ∀ w, prefixCoverClock v N k w ≤ prefixCoverClock v N (k + 1) w :=
      fun w ↦ prefixCoverClock_mono v N w (Nat.le_succ k)
    have hprev (b : ℕ) : IsMeasurableAtStopping (prefixCoverClock v N (k + 1))
        {w | coverRecordCount v N k w = b} := IsMeasurableAtStopping.mono_time (ih b) hs hmono
    have hind (b : ℕ) : IsMeasurableAtStopping (prefixCoverClock v N (k + 1))
        {w | (coverExtension v N k).indicator (fun _ ↦ (1 : ℕ)) w = b} :=
      IsMeasurableAtStopping.mono_time
        (stopped_indicator_observable (prefixCoverClock_stopping v N k)
          (coverExtension_observable v N k) b) hs hmono
    have h := isMeasurableAtStopping_binary_fiber hprev hind (fun b c : ℕ ↦ b + c) a
    simpa only [coverRecordCount_succ, Set.indicator_apply] using h

/-- Time, origin visits, record count, and location at a partial cover. -/
noncomputable def coverState (v : ℕ → Point) (N k : ℕ) (w : StepPath) :
    ℕ × ℕ × ℕ × Point :=
  (prefixCoverClock v N k w, originVisits (trajectory w) (prefixCoverClock v N k w),
    coverRecordCount v N k w, trajectory w (prefixCoverClock v N k w))

theorem coverState_observable (v : ℕ → Point) (N k : ℕ) (s : ℕ × ℕ × ℕ × Point) :
    IsMeasurableAtStopping (prefixCoverClock v N k) {w | coverState v N k w = s} := by
  have hs := prefixCoverClock_stopping v N k
  have hqpoint (a : ℕ × Point) := isMeasurableAtStopping_binary_fiber
    (coverRecordCount_observable v N k) (stoppedLocation_fiber_observable hs) Prod.mk a
  have hrest (a : ℕ × ℕ × Point) := isMeasurableAtStopping_binary_fiber
    (originVisits_at_stopping_observable hs) hqpoint Prod.mk a
  exact isMeasurableAtStopping_binary_fiber (stopping_value_observable hs) hrest Prod.mk s

end Erdos1164
