import ErdosProblems.Erdos1164.PointHittingClock
import ErdosProblems.Erdos1164.PermutationRecords

/-! # Capped clocks for covering successive deterministic targets -/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.HLOZGapEstimate

/-- Cover the first `k` targets, with a deterministic deadline. -/
noncomputable def prefixCoverClock (v : ℕ → Point) (N : ℕ) : ℕ → StepPath → ℕ
  | 0 => fun _ ↦ 0
  | k + 1 => fun w ↦ max (prefixCoverClock v N k w) (pointHitClock 0 (v k) N w)

@[simp] theorem prefixCoverClock_zero (v : ℕ → Point) (N : ℕ) (w : StepPath) :
    prefixCoverClock v N 0 w = 0 := rfl

theorem prefixCoverClock_succ (v : ℕ → Point) (N k : ℕ) (w : StepPath) :
    prefixCoverClock v N (k + 1) w =
      max (prefixCoverClock v N k w) (pointHitClock 0 (v k) N w) := rfl

theorem isFiniteStoppingTime_max {τ σ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) (hσ : IsFiniteStoppingTime σ) :
    IsFiniteStoppingTime (fun w ↦ max (τ w) (σ w)) := by
  intro n
  have ht : MeasurableSet[incrementFiltration n] {w : StepPath | τ w ≤ n} := by simpa using hτ n
  have hs : MeasurableSet[incrementFiltration n] {w : StepPath | σ w ≤ n} := by simpa using hσ n
  simpa [max_le_iff, Set.ofPred_and] using ht.inter hs

theorem prefixCoverClock_stopping (v : ℕ → Point) (N k : ℕ) :
    IsFiniteStoppingTime (prefixCoverClock v N k) := by
  induction k with
  | zero => exact isFiniteStoppingTime_const 0
  | succ k ih => exact isFiniteStoppingTime_max ih (pointHitClock_stopping 0 (v k) N)

theorem measurable_prefixCoverClock (v : ℕ → Point) (N k : ℕ) :
    Measurable (prefixCoverClock v N k) := by
  apply measurable_to_countable'
  intro n
  exact (prefixCoverClock_stopping v N k).measurableSet_eq_global n

theorem prefixCoverClock_le_deadline (v : ℕ → Point) (N k : ℕ) (w : StepPath) :
    prefixCoverClock v N k w ≤ N := by
  induction k with
  | zero => exact Nat.zero_le N
  | succ k ih => exact max_le ih (pointHitClock_le 0 (v k) N w)

theorem prefixCoverClock_mono (v : ℕ → Point) (N : ℕ) (w : StepPath) :
    Monotone fun k ↦ prefixCoverClock v N k w := by
  exact monotone_nat_of_le_succ (fun k ↦ le_max_left _ _)

theorem pointHitClock_le_prefix {v : ℕ → Point} {N i k : ℕ} (hik : i < k) (w : StepPath) :
    pointHitClock 0 (v i) N w ≤ prefixCoverClock v N k w := by
  have hs : pointHitClock 0 (v i) N w ≤ prefixCoverClock v N (i + 1) w := le_max_right _ _
  exact hs.trans (prefixCoverClock_mono v N w (by omega))

theorem prefixCoverClock_lt_iff {v : ℕ → Point} {N k n : ℕ} (hn : 0 < n) (w : StepPath) :
    prefixCoverClock v N k w < n ↔ ∀ i < k, pointHitClock 0 (v i) N w < n := by
  induction k with
  | zero => simp [hn]
  | succ k ih =>
    rw [prefixCoverClock_succ, max_lt_iff, ih]
    constructor
    · rintro ⟨hp, hk⟩ i hi
      by_cases hik : i < k
      · exact hp i hik
      · have hieq : i = k := by omega
        simpa only [hieq] using hk
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), h k (by omega)⟩

/-- At a successful partial cover time, the walk is either still at time zero
or at one of the targets already listed. -/
theorem prefixCoverClock_position {v : ℕ → Point} {N k : ℕ} {w : StepPath}
    (h : prefixCoverClock v N k w < N) :
    trajectory w (prefixCoverClock v N k w) = 0 ∨
      ∃ i < k, trajectory w (prefixCoverClock v N k w) = v i := by
  induction k with
  | zero => exact Or.inl (trajectory_zero w)
  | succ k ih =>
    by_cases hnext : prefixCoverClock v N k w ≤ pointHitClock 0 (v k) N w
    · rw [prefixCoverClock_succ, max_eq_right hnext] at h ⊢
      right
      refine ⟨k, by omega, ?_⟩
      simpa only [trajectoryFrom, zero_add] using pointHitClock_hit h
    · have hold : pointHitClock 0 (v k) N w ≤ prefixCoverClock v N k w := by omega
      rw [prefixCoverClock_succ, max_eq_left hold] at h ⊢
      rcases ih h with hz | ⟨i, hi, hp⟩
      · exact Or.inl hz
      · exact Or.inr ⟨i, by omega, hp⟩

/-- A newly listed target actually extends the current cover clock. -/
def coverExtension (v : ℕ → Point) (N k : ℕ) : Set StepPath :=
  {w | prefixCoverClock v N k w < pointHitClock 0 (v k) N w}

/-- Number of genuine cover-clock extensions among the first `k` targets. -/
noncomputable def coverRecordCount (v : ℕ → Point) (N k : ℕ) (w : StepPath) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range k, if w ∈ coverExtension v N i then 1 else 0

@[simp] theorem coverRecordCount_zero (v : ℕ → Point) (N : ℕ) (w : StepPath) :
    coverRecordCount v N 0 w = 0 := by
  classical
  simp [coverRecordCount]

open Classical in
theorem coverRecordCount_succ (v : ℕ → Point) (N k : ℕ) (w : StepPath) :
    coverRecordCount v N (k + 1) w = coverRecordCount v N k w +
      (if w ∈ coverExtension v N k then 1 else 0) := by
  exact Finset.sum_range_succ _ _

theorem measurableSet_coverExtension (v : ℕ → Point) (N k : ℕ) :
    MeasurableSet (coverExtension v N k) :=
  measurableSet_lt (measurable_prefixCoverClock v N k) (measurable_pointHitClock 0 (v k) N)

theorem measurable_coverRecordCount (v : ℕ → Point) (N k : ℕ) :
    Measurable (coverRecordCount v N k) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_coverExtension v N i) measurable_const measurable_const

/-- Cover-clock extensions coincide with left records of the first-hit times. -/
theorem coverExtension_iff_record {v : ℕ → Point} {N k : ℕ} (hN : 0 < N) (w : StepPath) :
    w ∈ coverExtension v N k ↔
      ∀ i < k, pointHitClock 0 (v i) N w < pointHitClock 0 (v k) N w :=
  prefixCoverClock_lt_iff (pointHitClock_pos 0 (v k) hN w) w

theorem coverRecordCount_eq_leftRecordCount (v : ℕ → Point) {N M : ℕ}
    (hN : 0 < N) (w : StepPath) :
    coverRecordCount v N M w = leftRecordCount
      (fun i : Fin M ↦ (pointHitClock 0 (v (i : ℕ)) N w : ℝ)) := by
  classical
  unfold coverRecordCount leftRecordCount
  have hterm (i : Fin M) :
      (if ∀ j : Fin M, j < i →
          (pointHitClock 0 (v (j : ℕ)) N w : ℝ) <
            pointHitClock 0 (v (i : ℕ)) N w then 1 else 0 : ℕ) =
      (if w ∈ coverExtension v N (i : ℕ) then 1 else 0) := by
    apply if_congr _ rfl rfl
    rw [coverExtension_iff_record hN]
    constructor
    · intro h j hj
      have hjM : j < M := hj.trans i.isLt
      exact_mod_cast h ⟨j, hjM⟩ hj
    · intro h j hj
      exact_mod_cast h j hj
  simp_rw [hterm]
  exact (Fin.sum_univ_eq_sum_range
    (fun i ↦ if w ∈ coverExtension v N i then 1 else 0) M).symm

end Erdos1164
