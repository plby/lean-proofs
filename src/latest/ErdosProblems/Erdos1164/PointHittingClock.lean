import ErdosProblems.Erdos1164.DiscountedHit

/-! # Capped first-hit clocks and their exact restart identity -/

open MeasureTheory Set

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.HLOZGapEstimate

/-- The first positive visit to `y` from `x`, or the deadline if none occurs earlier.
When `x ≠ y` this is the ordinary first-hit clock capped at `N`. -/
noncomputable abbrev pointHitClock (x y : Point) (N : ℕ) : StepPath → ℕ :=
  nextVisitBefore (fun _ ↦ 0) (fun _ ↦ y - x) N

theorem pointHitClock_le (x y : Point) (N : ℕ) (w : StepPath) : pointHitClock x y N w ≤ N :=
  nextVisitBefore_le_deadline _ _ _ _

theorem pointHitClock_stopping (x y : Point) (N : ℕ) :
    IsFiniteStoppingTime (pointHitClock x y N) := by
  apply isFiniteStoppingTime_nextVisitBefore
  intro z n
  by_cases h : y - x = z
  · simpa only [h, Set.ofPred_true, Set.univ_inter] using
      (isFiniteStoppingTime_const 0).measurableSet_eq n
  · simp only [h, Set.ofPred_false, Set.empty_inter, MeasurableSet.empty]

theorem measurable_pointHitClock (x y : Point) (N : ℕ) : Measurable (pointHitClock x y N) := by
  apply measurable_to_countable'
  intro n
  exact (pointHitClock_stopping x y N).measurableSet_eq_global n

theorem pointHitClock_le_iff {x y : Point} (hxy : x ≠ y) {N n : ℕ} (hn : n < N)
    (w : StepPath) : pointHitClock x y N w ≤ n ↔ ∃ j ≤ n, trajectoryFrom x w j = y := by
  rw [nextVisitBefore_le_iff hn w]
  constructor
  · rintro ⟨j, hj, _, hp⟩
    refine ⟨j, hj, ?_⟩
    simp only [trajectoryFrom, hp, add_sub_cancel]
  · rintro ⟨j, hj, hp⟩
    have hjpos : 0 < j := by
      by_contra h
      have hj0 : j = 0 := by omega
      rw [hj0, trajectoryFrom_zero] at hp
      exact hxy hp
    refine ⟨j, hj, hjpos, ?_⟩
    have h : x + trajectory w j = y := hp
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h)

theorem pointHitClock_hit {x y : Point} {N : ℕ} {w : StepPath}
    (h : pointHitClock x y N w < N) : trajectoryFrom x w (pointHitClock x y N w) = y := by
  have hex := (nextVisitBefore_lt_deadline_iff w).mp h
  change x + trajectory w (nextVisitBefore (fun _ ↦ 0) (fun _ ↦ y - x) N w) = y
  unfold nextVisitBefore
  rw [dif_pos hex, (Nat.find_spec hex).2.2]
  abel

theorem pointHitClock_avoids {x y : Point} (hxy : x ≠ y) {N n : ℕ} {w : StepPath}
    (hn : n < pointHitClock x y N w) : trajectoryFrom x w n ≠ y := by
  intro hh
  have hnN := hn.trans_le (pointHitClock_le x y N w)
  have hle := (pointHitClock_le_iff hxy hnN w).mpr ⟨n, le_rfl, hh⟩
  omega

theorem pointHitClock_pos (x y : Point) {N : ℕ} (hN : 0 < N) (w : StepPath) :
    0 < pointHitClock x y N w := by
  unfold pointHitClock nextVisitBefore
  split_ifs with h
  · exact (Nat.find_spec h).2.1
  · exact hN

theorem trajectory_restart (w : StepPath) (n j : ℕ) :
    trajectoryFrom (trajectory w n) (shiftSteps n w) j = trajectory w (n + j) := by
  rw [trajectoryFrom, ← trajectory_add_sub_trajectory]
  abel

/-- Once a target is still unvisited, its residual capped first-hit clock is
the first-hit clock of the fresh shifted trajectory. -/
theorem pointHitClock_restart {y : Point} (hy : y ≠ 0) {N n : ℕ} {w : StepPath}
    (hn : n < pointHitClock 0 y N w) :
    pointHitClock 0 y N w = n + pointHitClock (trajectory w n) y (N - n) (shiftSteps n w) := by
  have hnN := hn.trans_le (pointHitClock_le 0 y N w)
  have hxy : trajectory w n ≠ y := by
    simpa only [trajectoryFrom, zero_add] using pointHitClock_avoids (Ne.symm hy) hn
  let t := pointHitClock (trajectory w n) y (N - n) (shiftSteps n w)
  have ht : t ≤ N - n := pointHitClock_le _ _ _ _
  apply Nat.le_antisymm
  · by_cases htf : t < N - n
    · have hh := pointHitClock_hit htf
      rw [trajectory_restart] at hh
      apply (pointHitClock_le_iff (Ne.symm hy) (by omega : n + t < N) w).mpr
      refine ⟨n + t, le_rfl, ?_⟩
      simpa only [trajectoryFrom, zero_add] using hh
    · have heq : t = N - n := by omega
      change pointHitClock 0 y N w ≤ n + t
      rw [heq, Nat.add_sub_of_le hnN.le]
      exact pointHitClock_le _ _ _ _
  · by_cases hg : pointHitClock 0 y N w < N
    · have hh := pointHitClock_hit hg
      have hrel : trajectoryFrom (trajectory w n) (shiftSteps n w)
          (pointHitClock 0 y N w - n) = y := by
        rw [trajectory_restart, Nat.add_sub_of_le hn.le]
        simpa only [trajectoryFrom, zero_add] using hh
      have ht' : t ≤ pointHitClock 0 y N w - n :=
        (pointHitClock_le_iff hxy (by omega : pointHitClock 0 y N w - n < N - n)
          (shiftSteps n w)).mpr ⟨_, le_rfl, hrel⟩
      change n + t ≤ pointHitClock 0 y N w
      omega
    · have hgN : pointHitClock 0 y N w = N := by
        have := pointHitClock_le 0 y N w
        omega
      change n + t ≤ pointHitClock 0 y N w
      rw [hgN]
      omega

end Erdos1164
