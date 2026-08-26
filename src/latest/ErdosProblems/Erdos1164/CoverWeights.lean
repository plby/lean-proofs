import ErdosProblems.Erdos1164.CoverClocks

/-! # Exponential weights on partial-cover clocks -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential

noncomputable def recordAmplification : ℝ := 1 / targetCostDiscount

theorem recordAmplification_pos : 0 < recordAmplification := one_div_pos.mpr targetCostDiscount_pos

theorem recordAmplification_ge_one : 1 ≤ recordAmplification := by
  unfold recordAmplification
  apply (le_div_iff₀ targetCostDiscount_pos).mpr
  simpa only [one_mul] using targetCostDiscount_lt_one.le

theorem recordAmplification_discount :
    ENNReal.ofReal recordAmplification * ENNReal.ofReal targetCostDiscount = 1 := by
  rw [← ENNReal.ofReal_mul recordAmplification_pos.le]
  simp only [recordAmplification, one_div_mul_cancel targetCostDiscount_pos.ne', ENNReal.ofReal_one]

/-- Visits split exactly across a deterministic time interval. -/
theorem originVisits_add (s : WalkPath) (n m : ℕ) :
    originVisits s (n + m) = originVisits s n + originVisits (fun j ↦ s (n + j)) m := by
  classical
  have he (s : WalkPath) (k : ℕ) : originVisits s k =
      ∑ j ∈ Finset.range k, if s j = 0 then (1 : ℕ) else 0 := by
    simp only [originVisits, Finset.sum_boole, Nat.cast_id]
  rw [he, he, he, Finset.sum_range_add]

/-- The origin-started translated trajectory is the original trajectory as a function. -/
theorem trajectoryFrom_origin : trajectoryFrom 0 = trajectory := by
  funext w j
  simp only [trajectoryFrom, zero_add]

theorem originVisits_restart_add (w : StepPath) (n m : ℕ) :
    originVisits (trajectory w) (n + m) = originVisits (trajectory w) n +
      originVisits (trajectoryFrom (trajectory w n) (shiftSteps n w)) m := by
  rw [originVisits_add]
  congr 1
  congr 1
  funext j
  exact (trajectory_restart w n j).symm

/-- Weight of a successful partial cover, including one record amplification
for each actual extension of its clock. -/
noncomputable def coverWeight (v : ℕ → Point) (N ell k : ℕ) (w : StepPath) : ℝ≥0∞ :=
  discountedHitAt 0 ell (prefixCoverClock v N k) {w | prefixCoverClock v N k w < N} w *
    ENNReal.ofReal recordAmplification ^ coverRecordCount v N k w

theorem measurable_coverWeight (v : ℕ → Point) (N ell k : ℕ) :
    Measurable (coverWeight v N ell k) := by
  apply (measurable_discountedHitAt 0 ell (measurable_prefixCoverClock v N k)
    (measurableSet_lt (measurable_prefixCoverClock v N k) measurable_const)).mul
  exact (measurable_of_countable
    (fun r : ℕ ↦ ENNReal.ofReal recordAmplification ^ r)).comp (measurable_coverRecordCount v N k)

theorem coverWeight_of_alive {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (h : prefixCoverClock v N k w < N) :
    coverWeight v N ell k w = ENNReal.ofReal
      (Real.exp (-(originVisits (trajectory w) (prefixCoverClock v N k w) : ℝ) / (ell : ℝ))) *
        ENNReal.ofReal recordAmplification ^ coverRecordCount v N k w := by
  simp only [coverWeight, discountedHitAt, Set.indicator_apply, Set.mem_ofPred_eq, h, if_true, trajectoryFrom_origin]

theorem coverWeight_of_dead {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (h : ¬prefixCoverClock v N k w < N) : coverWeight v N ell k w = 0 := by
  simp only [coverWeight, discountedHitAt, Set.indicator_apply, Set.mem_ofPred_eq, h, if_false, zero_mul]

theorem coverWeight_zero (v : ℕ → Point) {N : ℕ} (hN : 0 < N) (ell : ℕ) (w : StepPath) :
    coverWeight v N ell 0 w = 1 := by
  rw [coverWeight_of_alive hN]
  simp only [prefixCoverClock_zero, originVisits_zero, Nat.cast_zero, neg_zero,
    zero_div, Real.exp_zero, ENNReal.ofReal_one, coverRecordCount_zero, pow_zero, mul_one]

/-- Listing an already visited target leaves the full weight unchanged. -/
theorem coverWeight_no_extension {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (h : w ∉ coverExtension v N k) : coverWeight v N ell (k + 1) w = coverWeight v N ell k w := by
  classical
  have hclock : prefixCoverClock v N (k + 1) w = prefixCoverClock v N k w := by
    rw [prefixCoverClock_succ]
    exact max_eq_left (Nat.le_of_not_gt h)
  have hrecord : coverRecordCount v N (k + 1) w = coverRecordCount v N k w := by
    rw [coverRecordCount_succ, if_neg h, add_zero]
  by_cases ha : prefixCoverClock v N k w < N
  · rw [coverWeight_of_alive (hclock.symm ▸ ha), coverWeight_of_alive ha, hclock, hrecord]
  · rw [coverWeight_of_dead (by simpa only [hclock] using ha), coverWeight_of_dead ha]

/-- The new clock on an extension is precisely the old clock plus the fresh
capped hitting time. -/
theorem prefixCoverClock_extension_restart {v : ℕ → Point} {N k : ℕ} {w : StepPath}
    (hy : v k ≠ 0) (h : w ∈ coverExtension v N k) :
    prefixCoverClock v N (k + 1) w = prefixCoverClock v N k w +
      pointHitClock (trajectory w (prefixCoverClock v N k w)) (v k)
        (N - prefixCoverClock v N k w) (shiftSteps (prefixCoverClock v N k w) w) := by
  rw [prefixCoverClock_succ, max_eq_right h.le]
  exact pointHitClock_restart hy h

/-- Exact factorization of the weight on a genuine extension. -/
theorem coverWeight_extension {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (hy : v k ≠ 0) (h : w ∈ coverExtension v N k) :
    let n := prefixCoverClock v N k w
    let x := trajectory w n
    let τ := pointHitClock x (v k) (N - n)
    coverWeight v N ell (k + 1) w =
      coverWeight v N ell k w * ENNReal.ofReal recordAmplification *
        discountedHitAt x ell τ {z | τ z < N - n} (shiftSteps n w) := by
  classical
  dsimp only
  let n := prefixCoverClock v N k w
  let x := trajectory w n
  let τ := pointHitClock x (v k) (N - n)
  have hn : n < N := h.trans_le (pointHitClock_le 0 (v k) N w)
  have hclock : prefixCoverClock v N (k + 1) w = n + τ (shiftSteps n w) :=
    prefixCoverClock_extension_restart hy h
  have hrecord : coverRecordCount v N (k + 1) w = coverRecordCount v N k w + 1 := by
    rw [coverRecordCount_succ, if_pos h]
  by_cases hnew : prefixCoverClock v N (k + 1) w < N
  · have hf : τ (shiftSteps n w) < N - n := by omega
    dsimp only [τ, x, n] at hf
    rw [coverWeight_of_alive hnew, coverWeight_of_alive hn, hrecord, pow_succ]
    simp only [discountedHitAt, Set.indicator_apply, Set.mem_ofPred_eq, hf, if_true]
    rw [hclock, originVisits_restart_add]
    simp only [Nat.cast_add]
    have hex (a b e : ℝ) : -(a + b) / e = -a / e + -b / e := by ring
    rw [hex, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    dsimp only [n, x, τ]
    ac_rfl
  · have hf : ¬τ (shiftSteps n w) < N - n := by omega
    dsimp only [τ, x, n] at hf
    rw [coverWeight_of_dead hnew]
    simp only [discountedHitAt, Set.indicator_apply, Set.mem_ofPred_eq, hf, if_false, mul_zero]

end Erdos1164
