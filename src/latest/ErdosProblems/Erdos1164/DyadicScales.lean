import ErdosProblems.Erdos1164.LowerRadiusTail
import ErdosProblems.Erdos1164.UpperRadiusTail

/-! # Elementary scales for the two probability tails -/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1164

noncomputable def sqrtLogTime (n : ℕ) : ℝ := Real.sqrt (Real.log (n : ℝ))

theorem sqrtLogTime_nonneg (n : ℕ) : 0 ≤ sqrtLogTime n := Real.sqrt_nonneg _

theorem sqrtLogTime_sq {n : ℕ} (hn : 1 ≤ n) : sqrtLogTime n ^ 2 = Real.log (n : ℝ) :=
  Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hn))

theorem sqrtLogTime_tendsto : Tendsto sqrtLogTime atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_sqrtLogTime_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ sqrtLogTime n :=
  sqrtLogTime_tendsto.eventually (eventually_ge_atTop c)

/-- A fixed multiple of the square logarithm is eventually smaller than time. -/
theorem eventually_log_square_le_time (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) := by
  have hbase : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ C * Real.log (n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hbase.const_mul C
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn hb
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := (div_lt_iff₀ hnpos).mp hb
  simpa only [one_mul] using h.le

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

theorem dyadic_ge_index (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

theorem log_dyadic (j : ℕ) : Real.log ((2 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

theorem log_dyadic_add_two_le (j : ℕ) :
    Real.log (((2 ^ j + 2 : ℕ) : ℝ)) ≤ ((j : ℝ) + 2) * Real.log 2 := by
  have hj : 1 ≤ 2 ^ j := (by omega : 1 ≤ j + 1).trans (dyadic_ge_index j)
  have hpow : 2 ^ j + 2 ≤ 2 ^ (j + 2) := by
    rw [pow_add]
    norm_num
    omega
  have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ j + 2 : ℕ) : ℝ))
    (show ((2 ^ j + 2 : ℕ) : ℝ) ≤ ((2 ^ (j + 2) : ℕ) : ℝ) by exact_mod_cast hpow)
  rw [log_dyadic] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

theorem dyadic_budget_upper (j : ℕ) :
    (discReturnBudget (2 ^ j) : ℝ) ≤ 1000 * ((j : ℝ) + 2) ^ 2 + 1 := by
  have hlog := (log_dyadic_add_two_le j).trans
    (mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ (j : ℝ) + 2) log_two_le_one)
  have hnonneg : 0 ≤ Real.log (((2 ^ j + 2 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    rw [Nat.cast_add, Nat.cast_ofNat]
    have hp : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h := discReturnBudget_upper (2 ^ j)
  nlinarith

/-- The log convention at radius zero causes no exception to this event inclusion. -/
theorem logRadius_lower_event_subset (n j : ℕ) (u : ℝ) (hu : u ≤ (j : ℝ) * Real.log 2) :
    {s : WalkPath | logRadius s n < u} ⊆ {s | coveredRadius s n < 2 ^ j} := by
  intro s hs
  change coveredRadius s n < 2 ^ j
  by_cases hr : coveredRadius s n = 0
  · simpa only [hr] using (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
  · have hrpos : (0 : ℝ) < coveredRadius s n := by exact_mod_cast (Nat.pos_of_ne_zero hr)
    have hlog : Real.log (coveredRadius s n : ℝ) < Real.log ((2 ^ j : ℕ) : ℝ) := by
      rw [log_dyadic]
      exact hs.trans_le hu
    exact_mod_cast (Real.log_lt_log_iff hrpos (by positivity)).mp hlog

theorem logRadius_upper_event_subset (n r : ℕ) (hr : 1 ≤ r) (u : ℝ)
    (hu : Real.log (r : ℝ) ≤ u) :
    {s : WalkPath | u < logRadius s n} ⊆ {s | r ≤ coveredRadius s n} := by
  intro s hs
  change r ≤ coveredRadius s n
  by_contra h
  have hrad : coveredRadius s n ≤ r := by omega
  have hlog : logRadius s n ≤ Real.log (r : ℝ) := by
    by_cases hz : coveredRadius s n = 0
    · simp only [logRadius, hz, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hr)
    · apply Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz))
      exact_mod_cast hrad
  exact (not_lt_of_ge (hlog.trans hu)) hs

/-- Real-valued version of the checked lower tail. -/
theorem radius_lower_tail_real (n r : ℕ) (hn : 2 ≤ n)
    (hbudget : (discReturnBudget r + 1) ^ 2 ≤ n) :
    walkLaw.real {s | coveredRadius s n < r} ≤
      24 * (discReturnBudget r : ℝ) / Real.log (n : ℝ) +
        4 / (((r + 2 : ℕ) : ℝ) ^ 3) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hnon : 0 ≤ 24 * (discReturnBudget r : ℝ) / Real.log (n : ℝ) +
      4 / (((r + 2 : ℕ) : ℝ) ^ 3) := by positivity
  have h := ENNReal.toReal_mono (by finiteness) (radius_lower_tail n r hn hbudget)
  simpa only [ENNReal.toReal_ofReal hnon, measureReal_def] using h

/-- Real-valued version of the checked upper tail. -/
theorem radius_upper_tail_real {m n K : ℕ} (hm : LargeTargetScale m) (hK : 2 ≤ K) :
    walkLaw.real {s | 2 * m ^ 2 ≤ coveredRadius s n} ≤
      Real.exp ((K : ℝ) / (targetVisitCost m : ℝ) -
        (1 - targetCostDiscount) * (harmonic m : ℝ)) +
      Real.exp (-((K - 1 : ℕ) : ℝ) / (100 * Real.log ((n + 2 : ℕ) : ℝ))) := by
  have h := ENNReal.toReal_mono (by finiteness) (radius_upper_tail hm hK (n := n))
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, measureReal_def] using h

end Erdos1164
