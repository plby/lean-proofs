/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform domination of the exponent contributions to the counting size.
Informal argument: a global prime-weight bound and the summable envelope u^2(1-log u).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingFibres
import ErdosProblems.Erdos1189.LogWeightSummability

namespace Erdos1189

open Filter

lemma exists_realPrimeWeightSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 < y →
      realPrimeWeightSum y * (1 + Real.log y) ≤ C * y ^ 2 := by
  have hgood : ∀ᶠ y : ℝ in atTop, 2 ≤ y ∧ 1 ≤ Real.log y ∧
      realPrimeWeightSum y * Real.log y ≤ y ^ 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      (tendsto_order.mp real_prime_weight_sum_ratio).2 1 (by norm_num)] with y hy hlog hratio
    have hqpos : 0 < realLogPower 2 y := div_pos (by positivity) (by linarith)
    have hs : realPrimeWeightSum y < y ^ 2 / Real.log y := (div_lt_one hqpos).mp hratio
    exact ⟨hy, hlog, ((lt_div_iff₀ (by linarith)).mp hs).le⟩
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hgood
  have hYlog : 1 ≤ Real.log Y := (hY Y le_rfl).2.1
  refine ⟨2 * (1 + Real.log Y), by linarith, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  have hS0 := realPrimeWeightSum_nonneg y
  by_cases hyY : Y ≤ y
  · obtain ⟨_, hlog, hS⟩ := hY y hyY
    have hS' : realPrimeWeightSum y ≤ realPrimeWeightSum y * Real.log y :=
      le_mul_of_one_le_right hS0 hlog
    have hC : 2 * y ^ 2 ≤ 2 * (1 + Real.log Y) * y ^ 2 := by
      have := mul_nonneg (show 0 ≤ Real.log Y by linarith) (sq_nonneg y)
      nlinarith
    nlinarith
  · have hlog : Real.log y ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    have hS := realPrimeWeightSum_le_two_sq hy0
    have hm := mul_le_mul hS (show 1 + Real.log y ≤ 1 + Real.log Y by linarith)
      (show 0 ≤ 1 + Real.log y by have := (Real.log_pos hy).le; linarith)
      (show 0 ≤ 2 * y ^ 2 by positivity)
    nlinarith

lemma scaled_prime_weight_domination {C x u : ℝ}
    (hC : 0 < C)
    (hbound : ∀ y : ℝ, 1 < y → realPrimeWeightSum y * (1 + Real.log y) ≤ C * y ^ 2)
    (hx : 2 ≤ x) (hu : 0 < u) (hu1 : u ≤ 1) :
    realPrimeWeightSum (x * u) / realLogPower 2 x ≤ C * u ^ 2 * (1 - Real.log u) := by
  have hx0 : 0 < x := by linarith
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogu : Real.log u ≤ 0 := by simpa using Real.log_le_log hu hu1
  by_cases hy : x * u ≤ 1
  · rw [realPrimeWeightSum_zero_of_le_one hy, zero_div]
    exact mul_nonneg (by positivity) (by linarith)
  · have hy1 : 1 < x * u := by linarith
    have hlogy : 0 ≤ Real.log (x * u) := (Real.log_pos hy1).le
    have hlogx : Real.log x ≤ (1 - Real.log u) * (1 + Real.log (x * u)) := by
      have heq := Real.log_mul hx0.ne' hu.ne'
      have hh := mul_nonpos_of_nonpos_of_nonneg hlogu hlogy
      nlinarith
    have hS0 := realPrimeWeightSum_nonneg (x * u)
    have hSlog := mul_le_mul_of_nonneg_left hlogx hS0
    have hSbound := mul_le_mul_of_nonneg_left (hbound (x * u) hy1)
      (show 0 ≤ 1 - Real.log u by linarith)
    have hnum : realPrimeWeightSum (x * u) * Real.log x ≤
        C * u ^ 2 * (1 - Real.log u) * x ^ 2 := by nlinarith
    have hdiv := (div_le_iff₀ (sq_pos_of_pos hx0)).mpr hnum
    simpa only [realLogPower, div_div_eq_mul_div] using hdiv

theorem exists_counting_size_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ e : ℕ,
      ‖realPrimeWeightSum (x * logIncrement e) / realLogPower 2 x‖ ≤
        C * (logIncrement e ^ 2 * (1 - Real.log (logIncrement e))) := by
  obtain ⟨C, hC, hbound⟩ := exists_realPrimeWeightSum_bound
  refine ⟨C, hC, ?_⟩
  intro x hx e
  have hnonneg : 0 ≤ realPrimeWeightSum (x * logIncrement e) / realLogPower 2 x :=
    div_nonneg (realPrimeWeightSum_nonneg _) (div_nonneg (sq_nonneg _)
      (Real.log_nonneg (by linarith)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [mul_assoc] using scaled_prime_weight_domination hC hbound hx
    (logIncrement_pos e) (logIncrement_le_one e)

end Erdos1189
