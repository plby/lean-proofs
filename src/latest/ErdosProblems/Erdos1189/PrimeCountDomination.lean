/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform domination of the prime-counting terms in divisor entropy.
Informal argument: PNT and the summable envelope u^2(1-log u).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.TruncatedCountingMoments
import ErdosProblems.Erdos1189.LogWeightSummability

namespace Erdos1189

open Finset Filter

lemma primeCounting_ceil_zero_of_le_one {y : ℝ} (hy : y ≤ 1) :
    Nat.primeCounting (Nat.ceil y) = 0 := by
  apply Nat.primeCounting_eq_zero_iff.mpr
  exact Nat.ceil_le.mpr (by simpa using hy)

lemma primeCounting_ceil_le_two_mul {y : ℝ} (hy : 1 < y) :
    (Nat.primeCounting (Nat.ceil y) : ℝ) ≤ 2 * y := by
  have hcard : (Nat.primesLE (Nat.ceil y)).card ≤ Nat.ceil y := by
    have hsub : Nat.primesLE (Nat.ceil y) ⊆ Ioc 0 (Nat.ceil y) := fun p hp =>
      mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting] at hcard
  have hcard' : (Nat.primeCounting (Nat.ceil y) : ℝ) ≤ Nat.ceil y := by exact_mod_cast hcard
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ y by linarith)
  linarith

lemma exists_realPrimeCount_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 < y →
      (Nat.primeCounting (Nat.ceil y) : ℝ) * (1 + Real.log y) ≤ C * y := by
  have hgood : ∀ᶠ y : ℝ in atTop, 2 ≤ y ∧ 1 ≤ Real.log y ∧
      (Nat.primeCounting (Nat.ceil y) : ℝ) * Real.log y ≤ 2 * y := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      (tendsto_order.mp real_primeCounting_ratio).2 2 (by norm_num)] with y hy hlog hratio
    have hqpos : 0 < realLogPower 1 y := div_pos (by positivity) (by linarith)
    have hs := (div_lt_iff₀ hqpos).mp hratio
    have hs' : (Nat.primeCounting (Nat.ceil y) : ℝ) < 2 * y / Real.log y := by
      simpa only [realLogPower, pow_one, mul_div_assoc] using hs
    exact ⟨hy, hlog, ((lt_div_iff₀ (by linarith)).mp hs').le⟩
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hgood
  have hYlog : 1 ≤ Real.log Y := (hY Y le_rfl).2.1
  refine ⟨4 * (1 + Real.log Y), by linarith, ?_⟩
  intro y hy
  have hS0 : (0 : ℝ) ≤ Nat.primeCounting (Nat.ceil y) := Nat.cast_nonneg _
  by_cases hyY : Y ≤ y
  · obtain ⟨_, hlog, hS⟩ := hY y hyY
    have hS' := le_mul_of_one_le_right hS0 hlog
    have hC : 4 * y ≤ 4 * (1 + Real.log Y) * y := by
      have := mul_nonneg (show 0 ≤ Real.log Y by linarith) (show 0 ≤ y by linarith)
      nlinarith
    nlinarith
  · have hlog := Real.log_le_log (show 0 < y by linarith) (show y ≤ Y by linarith)
    have hbound := primeCounting_ceil_le_two_mul hy
    have hm := mul_le_mul hbound (show 1 + Real.log y ≤ 1 + Real.log Y by linarith)
      (show 0 ≤ 1 + Real.log y by have := (Real.log_pos hy).le; linarith)
      (show 0 ≤ 2 * y by positivity)
    have hpos := mul_nonneg (show 0 ≤ 1 + Real.log Y by linarith) (show 0 ≤ y by linarith)
    nlinarith

lemma scaled_prime_count_domination {C x u : ℝ}
    (hC : 0 < C)
    (hbound : ∀ y : ℝ, 1 < y →
      (Nat.primeCounting (Nat.ceil y) : ℝ) * (1 + Real.log y) ≤ C * y)
    (hx : 2 ≤ x) (hu : 0 < u) (hu1 : u ≤ 1) :
    (Nat.primeCounting (Nat.ceil (x * u)) : ℝ) * u / realLogPower 1 x ≤
      C * u ^ 2 * (1 - Real.log u) := by
  have hx0 : 0 < x := by linarith
  have hlogu : Real.log u ≤ 0 := by simpa using Real.log_le_log hu hu1
  by_cases hy : x * u ≤ 1
  · rw [primeCounting_ceil_zero_of_le_one hy, Nat.cast_zero, zero_mul, zero_div]
    exact mul_nonneg (by positivity) (by linarith)
  · have hy1 : 1 < x * u := by linarith
    have hlogy : 0 ≤ Real.log (x * u) := (Real.log_pos hy1).le
    have hlogx : Real.log x ≤ (1 - Real.log u) * (1 + Real.log (x * u)) := by
      have heq := Real.log_mul hx0.ne' hu.ne'
      have hh := mul_nonpos_of_nonpos_of_nonneg hlogu hlogy
      nlinarith
    have hS0 : (0 : ℝ) ≤ Nat.primeCounting (Nat.ceil (x * u)) := Nat.cast_nonneg _
    have hSlog := mul_le_mul_of_nonneg_left hlogx hS0
    have hSbound := mul_le_mul_of_nonneg_left (hbound (x * u) hy1)
      (show 0 ≤ 1 - Real.log u by linarith)
    have hnum : (Nat.primeCounting (Nat.ceil (x * u)) : ℝ) * Real.log x ≤
        C * u * (1 - Real.log u) * x := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hnum hu.le
    have hdiv : (Nat.primeCounting (Nat.ceil (x * u)) : ℝ) * u * Real.log x / x ≤
        C * u ^ 2 * (1 - Real.log u) := (div_le_iff₀ hx0).mpr (by nlinarith)
    simpa only [realLogPower, pow_one, div_div_eq_mul_div] using hdiv

theorem exists_counting_mass_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ e : ℕ,
      ‖(Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) * logIncrement e /
        realLogPower 1 x‖ ≤ C * (logIncrement e ^ 2 * (1 - Real.log (logIncrement e))) := by
  obtain ⟨C, hC, hbound⟩ := exists_realPrimeCount_bound
  refine ⟨C, hC, ?_⟩
  intro x hx e
  have hnonneg : 0 ≤ (Nat.primeCounting (Nat.ceil (x * logIncrement e)) : ℝ) * logIncrement e /
      realLogPower 1 x := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (logIncrement_pos e).le)
        (div_nonneg (by positivity) (Real.log_nonneg (by linarith)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [mul_assoc] using scaled_prime_count_domination hC hbound hx
    (logIncrement_pos e) (logIncrement_le_one e)

end Erdos1189
