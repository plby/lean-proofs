/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform deterministic tails on logarithmically truncated intervals.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointScale
import ErdosProblems.Erdos521.Model

namespace Erdos521

open Filter
open scoped BigOperators

theorem polynomial_tail_le (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) (hc : c < 1) :
    |(polynomial ε m).eval x - (polynomial ε n).eval x| ≤ c ^ (n + 1) / (1 - c) := by
  rw [polynomial_eval, polynomial_eval, powerSum, powerSum,
    ← Finset.sum_Ico_eq_sub (fun k ↦ ε k * x ^ k) (Nat.add_le_add_right hnm 1)]
  calc
    |∑ k ∈ Finset.Ico (n + 1) (m + 1), ε k * x ^ k| ≤
        ∑ k ∈ Finset.Ico (n + 1) (m + 1), |ε k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico (n + 1) (m + 1), c ^ k := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx k)]
      exact (mul_le_mul_of_nonneg_right (hε k) (pow_nonneg hx k)).trans
        (by simpa only [one_mul] using pow_le_pow_left₀ hx hxc k)
    _ ≤ _ := geom_sum_Ico_le_of_lt_one (hx.trans hxc) hc

theorem endpointCenter_tail_first_le {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    (hx : 0 ≤ endpointCenter C n) :
    endpointCenter C n ^ (n + 1) ≤ (n : ℝ) ^ (-C) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  apply (pow_le_exp_nat_mul (u := -(C * Real.log n / n)) hx
    (by dsimp [endpointCenter]; linarith) (n + 1)).trans
  rw [Real.rpow_def_of_pos hn₀]
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ C * Real.log n / n := by positivity
  have hid : (n : ℝ) * (C * Real.log n / n) = C * Real.log n := by field_simp
  push_cast
  nlinarith

theorem eventually_polynomial_tail_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℕ → ℝ, (∀ k, |ε k| ≤ 1) →
      ∀ m, n ≤ m → ∀ x ∈ Set.Icc (0 : ℝ) (endpointCenter C n),
        |(polynomial ε m).eval x - (polynomial ε n).eval x| ≤ (n : ℝ) ^ (1 - C) := by
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hC
  have hlog := ht.eventually_ge_atTop 1
  filter_upwards [eventually_endpointCenter_bounds hC, hlog, eventually_ge_atTop 2]
    with n hc hlog hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc₀ : 0 ≤ endpointCenter C n := by linarith [hc.1]
  have hden : 0 < 1 - endpointCenter C n := sub_pos.mpr hc.2
  have hden' : 1 ≤ (1 - endpointCenter C n) * n := by
    have hid : (1 - endpointCenter C n) * n = C * Real.log n := by
      dsimp [endpointCenter]
      field_simp
      ring
    rwa [hid]
  intro ε hε m hnm x hx
  calc
    |(polynomial ε m).eval x - (polynomial ε n).eval x| ≤
        endpointCenter C n ^ (n + 1) / (1 - endpointCenter C n) :=
      polynomial_tail_le ε hε hnm hx.1 hx.2 hc.2
    _ ≤ (n : ℝ) ^ (-C) / (1 - endpointCenter C n) :=
      div_le_div_of_nonneg_right (endpointCenter_tail_first_le hC.le (by omega) hc₀) hden.le
    _ ≤ (n : ℝ) ^ (-C) * n := by
      apply (div_le_iff₀ hden).mpr
      have h := mul_le_mul_of_nonneg_left hden' (Real.rpow_nonneg hn₀.le (-C))
      simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using h
    _ = (n : ℝ) ^ (1 - C) := by
      calc
        (n : ℝ) ^ (-C) * n = (n : ℝ) ^ (-C) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring

end Erdos521
