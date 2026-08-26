import ErdosProblems.Erdos67.StationarySubgroupFactors

/-!
# A uniform lower bound for finite sieve densities

A bounded reciprocal sum of primes forces their finite Euler products to
stay uniformly positive. This elementary estimate is used in the subgroup
divergence argument.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

theorem neg_two_mul_le_log_one_sub {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hy : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [← one_div]
    apply (div_le_iff₀ hy).2
    have hprod := mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos hy
  linarith

theorem exp_neg_two_div_le_prime_factor (p : ℕ) (hp : p.Prime) :
    Real.exp (-2 * (1 / (p : ℝ))) ≤ 1 - 1 / (p : ℝ) := by
  have hpr : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp.two_le
  have hx : (1 / (p : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) hpr
  apply (Real.le_log_iff_exp_le (by linarith : 0 < 1 - 1 / (p : ℝ))).mp
  exact neg_two_mul_le_log_one_sub (by positivity) hx

theorem exp_neg_two_sum_le_euler_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Real.exp (-2 * ∑ p ∈ S, (1 / p : ℝ)) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  rw [mul_sum, Real.exp_sum]
  exact prod_le_prod (fun p _ ↦ (Real.exp_pos _).le)
    (fun p hp ↦ exp_neg_two_div_le_prime_factor p (hS p hp))

theorem euler_product_lower_of_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (B : ℝ) (hB : (∑ p ∈ S, (1 / p : ℝ)) ≤ B) :
    Real.exp (-2 * B) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  apply le_trans _ (exp_neg_two_sum_le_euler_product S hS)
  apply Real.exp_le_exp.mpr
  linarith

theorem totient_ratio_eq_euler_product (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have he := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at he
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hn.ne')).2
  simpa only [one_div, mul_comm] using he

end Erdos67.StationaryModel
