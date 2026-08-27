import ErdosProblems.Erdos587.HooleyRankinWeights

/-!
# Local Euler factors for the Rankin divisor weight

Every truncated prime-power factor is bounded uniformly in the truncation.
The excess over one is proportional to `(p^β - 1)/p`, which is summable
over a bounded prime range when `β` is inversely proportional to its log.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_weighted_geometric_sum (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k) =
      20 - (4 * (m : ℝ) + 20) * (3 / 4 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma delta_weighted_geometric_sum_le (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k) ≤ 20 := by
  rw [delta_weighted_geometric_sum]
  have h : 0 ≤ (4 * (m : ℝ) + 20) * (3 / 4 : ℝ) ^ m := by positivity
  linarith

lemma delta_rankin_prime_ratio_le {p : ℕ} (hp : p.Prime) {β : ℝ} (hβ : β ≤ 1 / 2) :
    (p : ℝ) ^ β / p ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hs0 : 0 ≤ (p : ℝ) ^ β := Real.rpow_nonneg hp0.le _
  have hsq : ((p : ℝ) ^ β) ^ 2 ≤ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    calc
      _ ≤ (p : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
      _ = _ := Real.rpow_one _
  have hpSq : (p : ℝ) ≤ ((3 / 4 : ℝ) * p) ^ 2 := by nlinarith
  have hsle : (p : ℝ) ^ β ≤ (3 / 4 : ℝ) * p := by
    nlinarith only [hsq, hpSq, hs0, hp0]
  exact (div_le_iff₀ hp0).mpr hsle

lemma deltaRankinWeight_prime_pow_eq {p : ℕ} (hp : p.Prime) (k : ℕ) (β : ℝ) :
    deltaRankinWeight β (p ^ (k + 1)) =
      ((p : ℝ) ^ β - 1) * ((p : ℝ) ^ β) ^ k := by
  rw [deltaRankinWeight_prime_pow hp,
    ← Real.rpow_pow_comm (Nat.cast_nonneg p) β (k + 1),
    ← Real.rpow_pow_comm (Nat.cast_nonneg p) β k, pow_succ]
  ring

lemma delta_rankin_local_term {p : ℕ} (hp : p.Prime) (k : ℕ) (β : ℝ) :
    ((p ^ (k + 1)).divisors.card : ℝ) * deltaRankinWeight β (p ^ (k + 1)) /
      (p ^ (k + 1) : ℕ) =
        (((p : ℝ) ^ β - 1) / p) * ((k : ℝ) + 2) * ((p : ℝ) ^ β / p) ^ k := by
  have hcard : ((p ^ (k + 1)).divisors.card : ℝ) = (k : ℝ) + 2 := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    push_cast
    ring
  rw [hcard, deltaRankinWeight_prime_pow_eq hp, Nat.cast_pow, pow_succ, div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem delta_rankin_local_euler_le {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
      ((p ^ k).divisors.card : ℝ) * deltaRankinWeight β (p ^ k) / (p ^ k : ℕ)) ≤
        1 + 20 * (((p : ℝ) ^ β - 1) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs1 : (1 : ℝ) ≤ (p : ℝ) ^ β :=
    Real.one_le_rpow (by exact_mod_cast hp.one_le) hβ0
  have hcoef : 0 ≤ ((p : ℝ) ^ β - 1) / p := by positivity
  have hr0 : 0 ≤ (p : ℝ) ^ β / p := by positivity
  have hr := delta_rankin_prime_ratio_le hp hβ
  have hone : deltaRankinWeight β 1 = 1 := (deltaRankinWeight_isMultiplicative β).1
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, hone,
    mul_one, div_one]
  have hsum : (∑ k ∈ Finset.range m,
      ((p ^ (k + 1)).divisors.card : ℝ) * deltaRankinWeight β (p ^ (k + 1)) /
        (p ^ (k + 1) : ℕ)) ≤ 20 * (((p : ℝ) ^ β - 1) / p) := by
    calc
      _ ≤ ∑ k ∈ Finset.range m,
          (((p : ℝ) ^ β - 1) / p) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [delta_rankin_local_term hp]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr k) (by positivity)
      _ = (((p : ℝ) ^ β - 1) / p) *
          ∑ k ∈ Finset.range m, ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (((p : ℝ) ^ β - 1) / p) * 20 :=
        mul_le_mul_of_nonneg_left (delta_weighted_geometric_sum_le m) hcoef
      _ = _ := by ring
  linarith

end Erdos587
