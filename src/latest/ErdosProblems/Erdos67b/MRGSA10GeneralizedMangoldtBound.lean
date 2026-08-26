import ErdosProblems.Erdos67b.MRGSA10GeneralizedMangoldtSupport
import ErdosProblems.Erdos67b.MRGSA10HighMangoldtSupport

/-!
# A geometric prime-power bound for generalized Mangoldt coefficients

For an arbitrary one-bounded multiplicative coefficient the generalized
Mangoldt coefficient need not equal `a(n) * Λ(n)` at higher prime powers.
The finite convolution identity nevertheless gives the sharp elementary
majorant `(2^k - 1) log p` at `p^k`.  The factor `2^k` is precisely the
geometric loss absorbed by the doubled real shift in the second GS A.10
secondary term.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Prime-power form of `Λ_a * a = a · log`, with the final summand
isolated. -/
theorem sum_gsGeneralizedMangoldt_prime_pow_add_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (ha1 : a 1 = 1) (p k : ℕ) (hp : p.Prime) :
    (∑ j ∈ Finset.range k,
      gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ (k - j))) +
        gsGeneralizedMangoldt a ha (p ^ k) =
      a (p ^ k) * ((k : ℝ) * Real.log p : ℂ) := by
  have hconv := sum_gsGeneralizedMangoldt_mul_self a ha (p ^ k)
  rw [Nat.sum_divisorsAntidiagonal (fun x y ↦
      gsGeneralizedMangoldt a ha x * a y),
    Nat.sum_divisors_prime_pow hp] at hconv
  have hsum :
      (∑ j ∈ Finset.range (k + 1),
        gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ k / p ^ j)) =
      ∑ j ∈ Finset.range (k + 1),
        gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ (k - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.pow_div
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hp.pos]
  rw [hsum] at hconv
  rw [Finset.sum_range_succ] at hconv
  rw [show k - k = 0 by omega, pow_zero, ha1, mul_one] at hconv
  rw [Nat.cast_pow, Real.log_pow] at hconv
  simpa using hconv

/-- A one-bounded arithmetic coefficient has generalized Mangoldt value at
`p^k` at most `(2^k - 1) log p`.  No complete multiplicativity is used. -/
theorem norm_gsGeneralizedMangoldt_prime_pow_le_geometric
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (ha1 : a 1 = 1)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (p k : ℕ) (hp : p.Prime) :
    ‖gsGeneralizedMangoldt a ha (p ^ k)‖ ≤
      ((2 : ℝ) ^ k - 1) * Real.log p := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k = 0
      · subst k
        simp [gsGeneralizedMangoldt_one]
      · have hrec := sum_gsGeneralizedMangoldt_prime_pow_add_self
          a ha ha1 p k hp
        have hp1R : (1 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.one_lt.le
        have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
        have heq :
            gsGeneralizedMangoldt a ha (p ^ k) =
              a (p ^ k) * ((k : ℝ) * Real.log p : ℂ) -
                ∑ j ∈ Finset.range k,
                  gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ (k - j)) := by
          linear_combination hrec
        rw [heq]
        calc
          ‖a (p ^ k) * ((k : ℝ) * Real.log p : ℂ) -
              ∑ j ∈ Finset.range k,
                gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ (k - j))‖ ≤
              ‖a (p ^ k) * ((k : ℝ) * Real.log p : ℂ)‖ +
                ‖∑ j ∈ Finset.range k,
                  gsGeneralizedMangoldt a ha (p ^ j) * a (p ^ (k - j))‖ :=
            norm_sub_le _ _
          _ ≤ (k : ℝ) * Real.log p +
              ∑ j ∈ Finset.range k,
                (((2 : ℝ) ^ j - 1) * Real.log p) := by
            gcongr
            · rw [norm_mul, norm_mul]
              simp only [Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hlogp]
              exact mul_le_of_le_one_left
                (mul_nonneg (Nat.cast_nonneg _) hlogp)
                (hbound _ (pow_pos hp.pos _))
            · refine (norm_sum_le _ _).trans ?_
              apply Finset.sum_le_sum
              intro j hj
              rw [norm_mul]
              have hjk : j < k := Finset.mem_range.mp hj
              have hpowpos : 0 < p ^ (k - j) := pow_pos hp.pos _
              calc
                ‖gsGeneralizedMangoldt a ha (p ^ j)‖ *
                    ‖a (p ^ (k - j))‖ ≤
                    ‖gsGeneralizedMangoldt a ha (p ^ j)‖ * 1 :=
                  mul_le_mul_of_nonneg_left (hbound _ hpowpos) (norm_nonneg _)
                _ = ‖gsGeneralizedMangoldt a ha (p ^ j)‖ := by ring
                _ ≤ ((2 : ℝ) ^ j - 1) * Real.log p := ih j hjk
          _ = ((2 : ℝ) ^ k - 1) * Real.log p := by
            rw [← Finset.sum_mul, ← add_mul]
            congr 1
            rw [add_comm]
            rw [Finset.sum_sub_distrib,
              geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring

/-- The actual high-prime generalized Mangoldt coefficient satisfies the
same geometric prime-power bound for an ordinary multiplicative `f`. -/
theorem norm_gsA9HighGeneralizedMangoldt_prime_pow_le_geometric
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y p k : ℕ) (hp : p.Prime) :
    ‖gsA9HighGeneralizedMangoldt hmul y (p ^ k)‖ ≤
      ((2 : ℝ) ^ k - 1) * Real.log p := by
  apply norm_gsGeneralizedMangoldt_prime_pow_le_geometric
      (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
      (gsA9HighArithmetic_one hmul y) ?_ p k hp
  intro n hn
  rw [gsA9HighArithmetic_apply_of_ne_zero f y hn.ne']
  exact norm_primeBandCoefficient_le_one hbound _ hn

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.norm_gsGeneralizedMangoldt_prime_pow_le_geometric
#print axioms Erdos67b.MRHalaszBands.norm_gsA9HighGeneralizedMangoldt_prime_pow_le_geometric
