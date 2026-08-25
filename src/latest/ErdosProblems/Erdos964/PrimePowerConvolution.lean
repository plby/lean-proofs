import ErdosProblems.Erdos964.ScalarMomentFunction

/-!
# Prime-power coefficients of the finite local correction
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem arithmeticFunction_mul_prime_pow (f g : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (f * g) (p ^ j) = ∑ i ∈ Finset.range (j + 1), f (p ^ i) * g (p ^ (j - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have hquot : p ^ j / p ^ i = p ^ (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega, pow_add]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.pos i)
  rw [hquot]

theorem arithmeticFunction_mul_prime_pow_of_linear (f g : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (hf : ∀ i : ℕ, 2 ≤ i → f (p ^ i) = 0) (j : ℕ) :
    (f * g) (p ^ (j + 1)) = f 1 * g (p ^ (j + 1)) + f p * g (p ^ j) := by
  rw [arithmeticFunction_mul_prime_pow f g hp, Finset.sum_range_succ']
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.zero_add, pow_one, Nat.add_sub_cancel, pow_zero, Nat.sub_zero]
    ring
  · intro i hi hi0
    rw [hf (i + 1) (by omega), zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem coprimeMobiusInvAF_prime (M : ℕ) {p : ℕ} (hp : p.Prime) :
    coprimeMobiusInvAF M p = if p ∣ M then 0 else -(1 : ℝ) / p := by
  rw [coprimeMobiusInvAF_apply]
  simp only [if_neg hp.ne_zero, hp.coprime_iff_not_dvd, ArithmeticFunction.moebius_apply_prime hp,
    Int.cast_neg, Int.cast_one]
  by_cases h : p ∣ M <;> simp [h]

theorem coprimeMobiusInvAF_prime_pow_ge_two (M : ℕ) {p j : ℕ}
    (hp : p.Prime) (hj : 2 ≤ j) : coprimeMobiusInvAF M (p ^ j) = 0 := by
  rw [coprimeMobiusInvAF_apply, if_neg (pow_ne_zero j hp.ne_zero)]
  have hmu := ArithmeticFunction.moebius_apply_prime_pow hp (show j ≠ 0 by omega)
  rw [if_neg (show j ≠ 1 by omega)] at hmu
  simp only [hmu, Int.cast_zero, zero_div, ite_self]

theorem coprimeMobiusInvAF_pow_prime_pow (M k j : ℕ) {p : ℕ} (hp : p.Prime) :
    (coprimeMobiusInvAF M ^ k : ArithmeticFunction ℝ) (p ^ j) =
      (Nat.choose k j : ℝ) * (coprimeMobiusInvAF M p) ^ j := by
  induction k generalizing j with
  | zero =>
      by_cases hj : j = 0
      · simp [hj]
      · have hpj : p ^ j ≠ 1 := by
          have hgt : 1 < p ^ j := one_lt_pow₀ hp.one_lt hj
          omega
        rw [pow_zero, ArithmeticFunction.one_apply, if_neg hpj,
          Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
        norm_num
  | succ k ih =>
      cases j with
      | zero =>
          have hOne := ((coprimeMobiusInvAF_isMultiplicative M).pow
            (k := k + 1)).map_one
          simpa only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using hOne
      | succ j =>
          rw [pow_succ', arithmeticFunction_mul_prime_pow_of_linear _ _ hp
            (fun i hi => coprimeMobiusInvAF_prime_pow_ge_two M hp hi)]
          rw [(coprimeMobiusInvAF_isMultiplicative M).map_one, one_mul, ih, ih,
            Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring

theorem scalarMomentCorrectionAF_prime_pow_succ (M k j : ℕ) {p : ℕ} (hp : p.Prime) :
    scalarMomentCorrectionAF M k (p ^ (j + 1)) =
      (Nat.choose k (j + 1) : ℝ) * (coprimeMobiusInvAF M p) ^ (j + 1) +
        scalarMomentAF M k p * ((Nat.choose k j : ℝ) * (coprimeMobiusInvAF M p) ^ j) := by
  rw [scalarMomentCorrectionAF, arithmeticFunction_mul_prime_pow_of_linear _ _ hp
    (fun i hi => scalarMomentAF_prime_pow_ge_two M k hp hi),
    (scalarMomentAF_multiplicative M k).map_one, one_mul,
    coprimeMobiusInvAF_pow_prime_pow M k (j + 1) hp,
    coprimeMobiusInvAF_pow_prime_pow M k j hp]

theorem scalarMomentCorrectionAF_prime_pow_eq_zero (M k j : ℕ) {p : ℕ}
    (hp : p.Prime) (hj : k + 1 < j) : scalarMomentCorrectionAF M k (p ^ j) = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  rw [scalarMomentCorrectionAF_prime_pow_succ M k i hp,
    Nat.choose_eq_zero_of_lt (show k < i + 1 by omega),
    Nat.choose_eq_zero_of_lt (show k < i by omega)]
  simp

end Erdos964
