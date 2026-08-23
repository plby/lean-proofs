/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An exponential bound for `lcm (1, ..., h)`

This module records fixed-base exponential upper bounds for `Nat.lcmUpto`.
The elementary binomial-coefficient argument below gives the sharp convenient
base `4` needed in the auxiliary-polynomial estimates.  We also retain the
earlier analytic bound with the deliberately generous constant `512`:
Mathlib's explicit Chebyshev bound gives

`log (Nat.lcmUpto h) ≤ (log 4 + 4) * h`.

Since `exp (log 4 + 4) = 4 * exp 4 < 4 * 3 ^ 4 < 512`, exponentiation gives
the required integral estimate.  A fixed base, rather than the sharpest
constant, is what is needed in the auxiliary-polynomial estimates for
Erdős 240.
-/

namespace Erdos240.LcmBound

open Finset

/-- The fixed real exponential base obtained from Mathlib's explicit
Chebyshev estimate is at most `512`. -/
theorem exp_log_four_add_four_le :
    Real.exp (Real.log 4 + 4) ≤ (512 : ℝ) := by
  have hexpFour : Real.exp 4 ≤ (3 : ℝ) ^ 4 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      _ ≤ (3 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  calc
    Real.exp (Real.log 4 + 4) = 4 * Real.exp 4 := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ 4 * (3 : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hexpFour (by norm_num)
    _ ≤ (512 : ℝ) := by norm_num

/-- Real-valued form of the exponential lcm bound. -/
theorem cast_lcmUpto_le (h : ℕ) :
    (Nat.lcmUpto h : ℝ) ≤ (512 : ℝ) ^ h := by
  have hlog :
      Real.log (Nat.lcmUpto h) ≤
        (Real.log 4 + 4) * (h : ℝ) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos h)] at hexp
  calc
    (Nat.lcmUpto h : ℝ)
        ≤ Real.exp ((Real.log 4 + 4) * (h : ℝ)) := hexp
    _ = Real.exp (Real.log 4 + 4) ^ h := by
      rw [mul_comm, Real.exp_nat_mul]
    _ ≤ (512 : ℝ) ^ h :=
      pow_le_pow_left₀ (Real.exp_pos _).le exp_log_four_add_four_le h

/-- A fixed-base integral exponential bound for the least common multiple
of all positive integers at most `h`. -/
theorem lcmUpto_le (h : ℕ) :
    Nat.lcmUpto h ≤ 512 ^ h := by
  exact_mod_cast cast_lcmUpto_le h

/-! ## The elementary base-four bound -/

/-- If the base-`p` logarithm rises between `n` and `2n`, the last digit
position supplies a carry in Kummer's formula for the central binomial
coefficient. -/
theorem log_le_factorization_choose_add_log_even
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    p.log (2 * n) ≤ (Nat.choose (2 * n) n).factorization p + p.log n := by
  have hlog_step : p.log (2 * n) ≤ p.log n + 1 := by
    calc
      p.log (2 * n) ≤ p.log (n * p) :=
        Nat.log_mono_right (by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp.two_le)
      _ = p.log n + 1 := Nat.log_mul_base hp.one_lt hn.ne'
  by_cases hsame : p.log (2 * n) ≤ p.log n
  · omega
  have hltlog : p.log n < p.log (2 * n) := Nat.lt_of_not_ge hsame
  have hpow_le : p ^ p.log (2 * n) ≤ 2 * n :=
    Nat.pow_log_le_self p (by omega)
  have hn_lt_pow : n < p ^ p.log (2 * n) :=
    Nat.lt_pow_of_log_lt hp.one_lt hltlog
  have ha_mem : p.log (2 * n) ∈ Finset.Ico 1 (p.log (2 * n) + 1) := by
    simp only [Finset.mem_Ico]
    constructor
    · by_contra ha
      have ha0 : p.log (2 * n) = 0 := Nat.eq_zero_of_not_pos ha
      omega
    · omega
  have hcarry : p.log (2 * n) ∈
      (Finset.Ico 1 (p.log (2 * n) + 1)).filter
        (fun i ↦ p ^ i ≤ n % p ^ i + (2 * n - n) % p ^ i) := by
    simp only [Finset.mem_filter]
    refine ⟨ha_mem, ?_⟩
    rw [Nat.mod_eq_of_lt hn_lt_pow, show 2 * n - n = n by omega,
      Nat.mod_eq_of_lt hn_lt_pow]
    omega
  have hfac : 1 ≤ (Nat.choose (2 * n) n).factorization p := by
    rw [Nat.factorization_choose hp (by omega) (Nat.lt_succ_self _)]
    exact Finset.one_le_card.mpr ⟨_, hcarry⟩
  omega

/-- The lcm at an even argument divides a central binomial coefficient times
the lcm at half the argument. -/
theorem lcmUpto_two_mul_dvd (n : ℕ) :
    Nat.lcmUpto (2 * n) ∣ Nat.choose (2 * n) n * Nat.lcmUpto n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [Nat.lcmUpto]
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
      (Nat.mul_ne_zero (Nat.choose_ne_zero (by omega)) (Nat.lcmUpto_ne_zero _))]
  intro p hp
  rw [Nat.factorization_lcmUpto _ hp,
    Nat.factorization_mul (Nat.choose_ne_zero (by omega)) (Nat.lcmUpto_ne_zero _),
    Finsupp.add_apply, Nat.factorization_lcmUpto _ hp]
  exact log_le_factorization_choose_add_log_even hp hn

/-- Odd analogue of `log_le_factorization_choose_add_log_even`. -/
theorem log_le_factorization_choose_add_log_odd
    {p n : ℕ} (hp : p.Prime) :
    p.log (2 * n + 1) ≤
      (Nat.choose (2 * n + 1) n).factorization p + p.log (n + 1) := by
  have hlog_step : p.log (2 * n + 1) ≤ p.log (n + 1) + 1 := by
    calc
      p.log (2 * n + 1) ≤ p.log ((n + 1) * p) :=
        Nat.log_mono_right (by nlinarith [hp.two_le])
      _ = p.log (n + 1) + 1 :=
        Nat.log_mul_base hp.one_lt (Nat.succ_ne_zero n)
  by_cases hsame : p.log (2 * n + 1) ≤ p.log (n + 1)
  · omega
  have hltlog : p.log (n + 1) < p.log (2 * n + 1) := Nat.lt_of_not_ge hsame
  have hpow_le : p ^ p.log (2 * n + 1) ≤ 2 * n + 1 :=
    Nat.pow_log_le_self p (by omega)
  have hn1_lt_pow : n + 1 < p ^ p.log (2 * n + 1) :=
    Nat.lt_pow_of_log_lt hp.one_lt hltlog
  have ha_mem : p.log (2 * n + 1) ∈
      Finset.Ico 1 (p.log (2 * n + 1) + 1) := by
    simp only [Finset.mem_Ico]
    constructor
    · by_contra ha
      have ha0 : p.log (2 * n + 1) = 0 := Nat.eq_zero_of_not_pos ha
      omega
    · omega
  have hcarry : p.log (2 * n + 1) ∈
      (Finset.Ico 1 (p.log (2 * n + 1) + 1)).filter
        (fun i ↦ p ^ i ≤ n % p ^ i + (2 * n + 1 - n) % p ^ i) := by
    simp only [Finset.mem_filter]
    refine ⟨ha_mem, ?_⟩
    rw [Nat.mod_eq_of_lt (lt_trans (by omega) hn1_lt_pow),
      show 2 * n + 1 - n = n + 1 by omega,
      Nat.mod_eq_of_lt hn1_lt_pow]
    omega
  have hfac : 1 ≤ (Nat.choose (2 * n + 1) n).factorization p := by
    rw [Nat.factorization_choose hp (by omega) (Nat.lt_succ_self _)]
    exact Finset.one_le_card.mpr ⟨_, hcarry⟩
  omega

/-- The lcm at an odd argument divides the adjacent binomial coefficient
times the lcm at the rounded-up half argument. -/
theorem lcmUpto_two_mul_add_one_dvd (n : ℕ) :
    Nat.lcmUpto (2 * n + 1) ∣
      Nat.choose (2 * n + 1) n * Nat.lcmUpto (n + 1) := by
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
      (Nat.mul_ne_zero (Nat.choose_ne_zero (by omega)) (Nat.lcmUpto_ne_zero _))]
  intro p hp
  rw [Nat.factorization_lcmUpto _ hp,
    Nat.factorization_mul (Nat.choose_ne_zero (by omega)) (Nat.lcmUpto_ne_zero _),
    Finsupp.add_apply, Nat.factorization_lcmUpto _ hp]
  exact log_le_factorization_choose_add_log_odd hp

/-- The quantitatively sharp elementary estimate used in the source proof:
the least common multiple of `1, ..., h` is at most `4 ^ h`. -/
theorem lcmUpto_le_four_pow (h : ℕ) : Nat.lcmUpto h ≤ 4 ^ h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
      obtain ⟨n, hh | hh⟩ := Nat.even_or_odd' h
      · subst h
        obtain rfl | hn := n.eq_zero_or_pos
        · simp [Nat.lcmUpto]
        have hrec : Nat.lcmUpto (2 * n) ≤
            Nat.choose (2 * n) n * Nat.lcmUpto n :=
          Nat.le_of_dvd
            (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.lcmUpto_pos n))
            (lcmUpto_two_mul_dvd n)
        calc
          Nat.lcmUpto (2 * n) ≤
              Nat.choose (2 * n) n * Nat.lcmUpto n := hrec
          _ ≤ 2 ^ (2 * n) * 4 ^ n :=
            Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (ih n (by omega))
          _ = 4 ^ (2 * n) := by
            simp only [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
            congr 1
            omega
      · subst h
        obtain rfl | hn := n.eq_zero_or_pos
        · norm_num [Nat.lcmUpto]
        have hrec : Nat.lcmUpto (2 * n + 1) ≤
            Nat.choose (2 * n + 1) n * Nat.lcmUpto (n + 1) :=
          Nat.le_of_dvd
            (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.lcmUpto_pos (n + 1)))
            (lcmUpto_two_mul_add_one_dvd n)
        calc
          Nat.lcmUpto (2 * n + 1) ≤
              Nat.choose (2 * n + 1) n * Nat.lcmUpto (n + 1) := hrec
          _ ≤ 2 ^ (2 * n) * 4 ^ (n + 1) :=
            Nat.mul_le_mul (Nat.choose_succ_le_two_pow (2 * n) n)
              (ih (n + 1) (by omega))
          _ = 4 ^ (2 * n + 1) := by
            simp only [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
            congr 1
            omega

#print axioms Erdos240.LcmBound.lcmUpto_le
#print axioms Erdos240.LcmBound.lcmUpto_le_four_pow

end Erdos240.LcmBound
