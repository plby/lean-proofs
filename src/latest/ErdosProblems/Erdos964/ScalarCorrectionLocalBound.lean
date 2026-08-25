import ErdosProblems.Erdos964.ScalarCorrectionLocalSum
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Absolute local bounds for the scalar Euler corrections

The first prime coefficient cancels to order `p⁻²`. All remaining local
coefficients already have that order, and only finitely many occur.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem choose_cast_le_eight (k j : ℕ) (hk : k ≤ 3) : (Nat.choose k j : ℝ) ≤ 8 := by
  have h := (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk)
  exact_mod_cast h

theorem scalarMomentCorrectionAF_prime_pow_good_bound (M k j : ℕ) (hk : k ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (hpM : ¬p ∣ M) :
    |scalarMomentCorrectionAF M k (p ^ (j + 1))| ≤ 104 / (p : ℝ) ^ 2 := by
  let u : ℝ := 1 / p
  let a : ℝ := (k : ℝ) / ((p : ℝ) - 3)
  have hp4R : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (0 : ℝ) < (p : ℝ) - 3 := by linarith
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; exact div_le_self (by norm_num) (by linarith)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hau : a ≤ 12 * u := by
    dsimp only [a, u]
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ hp3R hpR]
    nlinarith [mul_le_mul_of_nonneg_right hkR hpR.le]
  rw [scalarMomentCorrectionAF_prime_pow_succ M k j hp,
    coprimeMobiusInvAF_prime M hp, scalarMomentAF_prime M k hp, if_neg hpM, if_neg hpM]
  simp only [neg_div]
  change |(Nat.choose k (j + 1) : ℝ) * (-u) ^ (j + 1) +
    a * ((Nat.choose k j : ℝ) * (-u) ^ j)| ≤ 104 / (p : ℝ) ^ 2
  have htarget : (104 : ℝ) / (p : ℝ) ^ 2 = 104 * u ^ 2 := by dsimp only [u]; ring
  rw [htarget]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.zero_add, Nat.choose_one_right, Nat.choose_zero_right,
      Nat.cast_one, pow_one, pow_zero, mul_one]
    have hid : (k : ℝ) * (-u) + a = 3 * a * u := by
      dsimp only [a, u]
      field_simp
      ring
    rw [hid, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hau hu, sq_nonneg u]
  · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj
    have hpow2 : u ^ (j + 1) ≤ u ^ 2 := pow_le_pow_of_le_one hu hu1 (by omega)
    have hpow1 : u ^ j ≤ u := by simpa only [pow_one] using pow_le_pow_of_le_one hu hu1 hj1
    have hterm1 : (Nat.choose k (j + 1) : ℝ) * u ^ (j + 1) ≤ 8 * u ^ 2 :=
      mul_le_mul (choose_cast_le_eight k (j + 1) hk) hpow2 (by positivity) (by norm_num)
    have hterm2 : a * ((Nat.choose k j : ℝ) * u ^ j) ≤ (12 * u) * (8 * u) :=
      mul_le_mul hau (mul_le_mul (choose_cast_le_eight k j hk) hpow1
        (by positivity) (by norm_num)) (by positivity) (by positivity)
    calc
      _ ≤ |(Nat.choose k (j + 1) : ℝ) * (-u) ^ (j + 1)| +
          |a * ((Nat.choose k j : ℝ) * (-u) ^ j)| := abs_add_le _ _
      _ = (Nat.choose k (j + 1) : ℝ) * u ^ (j + 1) +
          a * ((Nat.choose k j : ℝ) * u ^ j) := by
        simp only [abs_mul, abs_pow, abs_neg, abs_of_nonneg hu, abs_of_nonneg ha,
          abs_of_nonneg (show (0 : ℝ) ≤ Nat.choose k j by positivity),
          abs_of_nonneg (show (0 : ℝ) ≤ Nat.choose k (j + 1) by positivity)]
      _ ≤ 104 * u ^ 2 := by nlinarith [hterm1, hterm2]

theorem scalarMomentCorrectionAF_prime_pow_bad (M k j : ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p ∣ M) : scalarMomentCorrectionAF M k (p ^ (j + 1)) = 0 := by
  rw [scalarMomentCorrectionAF_prime_pow_succ M k j hp,
    coprimeMobiusInvAF_prime M hp, scalarMomentAF_prime M k hp, if_pos hpM, if_pos hpM]
  simp

theorem scalarMomentCorrectionAF_local_abs_tsum_le (M k : ℕ) (hk : k ≤ 3)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, |scalarMomentCorrectionAF M k (p ^ j)|) ≤ 1 + 416 / (p : ℝ) ^ 2 := by
  have hterm (j : ℕ) : |scalarMomentCorrectionAF M k (p ^ (j + 1))| ≤ 104 / (p : ℝ) ^ 2 := by
    by_cases h : p ∣ M
    · rw [scalarMomentCorrectionAF_prime_pow_bad M k j hp h, abs_zero]
      positivity
    · have hp2 : p ≠ 2 := fun heq => h (heq ▸ h2M)
      have hp3 : p ≠ 3 := fun heq => h (heq ▸ h3M)
      exact scalarMomentCorrectionAF_prime_pow_good_bound M k j hk hp
        (by have := hp.two_le; omega) h
  rw [tsum_eq_sum (s := Finset.range (k + 2)) (fun j hj => by
    rw [scalarMomentCorrectionAF_prime_pow_eq_zero M k j hp
      (by simp only [Finset.mem_range] at hj; omega), abs_zero])]
  rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [pow_zero, (scalarMomentCorrectionAF_multiplicative M k).map_one, abs_one]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (k + 1)) => hterm j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hsmall : ((k : ℝ) + 1) * (104 / (p : ℝ) ^ 2) ≤ 4 * (104 / (p : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc
    _ ≤ 4 * (104 / (p : ℝ) ^ 2) + 1 := by linarith [hsum, hsmall]
    _ = _ := by ring

end Erdos964
