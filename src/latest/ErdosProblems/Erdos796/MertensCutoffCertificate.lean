import ErdosProblems.Erdos796.BaselineAsymptotic
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite certificate for the Meissel--Mertens upper bound

This module verifies the cutoff-at-100 numerical inequality using only
kernel reduction, rational arithmetic, and Mathlib's proved logarithm bounds.
-/

namespace Erdos796

open Real Finset

private lemma log_ratio_cubic_lower {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    2 * (z + z ^ 3 / 3) ≤ log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz0 hz1 2
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_lower_from_pow_two (p k : ℕ) (hp : 0 < p) (hk : 2 ^ k ≤ p) :
    (k : ℝ) * log 2 +
        2 * (((p : ℝ) - 2 ^ k) / ((p : ℝ) + 2 ^ k) +
          ((((p : ℝ) - 2 ^ k) / ((p : ℝ) + 2 ^ k)) ^ 3) / 3) ≤
      log p := by
  let b : ℝ := (2 ^ k : ℕ)
  let z : ℝ := ((p : ℝ) - b) / ((p : ℝ) + b)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (0 : ℝ) < b := by simp [b]
  have hpb : b ≤ (p : ℝ) := by
    dsimp [b]
    exact_mod_cast hk
  have hden : 0 < (p : ℝ) + b := add_pos hpR hb
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (sub_nonneg.mpr hpb) hden.le
  have hz1 : z < 1 := by
    dsimp [z]
    rw [div_lt_one hden]
    linarith
  have hcubic := log_ratio_cubic_lower hz0 hz1
  have hratio : (1 + z) / (1 - z) = (p : ℝ) / b := by
    dsimp [z]
    field_simp [hpR.ne', hb.ne']
    ring
  rw [hratio, Real.log_div hpR.ne' hb.ne'] at hcubic
  have hlogb : log b = (k : ℝ) * log 2 := by
    simp [b, Nat.cast_pow, Real.log_pow]
  rw [hlogb] at hcubic
  dsimp [z, b] at hcubic ⊢
  push_cast at hcubic ⊢
  linarith

private def primes100 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97}

private lemma primesLE_100 : Nat.primesLE 100 = primes100 := by
  decide

private lemma filterPrimes_100 :
    (Finset.Ioc 0 100).filter Nat.Prime = primes100 := by
  decide

private lemma primeHarmonic_100_lt :
    (∑ p ∈ primes100, (p : ℝ)⁻¹) < (18029 : ℝ) / 10000 := by
  unfold primes100
  norm_num

private lemma log_100_eq :
    log 100 = 2 * (log 2 + log 5) := by
  calc
    log 100 = log ((2 : ℝ) ^ 2 * 5 ^ 2) := by norm_num
    _ = log ((2 : ℝ) ^ 2) + log ((5 : ℝ) ^ 2) := by
      rw [Real.log_mul] <;> norm_num
    _ = 2 * (log 2 + log 5) := by rw [Real.log_pow, Real.log_pow]; ring

private lemma log_log_100_gt :
    (15271 : ℝ) / 10000 < log (log 100) := by
  have hlog100 : (921 : ℝ) / 200 < log 100 := by
    rw [log_100_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  let z : ℝ := (121 : ℝ) / 1721
  have hz0 : (0 : ℝ) ≤ z := by positivity
  have hz1 : z < 1 := by norm_num [z]
  have hcubic := log_ratio_cubic_lower hz0 hz1
  have hratio : (1 + z) / (1 - z) = (921 : ℝ) / 800 := by
    norm_num [z]
  rw [hratio] at hcubic
  have hrational :
      (15271 : ℝ) / 10000 <
        2 * (6931471803 / 10000000000 : ℝ) + 2 * (z + z ^ 3 / 3) := by
    norm_num [z]
  have hlograt : (15271 : ℝ) / 10000 < log ((921 : ℝ) / 200) := by
    calc
      _ < 2 * log 2 + 2 * (z + z ^ 3 / 3) := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ log 4 + log ((921 : ℝ) / 800) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        linarith
      _ = log ((921 : ℝ) / 200) := by
        rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (by norm_num : (921 : ℝ) / 800 ≠ 0)]
        norm_num
  exact hlograt.trans (Real.log_lt_log (by norm_num) hlog100)

private lemma log_100_lt :
    log 100 < (2303 : ℝ) / 500 := by
  rw [log_100_eq]
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private lemma primeLogNumerator_100_lt :
    log 4 + 2 / 5 - (∑ p ∈ primes100, log p / p) <
      -(1582 : ℝ) / 1000 := by
  unfold primes100
  norm_num
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have h2 := log_lower_from_pow_two 2 1 (by norm_num) (by norm_num)
  have h3 := log_lower_from_pow_two 3 1 (by norm_num) (by norm_num)
  have h5 := log_lower_from_pow_two 5 2 (by norm_num) (by norm_num)
  have h7 := log_lower_from_pow_two 7 2 (by norm_num) (by norm_num)
  have h11 := log_lower_from_pow_two 11 3 (by norm_num) (by norm_num)
  have h13 := log_lower_from_pow_two 13 3 (by norm_num) (by norm_num)
  have h17 := log_lower_from_pow_two 17 4 (by norm_num) (by norm_num)
  have h19 := log_lower_from_pow_two 19 4 (by norm_num) (by norm_num)
  have h23 := log_lower_from_pow_two 23 4 (by norm_num) (by norm_num)
  have h29 := log_lower_from_pow_two 29 4 (by norm_num) (by norm_num)
  have h31 := log_lower_from_pow_two 31 4 (by norm_num) (by norm_num)
  have h37 := log_lower_from_pow_two 37 5 (by norm_num) (by norm_num)
  have h41 := log_lower_from_pow_two 41 5 (by norm_num) (by norm_num)
  have h43 := log_lower_from_pow_two 43 5 (by norm_num) (by norm_num)
  have h47 := log_lower_from_pow_two 47 5 (by norm_num) (by norm_num)
  have h53 := log_lower_from_pow_two 53 5 (by norm_num) (by norm_num)
  have h59 := log_lower_from_pow_two 59 5 (by norm_num) (by norm_num)
  have h61 := log_lower_from_pow_two 61 5 (by norm_num) (by norm_num)
  have h67 := log_lower_from_pow_two 67 6 (by norm_num) (by norm_num)
  have h71 := log_lower_from_pow_two 71 6 (by norm_num) (by norm_num)
  have h73 := log_lower_from_pow_two 73 6 (by norm_num) (by norm_num)
  have h79 := log_lower_from_pow_two 79 6 (by norm_num) (by norm_num)
  have h83 := log_lower_from_pow_two 83 6 (by norm_num) (by norm_num)
  have h89 := log_lower_from_pow_two 89 6 (by norm_num) (by norm_num)
  have h97 := log_lower_from_pow_two 97 6 (by norm_num) (by norm_num)
  norm_num at h2 h3 h5 h7 h11 h13 h17 h19 h23 h29 h31 h37 h41
  norm_num at h43 h47 h53 h59 h61 h67 h71 h73 h79 h83 h89 h97
  linarith [Real.log_two_gt_d9]

theorem finite_cutoff_100_lt :
    primeHarmonic 100 - log (log 100) - Mertens.E₁p 100 / log 100 +
        log 4 / log 100 + 2 / (5 * log 100) < (933 : ℝ) / 1000 := by
  rw [show primeHarmonic 100 = ∑ p ∈ primes100, (p : ℝ)⁻¹ by
    simp [primeHarmonic, primesLE_100]]
  simp only [Mertens.E₁p, Nat.floor_ofNat, filterPrimes_100]
  have hlog100 : (0 : ℝ) < log 100 := log_pos (by norm_num)
  have hratio :
      (log 4 + 2 / 5 - (∑ p ∈ primes100, log p / p)) / log 100 <
        -(3431 : ℝ) / 10000 := by
    rw [div_lt_iff₀ hlog100]
    nlinarith [primeLogNumerator_100_lt, log_100_lt]
  calc
    _ = (∑ p ∈ primes100, (p : ℝ)⁻¹) + 1 - log (log 100) +
        (log 4 + 2 / 5 - (∑ p ∈ primes100, log p / p)) / log 100 := by
          field_simp [hlog100.ne']
          ring
    _ < (18029 : ℝ) / 10000 + 1 - (15271 : ℝ) / 10000 -
        (3431 : ℝ) / 10000 := by
          linarith [primeHarmonic_100_lt, log_log_100_gt, hratio]
    _ < (933 : ℝ) / 1000 := by norm_num

/-- The same cutoff certificate with the two tail terms combined. -/
theorem finite_cutoff_100_combined_lt :
    primeHarmonic 100 - log (log 100) - Mertens.E₁p 100 / log 100 +
        (log 4 + 2 / 5) / log 100 < (933 : ℝ) / 1000 := by
  have hlog100 : log (100 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  convert! finite_cutoff_100_lt using 1
  field_simp [hlog100]
  ring

end Erdos796
