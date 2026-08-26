import ErdosProblems.Erdos421.ZetaTruncation
import ErdosProblems.Erdos421.PowerSavingAsymptotics

/-! # Bounding the explicit zeta truncation errors at a quadratic cutoff -/

namespace Erdos421

theorem logarithmicSavingExponent_le_half (R : ℕ) {K : ℕ} (hK : 2 ≤ K) :
    logarithmicSavingExponent R K ≤ 1 / 2 := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (1 : ℝ) ≤ ((2 ^ R : ℕ) : ℝ) := by exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 2))
  unfold logarithmicSavingExponent
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)

/-- The tail error is bounded independently of the height when the cutoff
is at least one quarter of the square of an upper bound for the height. -/
theorem zeta_tail_error_le_eight {N : ℕ} (hN : 0 < N) {B : ℝ} (hB : 2 ≤ B)
    (hBN : B ^ 2 ≤ 4 * N) (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1)
    (ht : |s.im| ≤ B) :
    ‖s‖ / s.re * (N : ℝ) ^ (-s.re) ≤ 8 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsp : 0 < s.re := by linarith
  have hpow : 0 < (N : ℝ) ^ s.re := Real.rpow_pos_of_pos hNp _
  have hNpow : (N : ℝ) ≤ ((N : ℝ) ^ s.re) ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 ≤ s.re * (2 : ℕ) by norm_num; linarith)
    simpa only [Real.rpow_one, Real.rpow_mul_natCast hNp.le] using h
  have hBpow : B ≤ 2 * (N : ℝ) ^ s.re := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith
  have hsnorm : ‖s‖ ≤ 2 * B := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hsp.le] at h
    linarith
  have hquot : ‖s‖ / s.re ≤ 4 * B := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith
  rw [Real.rpow_neg hNp.le, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpow).mpr
  linarith

theorem zeta_pole_term_le_one {N : ℕ} (hN : 0 < N) (s : ℂ)
    (ht : (N : ℝ) ^ (1 - s.re) ≤ |s.im|) :
    (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 1 := by
  have hp : 0 < (N : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have him : |s.im| ≤ ‖s - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1)
  exact (div_le_one (hp.trans_le (ht.trans him))).mpr (ht.trans him)

theorem quadratic_dyadic_cutoff {V : ℕ} (hV : 0 < V) :
    (((2 ^ V : ℕ) : ℝ)) ^ 2 ≤ 4 * ((2 ^ (2 * V) - 1 : ℕ) : ℝ) := by
  have hv : 2 ≤ 2 ^ V := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2) hV
  have hpow : 2 ^ (2 * V) = (2 ^ V : ℕ) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hn : 1 ≤ (2 ^ V : ℕ) ^ 2 := one_le_pow₀ (by omega)
  rw [hpow, Nat.cast_sub hn, Nat.cast_one]
  have hvr : (2 : ℝ) ≤ (2 ^ V : ℕ) := by exact_mod_cast hv
  push_cast at hvr ⊢
  nlinarith

end Erdos421
