/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RealPowerHierarchyArithmetic

/-! # Explicit ambient exponent gaps for coupled drift budgets -/

namespace Erdos207

theorem power_le_ambient_power_ratio
    (N t : ℝ) (R r u a : ℕ) (ht : 1 ≤ t) (_hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hgap : u + a ≤ R * r) :
    t ^ u ≤ N ^ r / t ^ a := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  apply (le_div_iff₀ (pow_pos htpos a)).mpr
  calc
    t ^ u * t ^ a = t ^ (u + a) := (pow_add _ _ _).symm
    _ ≤ t ^ (R * r) := pow_le_pow_right₀ ht hgap
    _ = (t ^ R) ^ r := pow_mul _ _ _
    _ ≤ N ^ r := pow_le_pow_left₀ (pow_nonneg htpos.le R) hscale r

theorem coeff_power_le_ambient_power_ratio
    (N t C : ℝ) (R r u a : ℕ) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hC : C ≤ t) (hgap : u + a + 1 ≤ R * r) :
    C * t ^ u ≤ N ^ r / t ^ a := by
  calc
    C * t ^ u ≤ t ^ (u + 1) := real_coeff_mul_pow_le_pow ht hC le_rfl
    _ ≤ _ := power_le_ambient_power_ratio N t R r (u + 1) a ht hN hscale (by omega)

theorem power_residual_clock_ge_base
    (N t L : ℝ) (R b : ℕ) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hgap : 2 * b + 1 ≤ 2 * R)
    (hL : N ^ 2 / t ^ (2 * b) ≤ L) : t ≤ L := by
  have h := power_le_ambient_power_ratio N t R 2 1 (2 * b) ht hN hscale (by omega)
  simp only [pow_one] at h
  exact h.trans hL

theorem power_crude_cutoff_le_error
    (N t e : ℝ) (R a k : ℕ) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hgap : k + a ≤ R) (he : N / t ^ a ≤ e) : t ^ k ≤ e := by
  have h := power_le_ambient_power_ratio N t R 1 k a ht hN hscale (by simpa using hgap)
  simp only [pow_one] at h
  exact h.trans he

theorem power_pair_le_clock_error
    (N t L e x : ℝ) (R a b : ℕ) (ht : 3 ≤ t) (hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hgap : 2 * b + a + 1 ≤ 2 * R)
    (hL : N ^ 2 / t ^ (2 * b) ≤ L) (he : N / t ^ a ≤ e) (hx : x ≤ 3 * N) :
    x ≤ L * e := by
  have htpos : 0 < t := by linarith
  have h := coeff_power_le_ambient_power_ratio N t 3 R 2 0 (2 * b + a)
    (by linarith) hN hscale ht (by omega)
  simp only [pow_zero, mul_one] at h
  have hprod := mul_le_mul_of_nonneg_left h hN
  have hL0 : 0 ≤ L := (div_nonneg (sq_nonneg N) (pow_nonneg htpos.le _)).trans hL
  have he0 : 0 ≤ N / t ^ a := div_nonneg hN (pow_nonneg htpos.le _)
  calc
    x ≤ 3 * N := hx
    _ ≤ N * (N ^ 2 / t ^ (2 * b + a)) := by simpa only [mul_comm N 3] using hprod
    _ = (N ^ 2 / t ^ (2 * b)) * (N / t ^ a) := by rw [pow_add]; ring
    _ ≤ L * e := mul_le_mul hL he he0 hL0

theorem power_initial_available_taylor_budget
    (N t E A : ℝ) (R a b : ℕ) (ht : 1 ≤ t) (hN : 0 ≤ N) (hE : 0 < E)
    (hscale : t ^ R ≤ N) (hgap : a + b ≤ 2 * R)
    (hEfloor : N ^ 2 / t ^ b ≤ E) (hA : A / E ≤ N) :
    A ≤ (N / t ^ a) * E ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hp := power_le_ambient_power_ratio N t R 2 a b ht hN hscale (by omega)
  have hpow : t ^ a ≤ E := hp.trans hEfloor
  have hmul : N * t ^ a ≤ N * E := mul_le_mul_of_nonneg_left hpow hN
  have hNE : N ≤ (N / t ^ a) * E := by
    apply (le_div_iff₀ (pow_pos htpos a)).mpr at hmul
    simpa only [div_mul_eq_mul_div] using hmul
  calc
    A ≤ N * E := (div_le_iff₀ hE).mp hA
    _ ≤ ((N / t ^ a) * E) * E := mul_le_mul_of_nonneg_right hNE hE.le
    _ = _ := by ring

theorem power_crude_overlap_le (t : ℝ) (k : ℕ) (ht : 16 ≤ t) :
    9 + 7 * t ^ k ≤ t ^ (k + 1) := by
  have hp : 1 ≤ t ^ k := one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
  calc
    9 + 7 * t ^ k ≤ 16 * t ^ k := by linarith
    _ ≤ t * t ^ k := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem ambient_succ_power_le_scale
    (N t : ℝ) (q z : ℕ) (hN : 1 ≤ N) (hconst : (2 : ℝ) ^ q ≤ t) (hz : z ≤ q) :
    (N + 1) ^ z ≤ t * N ^ z := by
  calc
    (N + 1) ^ z ≤ (2 * N) ^ z := by gcongr; linarith
    _ = (2 : ℝ) ^ z * N ^ z := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ q * N ^ z := by gcongr; norm_num
    _ ≤ t * N ^ z := mul_le_mul_of_nonneg_right hconst (by positivity)

theorem power_configuration_gain_budget
    (N t x h : ℝ) (R q z k a b : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N)
    (hscale : t ^ R ≤ N) (hconst : (2 : ℝ) ^ q ≤ t) (hz : z + 1 ≤ q)
    (hgap : k + a + 3 * b * (z + 1) + 2 ≤ R)
    (hx : N / t ^ (3 * b + 1) ≤ x)
    (hh : N ^ (z + 1) / t ^ (a + 3 * b * z) ≤ h) :
    (N + 1) ^ (z + 1) * t ^ k ≤ x * h := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hx0 : 0 ≤ x := (div_nonneg hN0 (pow_nonneg htpos.le _)).trans hx
  have hv := power_le_ambient_power_ratio N t R 1 (k + 1) (a + 3 * b * z + 3 * b + 1)
    ht hN0 hscale (by nlinarith)
  simp only [pow_one] at hv
  calc
    _ ≤ (t * N ^ (z + 1)) * t ^ k :=
      mul_le_mul_of_nonneg_right (ambient_succ_power_le_scale N t q (z + 1) hN hconst hz)
        (pow_nonneg htpos.le k)
    _ = N ^ (z + 1) * t ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ N ^ (z + 1) * (N / t ^ (a + 3 * b * z + 3 * b + 1)) :=
      mul_le_mul_of_nonneg_left hv (pow_nonneg hN0 _)
    _ = (N / t ^ (3 * b + 1)) * (N ^ (z + 1) / t ^ (a + 3 * b * z)) := by
      have hexp : a + 3 * b * z + 3 * b + 1 = (a + 3 * b * z) + (3 * b + 1) := by omega
      rw [hexp, pow_add]
      ring
    _ ≤ x * h := mul_le_mul hx hh (by positivity) hx0

end Erdos207
