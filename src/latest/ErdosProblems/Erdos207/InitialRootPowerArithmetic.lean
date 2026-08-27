/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets

/-! # Power budgets for initial rooted perturbations -/

namespace Erdos207

theorem initial_three_errors_power
    (N t x y w : ℝ) (q u z : ℕ) (hN : 1 ≤ N) (ht : 3 ≤ t)
    (hconst : (2 : ℝ) ^ q ≤ t) (hz : 1 ≤ z) (hzq : z ≤ q)
    (hx : x ≤ t ^ u) (hy : y ≤ t ^ u * N) (hw : w ≤ t ^ u) :
    x * (N + 1) ^ z + y * (N + 1) ^ (z - 1) + w * (N + 1) ^ z ≤ N ^ z * t ^ (u + 2) := by
  have hN0 : 0 ≤ N := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpow := ambient_succ_power_le_scale N t q z hN hconst hzq
  have hprev := ambient_succ_power_le_scale N t q (z - 1) hN hconst (by omega)
  have hxbound : x * (N + 1) ^ z ≤ N ^ z * t ^ (u + 1) := by
    calc
      _ ≤ t ^ u * (t * N ^ z) := mul_le_mul hx hpow (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hwbound : w * (N + 1) ^ z ≤ N ^ z * t ^ (u + 1) := by
    calc
      _ ≤ t ^ u * (t * N ^ z) := mul_le_mul hw hpow (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hNpow : N * N ^ (z - 1) = N ^ z := by
    rw [← pow_succ']
    congr 1
    omega
  have hybound : y * (N + 1) ^ (z - 1) ≤ N ^ z * t ^ (u + 1) := by
    calc
      _ ≤ (t ^ u * N) * (t * N ^ (z - 1)) := mul_le_mul hy hprev (by positivity) (by positivity)
      _ = (N * N ^ (z - 1)) * t ^ (u + 1) := by rw [pow_succ]; ring
      _ = _ := by rw [hNpow]
  calc
    _ ≤ 3 * (N ^ z * t ^ (u + 1)) := by linarith only [hxbound, hybound, hwbound]
    _ ≤ t * (N ^ z * t ^ (u + 1)) := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by rw [show u + 2 = (u + 1) + 1 by omega, pow_succ]; ring

theorem initial_error_power_budget
    (N t w e : ℝ) (q R d u s b : ℕ)
    (hN : 0 ≤ N) (ht : 1 ≤ t) (hd : 1 ≤ d) (hdq : d ≤ q)
    (hscale : t ^ R ≤ N) (hgap : u + s + b * q ≤ R)
    (hratio : N / t ^ b ≤ w) (he : e ≤ N ^ (d - 1) * t ^ u) :
    e ≤ (1 / t ^ s) * w ^ d := by
  have htpos : 0 < t := by linarith
  have hw0 : 0 ≤ w := (div_nonneg hN (pow_nonneg htpos.le b)).trans hratio
  have hpower : t ^ u ≤ N / t ^ (s + b * q) :=
    power_crude_cutoff_le_error N t (N / t ^ (s + b * q)) R (s + b * q) u ht hN hscale (by omega) le_rfl
  have hNpow : N ^ (d - 1) * N = N ^ d := by rw [← pow_succ]; congr 1; omega
  calc
    e ≤ N ^ (d - 1) * t ^ u := he
    _ ≤ N ^ (d - 1) * (N / t ^ (s + b * q)) := mul_le_mul_of_nonneg_left hpower (pow_nonneg hN _)
    _ = N ^ d / t ^ (s + b * q) := by rw [← mul_div_assoc, hNpow]
    _ ≤ N ^ d / t ^ (s + b * d) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hN _) (by positivity)
      exact pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_left b hdq) s)
    _ = (1 / t ^ s) * (N / t ^ b) ^ d := by rw [pow_add, pow_mul, div_pow]; ring
    _ ≤ (1 / t ^ s) * w ^ d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hratio d) (by positivity)

end Erdos207
