/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootPowerArithmetic

/-! # Explicit power budgets for the small initial supports -/

namespace Erdos207

theorem initial_support_unavailable_power
    (N t H K c : ℝ) (v : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t)
    (hH0 : 0 ≤ H) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c)
    (hH : H ≤ t ^ v) (hK : K ≤ t ^ v) (hc : c ≤ t) :
    (H ^ 2 * N + K ^ 3) * c ≤ t ^ (3 * v + 2) * N := by
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hp : t ^ (2 * v) ≤ t ^ (3 * v) :=
    pow_le_pow_right₀ ht1 (by omega)
  calc
    _ ≤ ((t ^ v) ^ 2 * N + (t ^ v) ^ 3) * t := by gcongr
    _ = (t ^ (2 * v) * N + t ^ (3 * v)) * t := by
      simp only [← pow_mul, Nat.mul_comm v]
    _ ≤ (t ^ (3 * v) * N + t ^ (3 * v) * N) * t := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (pow_nonneg ht0 (3 * v))
    _ = 2 * t ^ (3 * v + 1) * N := by rw [pow_succ]; ring
    _ ≤ t * t ^ (3 * v + 1) * N := by gcongr
    _ = _ := by rw [show 3 * v + 2 = (3 * v + 1) + 1 by omega, pow_succ]; ring

theorem initial_support_density_power
    (t : ℝ) (v : ℕ) (ht : 10 ≤ t) : 6 * t ^ v + 4 ≤ t ^ (v + 1) := by
  have hp : 1 ≤ t ^ v := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith only [hp, mul_nonneg (show 0 ≤ t - 10 by linarith) (show 0 ≤ t ^ v by linarith)]

theorem initial_support_pair_loss_power
    (N t : ℝ) (v s R : ℕ) (ht : 10 ≤ t)
    (hscale : t ^ R ≤ N) (hgap : v + s + 2 ≤ R) :
    3 * t ^ v + 2 ≤ N / (2 * t ^ s) := by
  have ht1 : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hp : 0 ≤ t ^ v := pow_nonneg htpos.le _
  have hloss : 3 * t ^ v + 2 ≤ t ^ (v + 1) := by
    have hd := initial_support_density_power t v ht
    linarith only [hd, hp]
  apply (le_div_iff₀ (by positivity : 0 < 2 * t ^ s)).mpr
  calc
    _ ≤ t ^ (v + 1) * (2 * t ^ s) := mul_le_mul_of_nonneg_right hloss (by positivity)
    _ = 2 * t ^ (v + s + 1) := by rw [pow_add, pow_add, pow_succ]; ring
    _ ≤ t * t ^ (v + s + 1) := by gcongr; linarith
    _ = t ^ (v + s + 2) := by rw [show v + s + 2 = (v + s + 1) + 1 by omega, pow_succ]; ring
    _ ≤ t ^ R := pow_le_pow_right₀ ht1 hgap
    _ ≤ N := hscale

end Erdos207
