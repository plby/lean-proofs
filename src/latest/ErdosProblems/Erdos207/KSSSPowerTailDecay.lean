/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicGeometricDecay
import ErdosProblems.Erdos207.KSSSPowerExponentChoice

/-! # The sum of the two actual failure bounds tends to zero -/

namespace Erdos207

theorem coupled_failure_coefficient_le (q N : ℕ) :
    2 * (N ^ 2 + (q + 1) ^ 2 * N ^ 3) + 4 * (q + 1) ^ 2 * (N + 1) ^ 6 ≤
      8 * (q + 1) ^ 2 * (N + 1) ^ 6 := by
  have h2 : N ^ 2 ≤ (N + 1) ^ 6 :=
    (Nat.pow_le_pow_left (Nat.le_succ N) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : N ^ 3 ≤ (N + 1) ^ 6 :=
    (Nat.pow_le_pow_left (Nat.le_succ N) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have ha : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2' : N ^ 2 ≤ (q + 1) ^ 2 * (N + 1) ^ 6 := by nlinarith
  have h3' := Nat.mul_le_mul_left ((q + 1) ^ 2) h3
  nlinarith only [h2', h3']

theorem eventually_coupled_power_failure_lt
    (q R : ℕ) (epsilon : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
        4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6) *
          (1 / 2 : ℝ) ^ dyadicPowerScale R N < epsilon := by
  obtain ⟨N₀, hN₀⟩ := eventually_polynomial_dyadic_geometric_lt R 6
    (8 * (q + 1 : ℝ) ^ 2) epsilon hR (by positivity) hepsilon
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have hcoef : 2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
      4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 ≤
        8 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 := by
    exact_mod_cast coupled_failure_coefficient_le q N
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans_lt (hN₀ N hN)

theorem eventually_ksss_coupled_failure_lt_one (q b B k Rmin : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
        4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6) *
          (1 / 2 : ℝ) ^ dyadicPowerScale (ksssPowerDenominatorExponent q b B k Rmin) N < 1 :=
  eventually_coupled_power_failure_lt q (ksssPowerDenominatorExponent q b B k Rmin) 1
    (ksss_power_exponent_hierarchy q b B k Rmin).2.2.2.2.2.2.2.2.2 (by norm_num)

end Erdos207
