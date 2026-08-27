/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSInitialMargins
import ErdosProblems.Erdos207.PowerConcentrationOptimization

/-! # A common initial-margin exponent for every trajectory index -/

namespace Erdos207

noncomputable section

def ksssTrajectoryDimension {V : Type*} [DecidableEq V] {q : ℕ} : KSSSTrajectoryIndex V q → ℕ
  | .inl _ => 0
  | .inr (i, _) => i.order - 4 - i.chosen

theorem ksssTrajectoryDimension_le {V : Type*} [DecidableEq V] {q : ℕ}
    (i : KSSSTrajectoryIndex V q) : ksssTrajectoryDimension i ≤ q := by
  rcases i with P | ⟨i, T⟩
  · exact Nat.zero_le _
  · dsimp only [ksssTrajectoryDimension]
    have hi := i.order_le
    omega

theorem ksssInitialMargin_eq_dimension_power
    {V : Type*} [DecidableEq V] {q : ℕ} (E A margin : ℝ) (i : KSSSTrajectoryIndex V q) :
    ksssInitialMargin E A margin i = margin * (A / E) ^ ksssTrajectoryDimension i := by
  rcases i with P | ⟨i, T⟩ <;> simp only [ksssInitialMargin, ksssTrajectoryDimension, pow_zero, mul_one]

theorem initial_margin_power_lower
    (N t w : ℝ) (a b q z : ℕ) (hN : 0 ≤ N) (ht : 1 ≤ t) (hz : z ≤ q)
    (hw : N / t ^ b ≤ w) :
    N ^ (z + 1) / (2 * t ^ (a + b * q)) ≤ (N / (2 * t ^ a)) * w ^ z := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hw0 : 0 ≤ w := (div_nonneg hN (pow_nonneg htpos.le b)).trans hw
  calc
    _ ≤ N ^ (z + 1) / (2 * t ^ (a + b * z)) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hN _) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_left b hz) a)
    _ = (N / (2 * t ^ a)) * (N / t ^ b) ^ z := by
      rw [pow_succ, pow_add, pow_mul, div_pow]
      ring
    _ ≤ _ := by gcongr

theorem ksssInitialMargin_power_lower
    {V : Type*} [DecidableEq V] {q : ℕ}
    (E A N t : ℝ) (a b : ℕ) (hN : 0 ≤ N) (ht : 1 ≤ t) (hratio : N / t ^ b ≤ A / E)
    (i : KSSSTrajectoryIndex V q) :
    N ^ (ksssTrajectoryDimension i + 1) / (2 * t ^ (a + b * q)) ≤
      ksssInitialMargin E A (N / (2 * t ^ a)) i := by
  rw [ksssInitialMargin_eq_dimension_power]
  exact initial_margin_power_lower N t (A / E) a b q (ksssTrajectoryDimension i)
    hN ht (ksssTrajectoryDimension_le i) hratio

theorem initial_regularity_power_margin_budget
    (N t w eta : ℝ) (a : ℕ) (_hN : 0 ≤ N) (ht : 0 < t) (hw : 0 ≤ w) (_heta : 0 ≤ eta)
    (hwN : w ≤ N) (hetaScale : eta ≤ 1 / (6 * t ^ a)) :
    3 * eta * w + N / (2 * t ^ a) ≤ N / t ^ a := by
  calc
    _ ≤ 3 * (1 / (6 * t ^ a)) * N + N / (2 * t ^ a) := by gcongr
    _ = _ := by ring

end

end Erdos207
