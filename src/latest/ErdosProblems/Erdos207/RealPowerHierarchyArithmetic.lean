/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerHierarchyArithmetic
import Mathlib.Tactic

/-! # Real-coefficient budgets on the existing integer dyadic hierarchy -/

namespace Erdos207

theorem real_coeff_mul_pow_le_pow
    {C t : ℝ} {a b : ℕ} (ht : 1 ≤ t) (hC : C ≤ t) (hab : a + 1 ≤ b) :
    C * t ^ a ≤ t ^ b := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  calc
    C * t ^ a ≤ t * t ^ a := mul_le_mul_of_nonneg_right hC (pow_nonneg ht0 a)
    _ = t ^ (a + 1) := by rw [pow_succ]; ring
    _ ≤ t ^ b := pow_le_pow_right₀ ht hab

theorem real_coeff_mul_power_ratio_le
    {C N t : ℝ} {u v w : ℕ} (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hC : C ≤ t) (hgap : u + w + 1 ≤ v) :
    C * N * t ^ u / t ^ v ≤ N / t ^ w := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [div_le_div_iff₀ (pow_pos htpos v) (pow_pos htpos w)]
  calc
    C * N * t ^ u * t ^ w = N * (C * t ^ (u + w)) := by rw [pow_add]; ring
    _ ≤ N * t ^ v := mul_le_mul_of_nonneg_left (real_coeff_mul_pow_le_pow ht hC hgap) hN

theorem eventually_real_le_dyadicPowerScale
    {R : ℕ} (hR : 0 < R) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C ≤ (dyadicPowerScale R n : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_ge C
  obtain ⟨N, hN⟩ := eventually_le_dyadicPowerScale hR K
  refine ⟨N, ?_⟩
  intro n hn
  exact hK.trans (by exact_mod_cast hN n hn)

theorem eventually_real_coeff_mul_dyadic_power_le
    {R a b : ℕ} (hR : 0 < R) (hab : a + 1 ≤ b) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (dyadicPowerScale R n : ℝ) ^ a ≤ (dyadicPowerScale R n : ℝ) ^ b := by
  obtain ⟨N, hN⟩ := eventually_real_le_dyadicPowerScale hR C
  refine ⟨N, fun n hn ↦ real_coeff_mul_pow_le_pow ?_ (hN n hn) hab⟩
  exact_mod_cast one_le_dyadicPowerScale R n

end Erdos207
