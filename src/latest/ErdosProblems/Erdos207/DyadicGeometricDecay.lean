/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicPowerScale
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Polynomially many geometric tails vanish at the dyadic scale -/

namespace Erdos207

open Filter
open scoped Topology NNReal

theorem dyadic_ambient_add_one_le (R n : ℕ) (hR : 0 < R) :
    n + 1 ≤ (2 ^ R + 1) * dyadicPowerScale R n ^ R := by
  have hn := le_two_pow_mul_dyadicPowerScale_pow (n := n) hR
  have ht : 1 ≤ dyadicPowerScale R n ^ R :=
    Nat.one_le_pow _ _ (one_le_dyadicPowerScale R n)
  calc
    n + 1 ≤ 2 ^ R * dyadicPowerScale R n ^ R + dyadicPowerScale R n ^ R :=
      Nat.add_le_add hn ht
    _ = _ := by ring

theorem polynomial_dyadic_geometric_le (R k n : ℕ) (C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) :
    C * (n + 1 : ℝ) ^ k * (1 / 2 : ℝ) ^ dyadicPowerScale R n ≤
      (C * (2 ^ R + 1 : ℝ) ^ k) *
        ((dyadicPowerScale R n : ℝ) ^ (R * k) * (1 / 2 : ℝ) ^ dyadicPowerScale R n) := by
  have hn : (n + 1 : ℝ) ≤ (2 ^ R + 1 : ℝ) * (dyadicPowerScale R n : ℝ) ^ R := by
    exact_mod_cast dyadic_ambient_add_one_le R n hR
  calc
    _ ≤ C * ((2 ^ R + 1 : ℝ) * (dyadicPowerScale R n : ℝ) ^ R) ^ k *
        (1 / 2 : ℝ) ^ dyadicPowerScale R n := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem eventually_polynomial_dyadic_geometric_lt
    (R k : ℕ) (C ε : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n + 1 : ℝ) ^ k * (1 / 2 : ℝ) ^ dyadicPowerScale R n < ε := by
  have hlim : Tendsto (fun t : ℕ ↦ (C * (2 ^ R + 1 : ℝ) ^ k) *
      ((t : ℝ) ^ (R * k) * (1 / 2 : ℝ) ^ t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (R * k)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (C * (2 ^ R + 1 : ℝ) ^ k)
  have hev := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  obtain ⟨N, hN⟩ := eventually_le_dyadicPowerScale hR T
  exact ⟨N, fun n hn ↦ (polynomial_dyadic_geometric_le R k n C hR hC).trans_lt
    (hT _ (hN n hn))⟩

theorem eventually_crude_dyadic_geometric_tail_lt
    (q R : ℕ) (ε : ℝ≥0) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      4 * (q + 1 : ℝ≥0) ^ 2 * (n + 1 : ℝ≥0) ^ 6 *
        (1 / 2 : ℝ≥0) ^ dyadicPowerScale R n < ε := by
  obtain ⟨N, hN⟩ := eventually_polynomial_dyadic_geometric_lt R 6
    (4 * (q + 1 : ℝ) ^ 2) ε hR (by positivity) (by exact_mod_cast hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  exact_mod_cast hN n hn

end Erdos207
