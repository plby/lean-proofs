/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerTailDecay

/-! # The combined coupled and degree failure bound tends to zero -/

namespace Erdos207

theorem eventually_degree_coupled_failure_lt_one
    (q numSets R : ℕ) (hR : 0 < R) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
        2 * (numSets : ℝ) * N + 4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6) *
        (1 / 2 : ℝ) ^ dyadicPowerScale R N < 1 := by
  obtain ⟨N₁, hN₁⟩ := eventually_coupled_power_failure_lt q R (1 / 2) hR (by norm_num)
  obtain ⟨N₂, hN₂⟩ := eventually_polynomial_dyadic_geometric_lt R 1 (2 * (numSets : ℝ))
    (1 / 2) hR (by positivity) (by norm_num)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hfirst := hN₁ N ((le_max_left _ _).trans hN)
  have hsecond := hN₂ N ((le_max_right _ _).trans hN)
  have hdegree : 2 * (numSets : ℝ) * N * (1 / 2 : ℝ) ^ dyadicPowerScale R N < 1 / 2 := by
    apply lt_of_le_of_lt _ hsecond
    simp only [pow_one]
    gcongr
    linarith
  have hsum := add_lt_add hfirst hdegree
  calc
    _ = (2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
        4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6) * (1 / 2 : ℝ) ^ dyadicPowerScale R N +
        2 * (numSets : ℝ) * N * (1 / 2 : ℝ) ^ dyadicPowerScale R N := by ring
    _ < (1 : ℝ) / 2 + 1 / 2 := hsum
    _ = 1 := by norm_num

end Erdos207
