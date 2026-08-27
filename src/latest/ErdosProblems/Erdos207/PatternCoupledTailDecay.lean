/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerTailDecay

/-! # Polynomially many simultaneous pattern failures still have vanishing probability -/

namespace Erdos207

theorem pattern_coupled_failure_coefficient_le
    (q h numSets numPatterns numInner N : ℕ)
    (hPatterns : numPatterns ≤ (h ^ 2 + 1) * (N + 1) ^ (2 * h ^ 2)) (hInner : numInner ≤ numSets) :
    2 * (N ^ 2 + (q + 1) ^ 2 * N ^ 3) + 2 * numSets * N + 2 * numSets * numPatterns +
      4 * (q + 1) ^ 2 * (N + 1) ^ 6 + numInner * N ^ 5 ≤
        (8 * (q + 1) ^ 2 + 5 * numSets + 2 * numSets * h ^ 2) * (N + 1) ^ (6 + 2 * h ^ 2) := by
  let Z := (N + 1) ^ (6 + 2 * h ^ 2)
  have hp (d : ℕ) (hd : d ≤ 6 + 2 * h ^ 2) : N ^ d ≤ Z :=
    (Nat.pow_le_pow_left (Nat.le_succ N) d).trans (Nat.pow_le_pow_right (by omega) hd)
  have h6 : (N + 1) ^ 6 ≤ Z := Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : (N + 1) ^ (2 * h ^ 2) ≤ Z := Nat.pow_le_pow_right (by omega) (by omega)
  have hcoupled := (coupled_failure_coefficient_le q N).trans (Nat.mul_le_mul_left (8 * (q + 1) ^ 2) h6)
  have hdegree : 2 * numSets * N ≤ 2 * numSets * Z := by
    have hn : N ≤ Z := by simpa only [pow_one] using hp 1 (by omega)
    exact Nat.mul_le_mul_left _ hn
  have hpattern : 2 * numSets * numPatterns ≤ 2 * numSets * ((h ^ 2 + 1) * Z) :=
    Nat.mul_le_mul_left _ (hPatterns.trans (Nat.mul_le_mul_left _ hsmall))
  have hlocal : numInner * N ^ 5 ≤ numSets * Z := Nat.mul_le_mul hInner (hp 5 (by omega))
  change _ ≤ (8 * (q + 1) ^ 2 + 5 * numSets + 2 * numSets * h ^ 2) * Z
  nlinarith only [hcoupled, hdegree, hpattern, hlocal]

theorem eventually_pattern_coupled_failure_lt_one
    (q h numSets R : ℕ) (hR : 0 < R) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ numPatterns numInner : ℕ,
      numPatterns ≤ (h ^ 2 + 1) * (N + 1) ^ (2 * h ^ 2) → numInner ≤ numSets →
      (2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
        2 * (numSets : ℝ) * N + 2 * (numSets : ℝ) * numPatterns +
        4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 + (numInner : ℝ) * (N : ℝ) ^ 5) *
          (1 / 2 : ℝ) ^ dyadicPowerScale R N < 1 := by
  obtain ⟨N₀, hN₀⟩ := eventually_polynomial_dyadic_geometric_lt R (6 + 2 * h ^ 2)
    (8 * (q + 1 : ℝ) ^ 2 + 5 * (numSets : ℝ) + 2 * (numSets : ℝ) * h ^ 2) 1 hR (by positivity) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN numPatterns numInner hPatterns hInner
  have hcoef : 2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
      2 * (numSets : ℝ) * N + 2 * (numSets : ℝ) * numPatterns +
      4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 + (numInner : ℝ) * (N : ℝ) ^ 5 ≤
      (8 * (q + 1 : ℝ) ^ 2 + 5 * (numSets : ℝ) + 2 * (numSets : ℝ) * h ^ 2) * (N + 1 : ℝ) ^ (6 + 2 * h ^ 2) := by
    exact_mod_cast pattern_coupled_failure_coefficient_le q h numSets numPatterns numInner N hPatterns hInner
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans_lt (hN₀ N hN)

end Erdos207
