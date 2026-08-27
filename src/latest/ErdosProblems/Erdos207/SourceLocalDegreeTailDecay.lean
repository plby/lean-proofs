/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedMomentFailureBudget

/-! # Explicit eventual local-degree failure bounds at a fixed moment order -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceNibbleWitnessBound_le_power
    (N t R j' : ℕ) (ht : 1 ≤ t) (hN : N ≤ t ^ R) :
    2 ^ j' * (N + 1) ^ (3 * j') ≤
      (2 ^ j' * 2 ^ (3 * j')) * t ^ (R * (3 * j')) := by
  have htR : 1 ≤ t ^ R := Nat.one_le_pow _ _ ht
  have hbase : N + 1 ≤ 2 * t ^ R := by omega
  calc
    _ ≤ 2 ^ j' * (2 * t ^ R) ^ (3 * j') :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem eventually_sourceLocalDegreeTailBudget_lt
    (ell j j' R D s : ℕ) (C B epsilon : ℝ≥0)
    (hs : 3 * R + 1 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N n : ℕ) (p y b K : ℝ≥0),
      N ≤ t ^ R →
      0 < sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
        (n : ℝ≥0) ^ (j - 3) →
      (t : ℝ≥0) * (sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
        (n : ℝ≥0) ^ (j - 3)) ≤ K → 1 ≤ K →
      b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t →
      sourceLocalDegreeTailBudget ell j j' s N n p C b y K < epsilon := by
  obtain ⟨T, hT1, hT⟩ := eventually_fixedMoment_failure_lt R s D (R * (3 * j'))
    ((2 * C) ^ (s * (3 * j'))) (boundedIntersectionMomentCoefficient (3 * j') s)
    B ((2 ^ j' * 2 ^ (3 * j') : ℕ) : ℝ≥0) epsilon hs hepsilon
  refine ⟨T, hT1, fun t ht N n p y b K hN hkappa hK hK1 hb ↦ ?_⟩
  exact hT t ht N
    (sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) * (n : ℝ≥0) ^ (j - 3))
    K b ((2 ^ j' * (N + 1) ^ (3 * j') : ℕ) : ℝ≥0) hN hkappa hK hK1 hb
    (by exact_mod_cast sourceNibbleWitnessBound_le_power N t R j' (hT1.trans ht) hN)

end

end Erdos207
