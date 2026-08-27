/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # One envelope exponent for finitely many explicit drift and Taylor budgets -/

namespace Erdos207

open Finset

theorem exists_coupled_envelope_exponent
    {I : Type*} [Fintype I] (q : ℕ) (pairCoefficient : ℝ) (configurationCoefficient : I → ℝ) :
    ∃ B : ℕ, 4 * q ≤ B ∧ pairCoefficient ≤ 3 * (B : ℝ) ∧
      ∀ i, configurationCoefficient i ≤ 3 * (B : ℝ) / 2 := by
  classical
  let S : ℝ := ∑ i, |configurationCoefficient i|
  have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ abs_nonneg _
  obtain ⟨B, hB⟩ := exists_nat_gt (4 * (q : ℝ) + 2 * |pairCoefficient| + 2 * S)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  refine ⟨B, ?_, ?_, ?_⟩
  · have hreal : 4 * (q : ℝ) ≤ (B : ℝ) := by nlinarith [abs_nonneg pairCoefficient]
    exact_mod_cast hreal
  · have hp := le_abs_self pairCoefficient
    nlinarith only [hB, hq, hb, hS, hp]
  · intro i
    have hi : |configurationCoefficient i| ≤ S := by
      exact single_le_sum (fun j _ ↦ abs_nonneg (configurationCoefficient j)) (mem_univ i)
    have hc := le_abs_self (configurationCoefficient i)
    nlinarith [abs_nonneg pairCoefficient]

end Erdos207
