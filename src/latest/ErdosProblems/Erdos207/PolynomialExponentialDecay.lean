/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Explicit eventual bounds for fixed polynomials times exponential decay -/

namespace Erdos207

open Filter
open scoped Topology

theorem polynomial_exp_neg_mul_tendsToZero
    (C a : ℝ) (d : ℕ) (ha : 0 < a) :
    Tendsto (fun t : ℕ ↦ C * (t : ℝ) ^ d * Real.exp (-a * t)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d a ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hC := h.const_mul C
  simpa only [mul_zero, Function.comp_apply, Real.rpow_natCast, mul_assoc] using hC

theorem eventually_polynomial_exp_neg_mul_lt
    (C a epsilon : ℝ) (d : ℕ) (ha : 0 < a) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      C * (t : ℝ) ^ d * Real.exp (-a * t) < epsilon := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((polynomial_exp_neg_mul_tendsToZero C a d ha).eventually (gt_mem_nhds hepsilon))
  exact ⟨max 1 T, le_max_left _ _, fun t ht ↦ hT t ((le_max_right _ _).trans ht)⟩

end Erdos207
