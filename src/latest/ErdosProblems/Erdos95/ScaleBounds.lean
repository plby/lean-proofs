/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.GuthParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Large-scale real-power bounds
-/

namespace Erdos95.ScaleBounds

/-- A positive real power of a natural number eventually exceeds any fixed
real constant. -/
theorem exists_nat_forall_le_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C ≤ (n : ℝ) ^ a := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ a :=
    ht.eventually (Filter.eventually_ge_atTop C)
  exact Filter.eventually_atTop.mp hevent

/-- The threshold may additionally be required to be positive. -/
theorem exists_pos_nat_forall_le_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → C ≤ (n : ℝ) ^ a := by
  obtain ⟨N, hN⟩ := exists_nat_forall_le_rpow ha C
  refine ⟨max 1 N, by omega, ?_⟩
  intro n hn
  exact hN n ((le_max_right 1 N).trans hn)

end Erdos95.ScaleBounds
