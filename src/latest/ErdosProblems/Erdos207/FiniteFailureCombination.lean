/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteRealExpectation

/-! # Combining failure estimates on a common finite law -/

namespace Erdos207

theorem finiteLaw_failure_and_le
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (P Q : Ω → Prop) (a b : ℝ)
    (hP : (L.probability (fun ω ↦ ¬ P ω) : ℝ) ≤ a)
    (hQ : (L.probability (fun ω ↦ ¬ Q ω) : ℝ) ≤ b) :
    (L.probability (fun ω ↦ ¬ (P ω ∧ Q ω)) : ℝ) ≤ a + b := by
  classical
  have h := L.probability_or_le (fun ω ↦ ¬ P ω) (fun ω ↦ ¬ Q ω)
  have hr : (L.probability (fun ω ↦ ¬ (P ω ∧ Q ω)) : ℝ) ≤
      (L.probability (fun ω ↦ ¬ P ω) : ℝ) + (L.probability (fun ω ↦ ¬ Q ω) : ℝ) := by
    simpa only [not_and_or] using (show (L.probability (fun ω ↦ ¬ P ω ∨ ¬ Q ω) : ℝ) ≤
      (L.probability (fun ω ↦ ¬ P ω) : ℝ) + (L.probability (fun ω ↦ ¬ Q ω) : ℝ) by exact_mod_cast h)
  exact hr.trans (add_le_add hP hQ)

end Erdos207
