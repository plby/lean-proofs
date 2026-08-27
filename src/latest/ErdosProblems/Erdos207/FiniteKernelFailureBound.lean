/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-! # Accumulating a conditional failure budget over finite kernels -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem probability_bind_le_old_add
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ω)
    (P : Ω → Prop) [DecidablePred P] (epsilon : ℝ)
    (hK : ∀ x, ((K x).probability P : ℝ) ≤ (if P x then 1 else 0) + epsilon) :
    ((bind L K).probability P : ℝ) ≤ (L.probability P : ℝ) + epsilon := by
  rw [probability_bind]
  push_cast
  calc
    _ ≤ ∑ x, (L.mass x : ℝ) * ((if P x then 1 else 0) + epsilon) :=
      sum_le_sum (fun x _ ↦ mul_le_mul_of_nonneg_left (hK x) (NNReal.coe_nonneg _))
    _ = _ := by
      change L.expectationReal (fun x ↦ (if P x then 1 else 0) + epsilon) = _
      rw [expectationReal_add, expectationReal_indicator, expectationReal_const]

theorem probability_evolve_failure_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : ℕ → Ω → FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] (epsilon : ℝ)
    (hK : ∀ t x, ((K t x).probability P : ℝ) ≤ (if P x then 1 else 0) + epsilon)
    (x0 : Ω) (hx0 : ¬ P x0) (t : ℕ) :
    ((evolveKernels K t (pure x0)).probability P : ℝ) ≤ t * epsilon := by
  induction t with
  | zero => simp [hx0]
  | succ t ih =>
      rw [evolveKernels_succ]
      have h := probability_bind_le_old_add (evolveKernels K t (pure x0)) (K t) P epsilon (hK t)
      apply h.trans
      calc
        _ ≤ (t : ℝ) * epsilon + epsilon := add_le_add ih le_rfl
        _ = _ := by push_cast; ring

end

end Erdos207.FiniteLaw
