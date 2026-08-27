/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind

/-! # Averaging a conditional failure estimate with an unconditioned obstruction term -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem jointBind_failure_le_of_conditional_add
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (Good : Ω → Prop) (Fail Bad : Ω → Ξ → Prop)
    (priorError conditionalError obstructionError : ℝ≥0)
    (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (hconditional : ∀ omega, 0 < L.mass omega → Good omega →
      (K omega).probability (Fail omega) ≤ conditionalError+(K omega).probability (Bad omega))
    (hbad : (L.jointBind K).probability (fun z ↦ Bad z.1 z.2) ≤ obstructionError) :
    (L.jointBind K).probability (fun z ↦ Fail z.1 z.2) ≤ priorError+conditionalError+obstructionError := by
  classical
  have hpoint : ∀ omega, L.mass omega*(K omega).probability (Fail omega) ≤
      L.mass omega*((if Good omega then 0 else 1)+conditionalError+(K omega).probability (Bad omega)) := by
    intro omega
    by_cases hm : 0 < L.mass omega
    · apply mul_le_mul_of_nonneg_left _ zero_le
      by_cases hg : Good omega
      · simpa only [if_pos hg, zero_add] using hconditional omega hm hg
      · simp only [if_neg hg]
        exact ((K omega).probability_le_one _).trans (by
          calc
            (1 : ℝ≥0) ≤ 1+conditionalError := le_add_of_nonneg_right zero_le
            _ ≤ _ := le_add_of_nonneg_right zero_le)
    · have hz : L.mass omega = 0 := le_antisymm (not_lt.mp hm) zero_le
      simp only [hz, zero_mul, le_refl]
  have hindicator : (∑ omega, L.mass omega*(if Good omega then 0 else 1)) =
      L.probability (fun omega ↦ ¬ Good omega) := by
    unfold probability
    apply sum_congr rfl
    intro omega _
    by_cases hg : Good omega <;> simp [hg]
  have hconstant : (∑ omega, L.mass omega*conditionalError) = conditionalError := by
    rw [← sum_mul, L.sum_mass, one_mul]
  calc
    _ = ∑ omega, L.mass omega*(K omega).probability (Fail omega) := L.probability_jointBind K _
    _ ≤ ∑ omega, L.mass omega*((if Good omega then 0 else 1)+conditionalError+
        (K omega).probability (Bad omega)) := sum_le_sum (fun omega _ ↦ hpoint omega)
    _ = L.probability (fun omega ↦ ¬ Good omega)+conditionalError+
        (L.jointBind K).probability (fun z ↦ Bad z.1 z.2) := by
      simp only [mul_add, sum_add_distrib, hindicator, hconstant, probability_jointBind]
    _ ≤ _ := add_le_add (add_le_add hprior le_rfl) hbad

end

end Erdos207.FiniteLaw
