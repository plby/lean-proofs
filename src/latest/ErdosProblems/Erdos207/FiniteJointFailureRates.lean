/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind

/-! # A retrospective joint failure bound yields likely good conditional inputs -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem expectation_conditional_failure
    {D S : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    (P : FiniteLaw D) (K : D → FiniteLaw S) (Bad : D → S → Prop) :
    P.expectation (fun d ↦ (K d).probability (Bad d)) =
      (P.jointBind K).probability (fun u ↦ Bad u.1 u.2) := by
  rw [probability_jointBind]
  rfl

theorem probability_large_conditional_failure_le
    {D S : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    (P : FiniteLaw D) (K : D → FiniteLaw S) (Bad : D → S → Prop)
    (epsilon delta : ℝ≥0) (hdelta : 0 < delta)
    (hbad : (P.jointBind K).probability (fun u ↦ Bad u.1 u.2) ≤ epsilon) :
    P.probability (fun d ↦ delta ≤ (K d).probability (Bad d)) ≤ epsilon / delta := by
  have h := P.probability_le_expectation_div (fun d ↦ (K d).probability (Bad d)) hdelta
  rw [expectation_conditional_failure] at h
  exact h.trans (div_le_div_of_nonneg_right hbad zero_le)

end

end Erdos207.FiniteLaw
