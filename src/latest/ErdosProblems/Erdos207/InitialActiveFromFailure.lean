/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedIndexedInvariant

/-! # A nontrivial failure bound forces the frozen process to start active -/

namespace Erdos207.FiniteLaw

open scoped NNReal

noncomputable section

theorem timedStopped_initial_active_of_failure_lt_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω) (active : ℕ → Ω → Prop) (x₀ : Ω)
    (hsmall : (timedStoppedProcessLaw n K active x₀).probability (fun z ↦ ¬ active z.1.1 z.2) < 1) :
    active 0 x₀ := by
  by_contra hinactive
  have hs := timedStoppedProcessLaw_supported_indexed n K active (fun i x ↦ ¬ active i x) x₀ hinactive
    (fun _ _ _ hnot hyes ↦ (hnot hyes).elim)
  have hone := (timedStoppedProcessLaw n K active x₀).probability_eq_one_of_supported _ hs
  rw [hone] at hsmall
  exact lt_irrefl _ hsmall

end

end Erdos207.FiniteLaw
