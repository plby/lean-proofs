/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternSurvivalKernel
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-! # Stopped concentration while every edge of a base pattern survives -/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_pattern_observable_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (Q : SimpleGraph V)
    (obs : ℕ → GreedyStateOn V → ℝ) (M theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hQ₀ : PatternUncovered Q S₀)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      PatternUncovered Q S → S.available.Nonempty)
    (hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PatternUncovered Q S →
      ∀ T ∈ patternSurvivalSelectors Q S, obs (i + 1) (greedyStep F S T) - obs i S ≤ M)
    (hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PatternUncovered Q S →
      ∀ hR : (patternSurvivalSelectors Q S).Nonempty,
        (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PatternUncovered Q S →
      ∀ hR : (patternSurvivalSelectors Q S).Nonempty,
        (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ v)
    (hM : 0 ≤ M) (htheta : 0 < theta) (hthetaM : theta * M ≤ 1) (hv : 0 ≤ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PatternUncovered Q z.2 ∧ a ≤ obs z.1.1 z.2 - obs 0 S₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  apply FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
    (P := GreedyInvariant F) (alive := PatternUncovered Q)
    n (fun _ ↦ greedyKernel F) active obs S₀ theta M a v hInv₀ hQ₀
    htheta hM hthetaM hv
    (fun _ _ S hS ↦ greedyKernel_supported hS)
    (fun _ _ S _ hdead ↦ greedyKernel_supported_patternCovered F Q S hdead)
  · intro i hi S hS hactive hQ S' hmass _ halive
    obtain ⟨T, hT, rfl⟩ := greedyKernel_supported_step_of_nonempty F S
      (havailable i hi S hS hactive hQ) S' hmass
    exact hjump i hi S hS hactive hQ T
      (mem_filter.mpr ⟨hT, ((patternUncovered_greedyStep_iff F Q S T).mp halive).2⟩)
  · intro i hi S hS hactive hQ
    exact greedyKernel_expectationReal_patternUncovered_le_of_restricted Q hQ
      (havailable i hi S hS hactive hQ) (fun S' ↦ obs (i + 1) S' - obs i S) 0 le_rfl
      (hdrift i hi S hS hactive hQ)
  · intro i hi S hS hactive hQ
    exact greedyKernel_expectationReal_patternUncovered_le_of_restricted Q hQ
      (havailable i hi S hS hactive hQ) (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) v hv
      (hsecond i hi S hS hactive hQ)

end

end Erdos207
