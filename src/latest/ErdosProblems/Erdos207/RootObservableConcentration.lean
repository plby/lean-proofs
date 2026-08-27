/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootSurvivalKernel
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-! # Stopped concentration for a surviving triangle-root observable -/

namespace Erdos207

open Finset

noncomputable section

/-- Apply the proved finite stopped-kernel inequality using conditional
root-preserving drift and variance. The probabilistic estimate is proved;
its three quantitative hypotheses remain explicit for the application. -/
theorem probability_timedStoppedGreedy_root_observable_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (root : TripleOn V)
    (obs : ℕ → GreedyStateOn V → ℝ) (M theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hroot₀ : root ∈ S₀.available)
    (hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ T ∈ S.available \ greedyClosedThreats F S root,
        obs (i + 1) (greedyStep F S T) - obs i S ≤ M)
    (hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hR : (S.available \ greedyClosedThreats F S root).Nonempty,
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hR : (S.available \ greedyClosedThreats F S root).Nonempty,
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ v)
    (hM : 0 ≤ M) (htheta : 0 < theta) (hthetaM : theta * M ≤ 1) (hv : 0 ≤ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ root ∈ z.2.available ∧ a ≤ obs z.1.1 z.2 - obs 0 S₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  apply FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
    (P := GreedyInvariant F) (alive := fun S ↦ root ∈ S.available)
    n (fun _ ↦ greedyKernel F) active obs S₀ theta M a v hInv₀ hroot₀
    htheta hM hthetaM hv
    (fun _ _ S hS ↦ greedyKernel_supported hS)
    (fun _ _ S _ hdead ↦ greedyKernel_supported_rootDead F S root hdead)
  · intro i hi S hS hactive hroot S' hmass _ halive
    obtain ⟨T, hT, rfl⟩ := greedyKernel_supported_step_of_nonempty F S ⟨root, hroot⟩ S' hmass
    exact hjump i hi S hS hactive hroot T
      (mem_sdiff.mpr ⟨hT, (root_mem_greedyStep_available_iff hS hroot hT).mp halive⟩)
  · intro i hi S hS hactive hroot
    exact greedyKernel_expectationReal_rootAlive_le_of_restricted root hS hroot
      (fun S' ↦ obs (i + 1) S' - obs i S) 0 le_rfl (hdrift i hi S hS hactive hroot)
  · intro i hi S hS hactive hroot
    exact greedyKernel_expectationReal_rootAlive_le_of_restricted root hS hroot
      (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) v hv (hsecond i hi S hS hactive hroot)

end

end Erdos207
