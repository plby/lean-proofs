/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteStoppedKernel
import ErdosProblems.Erdos207.PairExtensionTrajectory

/-! # Time-indexed invariants and the actual insertion counter of a frozen process -/

namespace Erdos207

namespace FiniteLaw

theorem timedStoppedProcessLaw_supported_indexed
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (K : ℕ → Ω → FiniteLaw Ω) (active : ℕ → Ω → Prop)
    (P : ℕ → Ω → Prop) (x₀ : Ω) (hP₀ : P 0 x₀)
    (hstep : ∀ i, i < n → ∀ x, P i x → active i x → (K i x).SupportedOn (P (i + 1))) :
    (timedStoppedProcessLaw n K active x₀).SupportedOn (fun z ↦ P z.1.1 z.2) := by
  apply (supportedOn_pure (fun z : TimedState Ω n ↦ P z.1.1 z.2) hP₀).evolveKernels
  intro _i z hz
  classical
  unfold timedStoppedKernel
  split_ifs with hactive
  · exact (hstep z.1.1 hactive.1 z.2 hz hactive.2).map
      (fun x' ↦ (advanceTime z.1 hactive.1, x')) (fun x' hx' ↦ by
        simpa only [advanceTime_val] using hx')
  · exact supportedOn_pure _ hz

end FiniteLaw

noncomputable section

theorem timedStoppedGreedyProcessLaw_supported_counter
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S, PairTrajectoryInvariant F S₀ S →
      S.chosen.card = S₀.chosen.card + i → active i S → S.available.Nonempty) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2 ∧ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported_indexed n (fun _ ↦ greedyKernel F) active
    (fun i S ↦ PairTrajectoryInvariant F S₀ S ∧ S.chosen.card = S₀.chosen.card + i) S₀
    ⟨pairTrajectoryInvariant_initial hInv₀, by simp⟩
  intro i hi S hS hactive S' hmass
  obtain ⟨T, hT, rfl⟩ := greedyKernel_supported_step_of_nonempty F S
    (havailable i hi S hS.1 hS.2 hactive) S' hmass
  refine ⟨⟨hS.1.1.step hT, (greedyStep_available_subset F S T).trans hS.1.2⟩, ?_⟩
  rw [greedyStep_chosen_card F S T (hS.1.1.2.2 T hT).1, hS.2]
  omega

end

end Erdos207
