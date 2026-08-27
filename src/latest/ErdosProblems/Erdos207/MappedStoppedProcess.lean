/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyVertexKernel
import ErdosProblems.Erdos207.FiniteStoppedKernel
import ErdosProblems.Erdos207.CoupledEnvelopeProcess

/-! # Exact pushforward of the entire timed stopped law -/

namespace Erdos207

noncomputable section

theorem FiniteLaw.timedStoppedKernel_map
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (n : ℕ) (K : ℕ → A → FiniteLaw A) (L : ℕ → B → FiniteLaw B)
    (active : ℕ → A → Prop) (active' : ℕ → B → Prop) (f : A → B)
    (hkernel : ∀ i x, FiniteLaw.map f (K i x) = L i (f x))
    (hactive : ∀ i x, active' i (f x) ↔ active i x) (z : FiniteLaw.TimedState A n) :
    FiniteLaw.map (fun u : FiniteLaw.TimedState A n ↦ (u.1, f u.2))
      (FiniteLaw.timedStoppedKernel n K active z) =
        FiniteLaw.timedStoppedKernel n L active' (z.1, f z.2) := by
  classical
  unfold FiniteLaw.timedStoppedKernel
  simp only [hactive]
  split_ifs with hrun
  · rw [FiniteLaw.map_comp, ← hkernel z.1.1 z.2, FiniteLaw.map_comp]
    rfl
  · exact FiniteLaw.map_pure _ _

theorem FiniteLaw.timedStoppedProcessLaw_map
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (n : ℕ) (K : ℕ → A → FiniteLaw A) (L : ℕ → B → FiniteLaw B)
    (active : ℕ → A → Prop) (active' : ℕ → B → Prop) (f : A → B)
    (hkernel : ∀ i x, FiniteLaw.map f (K i x) = L i (f x))
    (hactive : ∀ i x, active' i (f x) ↔ active i x) (x₀ : A) :
    FiniteLaw.map (fun u : FiniteLaw.TimedState A n ↦ (u.1, f u.2))
      (FiniteLaw.timedStoppedProcessLaw n K active x₀) =
        FiniteLaw.timedStoppedProcessLaw n L active' (f x₀) := by
  have h := FiniteLaw.map_evolveKernels (fun _ ↦ FiniteLaw.timedStoppedKernel n K active)
    (fun _ ↦ FiniteLaw.timedStoppedKernel n L active')
    (fun u : FiniteLaw.TimedState A n ↦ (u.1, f u.2))
    (fun _ u ↦ FiniteLaw.timedStoppedKernel_map n K L active active' f hkernel hactive u)
    n (FiniteLaw.pure ((⟨0, by omega⟩ : Fin (n + 1)), x₀))
  simpa only [FiniteLaw.map_pure, FiniteLaw.timedStoppedProcessLaw] using h

theorem timedStoppedGreedyProcessLaw_map
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) (active' : ℕ → GreedyStateOn W → Prop)
    (hactive : ∀ i S, active' i (mapGreedyState f S) ↔ active i S) (S₀ : GreedyStateOn V) :
    FiniteLaw.map (fun u : FiniteLaw.TimedState (GreedyStateOn V) n ↦ (u.1, mapGreedyState f u.2))
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀) =
        FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (mapForbiddenFamily f F))
          active' (mapGreedyState f S₀) :=
  FiniteLaw.timedStoppedProcessLaw_map n (fun _ ↦ greedyKernel F)
    (fun _ ↦ greedyKernel (mapForbiddenFamily f F)) active active' (mapGreedyState f)
    (fun _ S ↦ greedyKernel_map f F S) hactive S₀

end

end Erdos207
