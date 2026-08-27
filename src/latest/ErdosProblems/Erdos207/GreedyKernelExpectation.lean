/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteStoppedKernel
import ErdosProblems.Erdos207.AbsorberGreedy

/-!
# Exact conditional expectations for the greedy kernel

When the availability set is nonempty, the next state is the uniform image
of its triangles under `greedyStep`.  The formulas below expose the exact
conditional drift and second moment of an arbitrary real observable.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Every positive-mass successor is either the frozen state or an actual
greedy step using one currently available triangle. -/
theorem greedyKernel_supported_step_or_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    FiniteLaw.SupportedOn
      (fun S' ↦ S' = S ∨ ∃ T ∈ S.available, S' = greedyStep F S T)
      (greedyKernel F S) := by
  classical
  unfold greedyKernel
  split_ifs with hA
  · let hne : Nonempty S.available :=
      ⟨⟨hA.choose, hA.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V :=
      fun T ↦ greedyStep F S T.1
    exact (FiniteLaw.uniform_supported (fun _ : S.available ↦ True)
      (fun _ ↦ trivial)).map next fun T _ ↦
        Or.inr ⟨T.1, T.2, rfl⟩
  · exact FiniteLaw.supportedOn_pure _ (Or.inl rfl)

/-- Exact expectation formula at a nonempty greedy state. -/
theorem greedyKernel_expectationReal_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hA : S.available.Nonempty) (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal φ =
      (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available, φ (greedyStep F S T.1) := by
  classical
  let hne : Nonempty S.available :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let next : S.available → GreedyStateOn V :=
    fun T ↦ greedyStep F S T.1
  have hkernel : greedyKernel F S =
      FiniteLaw.map next (@FiniteLaw.uniform S.available _ hne) := by
    simp [greedyKernel, hA, next]
  rw [hkernel, FiniteLaw.expectationReal_map,
    FiniteLaw.expectationReal_uniform]
  simp only [Fintype.card_coe, next]

/-- The empty state is frozen. -/
theorem greedyKernel_expectationReal_of_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hA : S.available = ∅) (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal φ = φ S := by
  classical
  have hnot : ¬S.available.Nonempty := by simpa [hA]
  have hkernel : greedyKernel F S = FiniteLaw.pure S := by
    simp [greedyKernel, hnot]
  rw [hkernel, FiniteLaw.expectationReal_pure]

/-- Exact conditional drift formula for an arbitrary observable. -/
theorem greedyKernel_expectationReal_increment_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hA : S.available.Nonempty) (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal (fun S' ↦ φ S' - φ S) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available, (φ (greedyStep F S T.1) - φ S) := by
  exact greedyKernel_expectationReal_of_nonempty F S hA _

/-- Exact conditional second-moment formula for an arbitrary observable. -/
theorem greedyKernel_expectationReal_sqIncrement_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hA : S.available.Nonempty) (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (φ S' - φ S) ^ 2) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available,
          (φ (greedyStep F S T.1) - φ S) ^ 2 := by
  exact greedyKernel_expectationReal_of_nonempty F S hA _

end

end Erdos207
