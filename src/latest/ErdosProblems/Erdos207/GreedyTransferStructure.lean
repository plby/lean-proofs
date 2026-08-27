/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpGreedySurvival

/-!
# Structural properties needed by the transfer recurrence

Besides monotone single insertion, the selected/available transfer argument
uses two elementary facts about a greedy transition: availability only
shrinks, and the unique newly selected triangle (if there is one) belonged
to the old availability family.
-/

namespace Erdos207

open Finset

noncomputable section

/-- One ordinary greedy transition only removes available triangles. -/
theorem greedyKernel_antitone_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) :
    IsAntitoneSetKernel (greedyKernel F)
      (fun S : GreedyStateOn V ↦ S.available) := by
  intro S S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with hself | hstep
  · subst S'
    exact Subset.rfl
  · obtain ⟨T, hT, rfl⟩ := hstep
    exact greedyStep_available_subset F S T

/-- Every newly selected triangle in one ordinary greedy transition was an
available choice before the transition. -/
theorem greedyKernel_newChosen_subset_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    (greedyKernel F S).SupportedOn fun S' ↦
      S'.chosen \ S.chosen ⊆ S.available := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with hself | hstep
  · subst S'
    simp
  · obtain ⟨T, hT, rfl⟩ := hstep
    intro U hU
    rw [greedyStep, mem_sdiff, mem_insert] at hU
    rcases hU.1 with rfl | hUold
    · exact hT
    · exact (hU.2 hUold).elim

/-- The threshold-stopped kernel retains antitone availability. -/
theorem stoppedGreedyKernel_antitone_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) :
    IsAntitoneSetKernel (stoppedGreedyKernel F D)
      (fun S : GreedyStateOn V ↦ S.available) := by
  classical
  intro S
  unfold stoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_antitone_available F S
  · exact FiniteLaw.supportedOn_pure _ Subset.rfl

/-- Every newly selected triangle of the stopped kernel also came from the
old availability family. -/
theorem stoppedGreedyKernel_newChosen_subset_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (S : GreedyStateOn V) :
    (stoppedGreedyKernel F D S).SupportedOn fun S' ↦
      S'.chosen \ S.chosen ⊆ S.available := by
  classical
  unfold stoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_newChosen_subset_available F S
  · exact FiniteLaw.supportedOn_pure _ (by simp)

end

end Erdos207
