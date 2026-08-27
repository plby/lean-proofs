/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyKernelExpectation

/-!
# Exact deletion statistics for the constrained greedy kernel

For a fixed test family `Q`, the trajectory observable is the number of
currently available triangles lying in `Q`.  A greedy step can only delete
triangles from the availability family.  This file records the resulting
exact cardinality, drift, and conditional second-moment identities.  These
are the algebraic input for the edge-extension and threat trajectories.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The currently available members of a fixed test family. -/
def greedyAvailableIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : TripleSystemOn V) (S : GreedyStateOn V) : TripleSystemOn V :=
  S.available ∩ Q

/-- The test-family triangles lost in one greedy step. -/
def greedyDeletedIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (T : TripleOn V) : TripleSystemOn V :=
  greedyAvailableIn Q S \ greedyAvailableIn Q (greedyStep F S T)

/-- Real-valued size of the test-family availability trajectory. -/
def greedyAvailableCountReal
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : TripleSystemOn V) (S : GreedyStateOn V) : ℝ :=
  (greedyAvailableIn Q S).card

/-- A greedy step never adds a new available triangle. -/
lemma greedyStep_available_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    (greedyStep F S T).available ⊆ S.available := by
  exact (legalAvailable_subset_right F _ _).trans (erase_subset _ _)

/-- The restricted availability family is also monotone under a step. -/
lemma greedyAvailableIn_step_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    greedyAvailableIn Q (greedyStep F S T) ⊆ greedyAvailableIn Q S := by
  intro U hU
  have hUint := mem_inter.mp hU
  exact mem_inter.mpr
    ⟨greedyStep_available_subset F S T hUint.1, hUint.2⟩

/-- Lost and surviving test-family triangles partition the old family. -/
lemma greedyDeletedIn_card_add_step_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    (greedyDeletedIn F Q S T).card +
        (greedyAvailableIn Q (greedyStep F S T)).card =
      (greedyAvailableIn Q S).card := by
  exact card_sdiff_add_card_eq_card
    (greedyAvailableIn_step_subset F Q S T)

/-- The one-step increment is exactly minus the number of deletions. -/
lemma greedyAvailableCountReal_step_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    greedyAvailableCountReal Q (greedyStep F S T) -
        greedyAvailableCountReal Q S =
      -((greedyDeletedIn F Q S T).card : ℝ) := by
  have hcard := greedyDeletedIn_card_add_step_card F Q S T
  have hcast : ((greedyDeletedIn F Q S T).card : ℝ) +
        ((greedyAvailableIn Q (greedyStep F S T)).card : ℝ) =
      ((greedyAvailableIn Q S).card : ℝ) := by
    exact_mod_cast hcard
  simp only [greedyAvailableCountReal]
  linarith

/-- Exact conditional drift of a restricted availability count. -/
theorem greedyKernel_expectationReal_availableCount_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal Q S' -
          greedyAvailableCountReal Q S) =
      -(S.available.card : ℝ)⁻¹ *
        ∑ T : S.available, ((greedyDeletedIn F Q S T.1).card : ℝ) := by
  rw [greedyKernel_expectationReal_increment_of_nonempty F S hA]
  simp_rw [greedyAvailableCountReal_step_sub]
  rw [sum_neg_distrib, mul_neg]
  ring

/-- Exact conditional second moment of a restricted availability count. -/
theorem greedyKernel_expectationReal_availableCount_sqIncrement
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (greedyAvailableCountReal Q S' -
          greedyAvailableCountReal Q S) ^ 2) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available,
          ((greedyDeletedIn F Q S T.1).card : ℝ) ^ 2 := by
  rw [greedyKernel_expectationReal_sqIncrement_of_nonempty F S hA]
  simp_rw [greedyAvailableCountReal_step_sub, neg_sq]

end

end Erdos207
