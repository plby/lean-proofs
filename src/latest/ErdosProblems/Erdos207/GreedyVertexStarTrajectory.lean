/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyKernelExpectation
import ErdosProblems.Erdos207.AvailablePairDegreeTrajectory
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-!
# Exact vertex-star dynamics in the constrained greedy process

The leave-degree trajectory is the complement of twice the selected
vertex-star count.  This file records the exact Bernoulli increment and its
conditional first and second moments.  These identities are the local input
for the stopped concentration argument controlling available pair-codegrees.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Real-valued selected vertex-star size. -/
def selectedStarCountReal
    {V : Type*} [DecidableEq V] (v : V) (S : GreedyStateOn V) : ℝ :=
  (triplesThrough S.chosen v).card

/-- The available vertex star at the current state. -/
def availableTriplesThrough
    {V : Type*} [DecidableEq V] (S : GreedyStateOn V) (v : V) :
    TripleSystemOn V :=
  triplesThrough S.available v

@[simp]
lemma mem_availableTriplesThrough_iff
    {V : Type*} [DecidableEq V]
    {S : GreedyStateOn V} {v : V} {T : TripleOn V} :
    T ∈ availableTriplesThrough S v ↔ T ∈ S.available ∧ v ∈ T.1 := by
  simp [availableTriplesThrough, triplesThrough]

/-- Selecting a new triangle increases the selected star at `v` exactly when
the triangle contains `v`. -/
lemma greedyStep_triplesThrough_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (v : V) (hTnot : T ∉ S.chosen) :
    (triplesThrough (greedyStep F S T).chosen v).card =
      if v ∈ T.1 then (triplesThrough S.chosen v).card + 1
      else (triplesThrough S.chosen v).card := by
  by_cases hv : v ∈ T.1
  · have hfilter : triplesThrough (insert T S.chosen) v =
        insert T (triplesThrough S.chosen v) := by
      ext U
      simp only [triplesThrough, mem_filter, mem_insert]
      constructor
      · rintro ⟨hUT | hUC, hvU⟩
        · exact Or.inl hUT
        · exact Or.inr ⟨hUC, hvU⟩
      · rintro (hUT | ⟨hUC, hvU⟩)
        · subst U
          exact ⟨Or.inl rfl, hv⟩
        · exact ⟨Or.inr hUC, hvU⟩
    have hTfiltered : T ∉ triplesThrough S.chosen v := by
      intro hT
      exact hTnot (mem_filter.mp hT).1
    rw [show (greedyStep F S T).chosen = insert T S.chosen by rfl,
      hfilter, card_insert_of_notMem hTfiltered, if_pos hv]
  · have hfilter : triplesThrough (insert T S.chosen) v =
        triplesThrough S.chosen v := by
      ext U
      simp only [triplesThrough, mem_filter, mem_insert]
      constructor
      · rintro ⟨hUT | hUC, hvU⟩
        · subst U
          exact (hv hvU).elim
        · exact ⟨hUC, hvU⟩
      · rintro ⟨hUC, hvU⟩
        exact ⟨Or.inr hUC, hvU⟩
    rw [show (greedyStep F S T).chosen = insert T S.chosen by rfl,
      hfilter]
    simp [hv]

/-- Real increment form of `greedyStep_triplesThrough_card`. -/
lemma selectedStarCountReal_step_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (v : V) (hTnot : T ∉ S.chosen) :
    selectedStarCountReal v (greedyStep F S T) -
        selectedStarCountReal v S =
      if v ∈ T.1 then 1 else 0 := by
  rw [selectedStarCountReal, selectedStarCountReal,
    greedyStep_triplesThrough_card F S T v hTnot]
  split_ifs <;> norm_num

/-- The number of available choices containing `v` is the sum of their
Bernoulli selection indicators. -/
lemma sum_available_vertex_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (v : V) :
    ∑ T : S.available, (if v ∈ T.1.1 then (1 : ℝ) else 0) =
      (availableTriplesThrough S v).card := by
  calc
    ∑ T : S.available, (if v ∈ T.1.1 then (1 : ℝ) else 0) =
        ∑ T ∈ S.available, (if v ∈ T.1 then (1 : ℝ) else 0) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach S.available
        (fun T ↦ if v ∈ T.1 then (1 : ℝ) else 0)
    _ = (availableTriplesThrough S v).card := by
      simp [availableTriplesThrough, triplesThrough]

/-- Exact conditional drift of a selected vertex-star count. -/
theorem greedyKernel_expectationReal_selectedStar_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hInv : GreedyInvariant F S) (hA : S.available.Nonempty) (v : V) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ selectedStarCountReal v S' - selectedStarCountReal v S) =
      ((availableTriplesThrough S v).card : ℝ) /
        (S.available.card : ℝ) := by
  rw [greedyKernel_expectationReal_increment_of_nonempty F S hA]
  have hpoint : ∀ T : S.available,
      selectedStarCountReal v (greedyStep F S T.1) -
          selectedStarCountReal v S =
        if v ∈ T.1.1 then 1 else 0 := by
    intro T
    exact selectedStarCountReal_step_sub F S T.1 v
      (hInv.2.2 T.1 T.2).1
  simp_rw [hpoint]
  rw [sum_available_vertex_indicator]
  rw [div_eq_mul_inv, mul_comm]

/-- The conditional second moment equals the conditional first moment,
because every star increment is zero or one. -/
theorem greedyKernel_expectationReal_selectedStar_sqIncrement
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hInv : GreedyInvariant F S) (hA : S.available.Nonempty) (v : V) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (selectedStarCountReal v S' -
          selectedStarCountReal v S) ^ 2) =
      ((availableTriplesThrough S v).card : ℝ) /
        (S.available.card : ℝ) := by
  rw [greedyKernel_expectationReal_sqIncrement_of_nonempty F S hA]
  have hpoint : ∀ T : S.available,
      (selectedStarCountReal v (greedyStep F S T.1) -
          selectedStarCountReal v S) ^ 2 =
        if v ∈ T.1.1 then 1 else 0 := by
    intro T
    rw [selectedStarCountReal_step_sub F S T.1 v
      (hInv.2.2 T.1 T.2).1]
    split_ifs <;> norm_num
  simp_rw [hpoint]
  rw [sum_available_vertex_indicator]
  rw [div_eq_mul_inv, mul_comm]

/-- Pointwise jump bound for the selected-star observable on supported
successors of a nonempty greedy state. -/
theorem greedyKernel_selectedStar_increment_mem_zero_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hInv : GreedyInvariant F S) (hA : S.available.Nonempty) (v : V)
    {S' : GreedyStateOn V} (hS' : 0 < (greedyKernel F S).mass S') :
    selectedStarCountReal v S' - selectedStarCountReal v S = 0 ∨
      selectedStarCountReal v S' - selectedStarCountReal v S = 1 := by
  obtain ⟨T, hT, rfl⟩ :=
    greedyKernel_supported_step_of_nonempty F S hA S' hS'
  rw [selectedStarCountReal_step_sub F S T v (hInv.2.2 T hT).1]
  split_ifs <;> simp

end

end Erdos207
