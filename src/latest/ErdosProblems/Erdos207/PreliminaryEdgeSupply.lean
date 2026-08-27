/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryGreedyJointLaw
import ErdosProblems.Erdos207.AvailableThreePairUnion

/-!
# Pair-extension floors give preliminary edge supply

The differential-equation part of the preliminary process controls available
triangles through every still-alive vertex pair.  This file identifies that
pair star with the exact choice set used in the selected/uncovered estimate.
-/

namespace Erdos207

open Finset

noncomputable section

lemma mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag
    {V : Type*} [DecidableEq V] (e : Sym2 V) (T : TripleOn V)
    (he : ¬ e.IsDiag) :
    e ∈ tripleEdgeFinset T ↔ e.toFinset ⊆ T.1 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [Sym2.mk_isDiag_iff] at he
      rw [mk_mem_tripleEdgeFinset_iff, Sym2.toFinset_mk_eq]
      constructor
      · rintro ⟨hu, hv, _⟩
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hv
      · intro h
        exact ⟨h (by simp), h (by simp), he⟩

/-- The subtype choice set and the filtered available pair star count the
same triangles. -/
lemma card_greedyChoicesCoveringEdge_eq_availablePair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (e : Sym2 V) (he : ¬ e.IsDiag) :
    (greedyChoicesCoveringEdge S e).card =
      (availableTrianglesContainingPair S e.toFinset).card := by
  classical
  unfold greedyChoicesCoveringEdge availableTrianglesContainingPair
  apply Finset.card_bij (fun T _ ↦ T.1)
  · intro T hT
    rw [mem_filter]
    exact ⟨T.2,
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag
        e T.1 he).mp (mem_filter.mp hT).2⟩
  · intro T₁ hT₁ T₂ hT₂ hEq
    exact Subtype.ext hEq
  · intro T hT
    refine ⟨⟨T, (mem_filter.mp hT).1⟩, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨mem_univ _,
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag
        e T he).mpr (mem_filter.mp hT).2⟩

/-- An edge of the ambient graph is an off-diagonal symmetric pair. -/
lemma not_isDiag_of_mem_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {e : Sym2 V}
    (he : e ∈ crossingEdges G U) : ¬ e.IsDiag :=
  G.not_isDiag_of_mem_edgeSet (mem_crossingEdges_iff.mp he).1

/-- A positive pair-extension floor supplies at least `d` greedy choices
through every currently uncovered crossing edge whose pair star is alive. -/
theorem greedyChoicesCoveringEdge_card_ge_of_pairFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {S : GreedyStateOn V}
    {d : ℕ} (hfloor : HasAvailablePairFloor d S)
    (halive : ∀ e ∈ greedyUncoveredEdges (crossingEdges G U) S,
      (availableTrianglesContainingPair S e.toFinset).Nonempty) :
    ∀ e ∈ greedyUncoveredEdges (crossingEdges G U) S,
      d ≤ (greedyChoicesCoveringEdge S e).card := by
  intro e he
  have hecross : e ∈ crossingEdges G U := (mem_sdiff.mp he).1
  have hdiag := not_isDiag_of_mem_crossingEdges hecross
  rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hdiag]
  exact hfloor e.toFinset
    (Sym2.card_toFinset_of_not_isDiag e hdiag) (halive e he)

/-- Convenient state predicate collecting exactly the local quantitative
facts required for the preliminary selected/uncovered recurrence. -/
def HasPreliminaryEdgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (S : GreedyStateOn V) : Prop :=
  ∀ e ∈ greedyUncoveredEdges (crossingEdges G U) S,
    d ≤ (greedyChoicesCoveringEdge S e).card

theorem hasPreliminaryEdgeSupply_of_pairFloor_alive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {S : GreedyStateOn V}
    {d : ℕ} (hfloor : HasAvailablePairFloor d S)
    (halive : ∀ e ∈ greedyUncoveredEdges (crossingEdges G U) S,
      (availableTrianglesContainingPair S e.toFinset).Nonempty) :
    HasPreliminaryEdgeSupply G U d S :=
  greedyChoicesCoveringEdge_card_ge_of_pairFloor hfloor halive

end

end Erdos207
