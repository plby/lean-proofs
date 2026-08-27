/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionBound

/-!
# Pair-codegree refinement of the greedy deletion envelope

The crude pair-collision term `3|V|` can be replaced by three times the
maximum number of currently available triangles through a pair.  This is the
decaying quantity used in the cover-down trajectory.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Currently available triangles containing a prescribed vertex pair. -/
def availableTrianglesContainingPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (P : Finset V) : TripleSystemOn V :=
  S.available.filter fun T ↦ P ⊆ T.1

@[simp]
lemma mem_availableTrianglesContainingPair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : Finset V} {T : TripleOn V} :
    T ∈ availableTrianglesContainingPair S P ↔
      T ∈ S.available ∧ P ⊆ T.1 := by
  simp [availableTrianglesContainingPair]

/-- Uniform cutoff for all two-vertex available codegrees. -/
def HasAvailablePairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (Δ : ℕ) (S : GreedyStateOn V) : Prop :=
  ∀ P : Finset V, P.card = 2 →
    (availableTrianglesContainingPair S P).card ≤ Δ

lemma HasAvailablePairCutoff.mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {Δ Δ' : ℕ}
    (h : HasAvailablePairCutoff Δ S) (hΔ : Δ ≤ Δ') :
    HasAvailablePairCutoff Δ' S := by
  intro P hP
  exact (h P hP).trans hΔ

lemma available_sharingPair_subset_pair_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (U : TripleOn V) :
    S.available ∩ triplesSharingPair U ⊆
      (U.1.powersetCard 2).biUnion fun P ↦
        availableTrianglesContainingPair S P := by
  intro T hT
  have hshare := triplesSharingPair_subset_pair_union U (mem_inter.mp hT).2
  obtain ⟨P, hPU, hTP⟩ := mem_biUnion.mp hshare
  apply mem_biUnion.mpr
  exact ⟨P, hPU, mem_availableTrianglesContainingPair_iff.mpr
    ⟨(mem_inter.mp hT).1,
      mem_universeTriplesContainingPair_iff.mp hTP⟩⟩

/-- A triple has three pairs, hence at most `3Δ` currently available
pair-sharing competitors. -/
theorem card_available_inter_triplesSharingPair_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {Δ : ℕ}
    (hΔ : HasAvailablePairCutoff Δ S) (U : TripleOn V) :
    (S.available ∩ triplesSharingPair U).card ≤ 3 * Δ := by
  calc
    (S.available ∩ triplesSharingPair U).card ≤
        ((U.1.powersetCard 2).biUnion fun P ↦
          availableTrianglesContainingPair S P).card :=
      card_le_card (available_sharingPair_subset_pair_union S U)
    _ ≤ ∑ P ∈ U.1.powersetCard 2,
        (availableTrianglesContainingPair S P).card := card_biUnion_le
    _ ≤ ∑ _P ∈ U.1.powersetCard 2, Δ := by
      apply sum_le_sum
      intro P hP
      exact hΔ P (mem_powersetCard.mp hP).2
    _ = 3 * Δ := by
      rw [sum_const, nsmul_eq_mul, card_powersetCard, U.2]
      norm_num

/-- The deletion obstruction can be intersected with current availability in
its pair-sharing branch. -/
theorem greedyDeleted_available_subset_pairSharing_union_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {U : TripleOn V}
    (hInv : GreedyInvariant F S) (hU : U ∈ S.available) :
    greedyDeletedIn F (univ : TripleSystemOn V) S U ⊆
      (S.available ∩ triplesSharingPair U) ∪
        twoAwayForbiddenTriangles F S.chosen U := by
  intro T hT
  have hTavailable : T ∈ S.available := by
    have hold := (mem_sdiff.mp hT).1
    simpa [greedyAvailableIn] using hold
  rcases mem_union.mp
      (greedyDeletedIn_subset_pairSharing_union_twoAway hInv hU hT) with
    hpair | htwo
  · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hTavailable, hpair⟩))
  · exact mem_union.mpr (Or.inr htwo)

/-- Refined one-step deletion bound. -/
theorem card_greedyDeleted_available_le_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ K : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S)
    {U : TripleOn V} (hU : U ∈ S.available) :
    (greedyDeletedIn F (univ : TripleSystemOn V) S U).card ≤
      3 * Δ + K := by
  calc
    (greedyDeletedIn F (univ : TripleSystemOn V) S U).card ≤
        (S.available ∩ triplesSharingPair U).card +
          (twoAwayForbiddenTriangles F S.chosen U).card :=
      (card_le_card
        (greedyDeleted_available_subset_pairSharing_union_twoAway hInv hU)).trans
        (card_union_le _ _)
    _ ≤ 3 * Δ + K := Nat.add_le_add
      (card_available_inter_triplesSharingPair_le hpair U) (htwo U hU)

/-- Refined availability decrement for one legal step. -/
theorem greedyStep_available_card_le_add_pairEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ K : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S)
    {U : TripleOn V} (hU : U ∈ S.available) :
    S.available.card ≤
      (greedyStep F S U).available.card + (3 * Δ + K) := by
  have hpartition := greedyDeletedIn_card_add_step_card
    F (univ : TripleSystemOn V) S U
  rw [greedyAvailableIn_univ, greedyAvailableIn_univ] at hpartition
  have hdeleted := card_greedyDeleted_available_le_pairCutoff
    hInv hpair htwo hU
  omega

end

end Erdos207
