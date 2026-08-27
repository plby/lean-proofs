/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairExtensionDeletionDrift

/-!
# Exact closed threat sets for the constrained greedy process

Closed threats include the selected triangle itself.  This convention
retains the diagonal contribution in the exact pair-star drift identity.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

def greedyClosedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    TripleSystemOn V :=
  S.available ∩ (triplesSharingPair T ∪ twoAwayForbiddenTriangles F S.chosen T)

def greedyOpenThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    TripleSystemOn V := (greedyClosedThreats F S T).erase T

theorem mem_greedyDeletedIn_univ_of_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T U : TripleOn V}
    (hU : U ∈ S.available)
    (htwo : U ∈ twoAwayForbiddenTriangles F S.chosen T) :
    U ∈ greedyDeletedIn F (univ : TripleSystemOn V) S T := by
  obtain ⟨hUT, C, hCF, hUC, hTC, hrest⟩ :=
    mem_twoAwayForbiddenTriangles_iff.mp htwo
  apply mem_sdiff.mpr
  refine ⟨by simp [greedyAvailableIn, hU], ?_⟩
  intro hnext
  have hlegal : IsLegalExtension F (insert T S.chosen) U :=
    (mem_legalAvailable_iff.mp (mem_inter.mp hnext).1).2
  apply hlegal.2.2 C hCF
  intro W hWC
  by_cases hWU : W = U
  · simp [hWU]
  by_cases hWT : W = T
  · simp [hWT]
  exact mem_insert_of_mem (mem_insert_of_mem
    (hrest (mem_erase.mpr ⟨hWT, mem_erase.mpr ⟨hWU, hWC⟩⟩)))

theorem greedyDeletedIn_eq_inter_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (Q : TripleSystemOn V) :
    greedyDeletedIn F Q S T = Q ∩ greedyClosedThreats F S T := by
  ext U
  constructor
  · intro hU
    have hmem := mem_inter.mp (mem_sdiff.mp hU).1
    exact mem_inter.mpr ⟨hmem.2, mem_inter.mpr ⟨hmem.1,
      greedyDeletedIn_subset_pairSharing_union_twoAway hS hT hU⟩⟩
  · intro hU
    obtain ⟨hUQ, hUA, hcause⟩ :=
      show U ∈ Q ∧ U ∈ S.available ∧
        U ∈ triplesSharingPair T ∪ twoAwayForbiddenTriangles F S.chosen T from
          ⟨(mem_inter.mp hU).1, (mem_inter.mp (mem_inter.mp hU).2).1,
            (mem_inter.mp (mem_inter.mp hU).2).2⟩
    have hdel : U ∈ greedyDeletedIn F (univ : TripleSystemOn V) S T := by
      rcases mem_union.mp hcause with hshare | htwo
      · exact mem_greedyDeletedIn_univ_of_pairSharing hS hT hUA hshare
      · exact mem_greedyDeletedIn_univ_of_twoAway hUA htwo
    refine mem_sdiff.mpr ⟨mem_inter.mpr ⟨hUA, hUQ⟩, ?_⟩
    intro hnext
    exact (mem_sdiff.mp hdel).2
      (mem_inter.mpr ⟨(mem_inter.mp hnext).1, mem_univ U⟩)

theorem mem_greedyClosedThreats_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) : T ∈ greedyClosedThreats F S T := by
  refine mem_inter.mpr ⟨hT, mem_union.mpr (Or.inl ?_)⟩
  rw [mem_triplesSharingPair_iff, inter_self, T.2]
  norm_num

theorem mem_greedyClosedThreats_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T U : TripleOn V}
    (hT : T ∈ S.available) (hU : U ∈ S.available) :
    U ∈ greedyClosedThreats F S T ↔ T ∈ greedyClosedThreats F S U := by
  simp only [greedyClosedThreats, mem_inter, hT, hU, true_and, mem_union]
  rw [mem_twoAwayForbiddenTriangles_comm]
  have hshare : U ∈ triplesSharingPair T ↔ T ∈ triplesSharingPair U := by
    simp only [mem_triplesSharingPair_iff, inter_comm]
  rw [hshare]

theorem greedyClosedThreats_card_eq_open_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) :
    (greedyClosedThreats F S T).card = (greedyOpenThreats F S T).card + 1 := by
  exact (card_erase_add_one (mem_greedyClosedThreats_self F S hT)).symm

theorem pairStar_subset_closedThreats
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    {P : Finset V} (hP : P.card = 2) {U : TripleOn V}
    (hU : U ∈ availableTrianglesContainingPair S P) :
    availableTrianglesContainingPair S P ⊆ greedyClosedThreats F S U := by
  intro T hT
  obtain ⟨hTA, hPT⟩ := mem_availableTrianglesContainingPair_iff.mp hT
  have hPU := (mem_availableTrianglesContainingPair_iff.mp hU).2
  refine mem_inter.mpr ⟨hTA, mem_union.mpr (Or.inl ?_)⟩
  rw [mem_triplesSharingPair_iff]
  calc
    2 = P.card := hP.symm
    _ ≤ (U.1 ∩ T.1).card := card_le_card
      (fun x hx ↦ mem_inter.mpr ⟨hPU hx, hPT hx⟩)

/-- Exact transposed pair-star loss over selectors not covering the pair. -/
theorem sum_nonPair_closedThreats_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    {P : Finset V} (hP : P.card = 2) :
    let Q := availableTrianglesContainingPair S P
    ∑ T ∈ S.available \ Q, (Q ∩ greedyClosedThreats F S T).card =
      ∑ U ∈ Q, ((greedyClosedThreats F S U).card - Q.card) := by
  dsimp only
  let Q := availableTrianglesContainingPair S P
  have hQ : Q ⊆ S.available := fun _ h ↦
    (mem_availableTrianglesContainingPair_iff.mp h).1
  change (∑ T ∈ S.available \ Q, (Q ∩ greedyClosedThreats F S T).card) = _
  calc
    (∑ T ∈ S.available \ Q, (Q ∩ greedyClosedThreats F S T).card) =
        ∑ T ∈ S.available \ Q, ∑ U ∈ Q,
          if U ∈ greedyClosedThreats F S T then 1 else 0 := by
      apply sum_congr rfl
      intro T _
      rw [card_eq_sum_ones, ← sum_filter]
      congr 1
    _ = ∑ U ∈ Q, ∑ T ∈ S.available \ Q,
          if T ∈ greedyClosedThreats F S U then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro U hU
      apply sum_congr rfl
      intro T hT
      simp only [mem_greedyClosedThreats_comm F S (mem_sdiff.mp hT).1 (hQ hU)]
    _ = ∑ U ∈ Q, ((greedyClosedThreats F S U).card - Q.card) := by
      apply sum_congr rfl
      intro U hU
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have hset : {T ∈ S.available \ Q | T ∈ greedyClosedThreats F S U} =
          greedyClosedThreats F S U \ Q := by
        ext T
        simp only [mem_filter, mem_sdiff]
        have hsub : greedyClosedThreats F S U ⊆ S.available := inter_subset_left
        constructor
        · rintro ⟨⟨_, hn⟩, hm⟩
          exact ⟨hm, hn⟩
        · rintro ⟨hm, hn⟩
          exact ⟨⟨hsub hm, hn⟩, hm⟩
      rw [hset, card_sdiff_of_subset (pairStar_subset_closedThreats F S hP hU)]
      rfl

end

end Erdos207
