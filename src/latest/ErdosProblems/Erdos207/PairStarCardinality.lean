/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClosedThreats

/-! # Exact cardinality of the three pair stars through an available triangle -/

namespace Erdos207

open Finset

noncomputable section

theorem distinct_triples_inter_card_le_two
    {V : Type*} [DecidableEq V] {T U : TripleOn V} (hne : T ≠ U) :
    (T.1 ∩ U.1).card ≤ 2 := by
  by_contra! h
  have heq : T.1 ∩ U.1 = T.1 :=
    eq_of_subset_of_card_le inter_subset_left (by rw [T.2]; omega)
  have hsub : T.1 ⊆ U.1 := heq ▸ inter_subset_right
  exact hne (Subtype.ext (eq_of_subset_of_card_le hsub (by rw [T.2, U.2])))

theorem pairStars_erase_root_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (T : TripleOn V) :
    (T.1.powersetCard 2 : Set (Finset V)).PairwiseDisjoint
      (fun P ↦ (availableTrianglesContainingPair S P).erase T) := by
  intro P hP Q hQ hne
  apply disjoint_left.mpr
  intro U hUP hUQ
  have hdP := mem_erase.mp hUP
  have hdQ := mem_erase.mp hUQ
  have hPT := (mem_powersetCard.mp hP).1
  have hQT := (mem_powersetCard.mp hQ).1
  have hPU := (mem_availableTrianglesContainingPair_iff.mp hdP.2).2
  have hQU := (mem_availableTrianglesContainingPair_iff.mp hdQ.2).2
  have hi := distinct_triples_inter_card_le_two (Ne.symm hdP.1)
  have hPeq : P = T.1 ∩ U.1 := eq_of_subset_of_card_le
    (fun x hx ↦ mem_inter.mpr ⟨hPT hx, hPU hx⟩) (by
      rw [(mem_powersetCard.mp hP).2]
      exact hi)
  have hQeq : Q = T.1 ∩ U.1 := eq_of_subset_of_card_le
    (fun x hx ↦ mem_inter.mpr ⟨hQT hx, hQU hx⟩) (by
      rw [(mem_powersetCard.mp hQ).2]
      exact hi)
  exact hne (hPeq.trans hQeq.symm)

theorem biUnion_pairStars_erase_root
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (T : TripleOn V) :
    (T.1.powersetCard 2).biUnion (fun P ↦ (availableTrianglesContainingPair S P).erase T) =
      (S.available ∩ triplesSharingPair T).erase T := by
  ext U
  constructor
  · intro h
    obtain ⟨P, hP, hU⟩ := mem_biUnion.mp h
    have hd := mem_erase.mp hU
    have hstar := mem_availableTrianglesContainingPair_iff.mp hd.2
    apply mem_erase.mpr
    refine ⟨hd.1, mem_inter.mpr ⟨hstar.1, mem_triplesSharingPair_iff.mpr ?_⟩⟩
    have hsub : P ⊆ T.1 ∩ U.1 := fun x hx ↦
      mem_inter.mpr ⟨(mem_powersetCard.mp hP).1 hx, hstar.2 hx⟩
    simpa only [(mem_powersetCard.mp hP).2] using card_le_card hsub
  · intro h
    have hd := mem_erase.mp h
    have hshare := (mem_inter.mp hd.2).2
    obtain ⟨P, hP, hUP⟩ := mem_biUnion.mp (triplesSharingPair_subset_pair_union T hshare)
    exact mem_biUnion.mpr ⟨P, hP, mem_erase.mpr ⟨hd.1,
      mem_availableTrianglesContainingPair_iff.mpr
        ⟨(mem_inter.mp hd.2).1, mem_universeTriplesContainingPair_iff.mp hUP⟩⟩⟩

theorem card_available_pairSharing_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) {T : TripleOn V} (hT : T ∈ S.available) :
    (S.available ∩ triplesSharingPair T).card + 2 =
      ∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card := by
  have hsum := card_biUnion (pairStars_erase_root_pairwiseDisjoint S T)
  rw [biUnion_pairStars_erase_root] at hsum
  have hroot : T ∈ S.available ∩ triplesSharingPair T := by
    refine mem_inter.mpr ⟨hT, mem_triplesSharingPair_iff.mpr ?_⟩
    rw [inter_self, T.2]
    omega
  have hrootcard := card_erase_add_one hroot
  have hstars : (∑ P ∈ T.1.powersetCard 2,
      (availableTrianglesContainingPair S P).card) =
      (∑ P ∈ T.1.powersetCard 2, ((availableTrianglesContainingPair S P).erase T).card) + 3 := by
    calc
      _ = ∑ P ∈ T.1.powersetCard 2,
          (((availableTrianglesContainingPair S P).erase T).card + 1) := by
        apply sum_congr rfl
        intro P hP
        exact (card_erase_add_one (mem_availableTrianglesContainingPair_iff.mpr
          ⟨hT, (mem_powersetCard.mp hP).1⟩)).symm
      _ = _ := by rw [sum_add_distrib]; simp [card_powersetCard, T.2]
  omega

end

end Erdos207
