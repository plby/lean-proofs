/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairStarCardinality
import ErdosProblems.Erdos207.TwoAwayCollisionBound
import ErdosProblems.Erdos207.TerminalConfigurationCount

/-! # Closed-threat cardinality with an explicit multiplicity correction -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem disjoint_pairSharing_twoAway_of_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) (T : TripleOn V)
    (hpack : ∀ E ∈ F, IsPackingOn E) :
    Disjoint (triplesSharingPair T) (twoAwayForbiddenTriangles F A T) := by
  apply disjoint_left.mpr
  intro U hshare htwo
  obtain ⟨hne, E, hEF, hUE, hTE, _⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo
  have hlo := mem_triplesSharingPair_iff.mp hshare
  have hhi := (hpack E hEF).inter_card_le_one hTE hUE (Ne.symm hne)
  omega

theorem card_greedyClosedThreats_add_two_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) (hpack : ∀ E ∈ F, IsPackingOn E) :
    (greedyClosedThreats F S T).card + 2 =
      (∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) +
        (S.available ∩ twoAwayForbiddenTriangles F S.chosen T).card := by
  have hset : greedyClosedThreats F S T =
      (S.available ∩ triplesSharingPair T) ∪
        (S.available ∩ twoAwayForbiddenTriangles F S.chosen T) := by
    ext U
    simp only [greedyClosedThreats, mem_inter, mem_union]
    tauto
  have hdis : Disjoint (S.available ∩ triplesSharingPair T)
      (S.available ∩ twoAwayForbiddenTriangles F S.chosen T) :=
    (disjoint_pairSharing_twoAway_of_packing F S.chosen T hpack).mono
      inter_subset_right inter_subset_right
  rw [hset, card_union_of_disjoint hdis]
  have h := card_available_pairSharing_add_two S hT
  omega

theorem card_greedyClosedThreats_add_two_le_witness_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) (hpack : ∀ E ∈ F, IsPackingOn E) :
    (greedyClosedThreats F S T).card + 2 ≤
      (∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) +
        (availableTwoAwayWitnesses F S T).card := by
  rw [card_greedyClosedThreats_add_two_eq F S hT hpack,
    ← image_availableTwoAwayWitnesses]
  exact Nat.add_le_add_left card_image_le _

theorem witness_sum_le_closedThreats_add_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) (hpack : ∀ E ∈ F, IsPackingOn E) :
    ((∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) : ℝ≥0) +
        ((availableTwoAwayWitnesses F S T).card : ℝ≥0) ≤
      ((greedyClosedThreats F S T).card : ℝ≥0) + 2 +
        selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen := by
  have hc := card_greedyClosedThreats_add_two_eq F S hT hpack
  have hc' : ((greedyClosedThreats F S T).card : ℝ≥0) + 2 =
      ((∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) : ℝ≥0) +
        ((S.available ∩ twoAwayForbiddenTriangles F S.chosen T).card : ℝ≥0) := by
    exact_mod_cast hc
  rw [hc', add_assoc]
  exact add_le_add le_rfl (availableTwoAwayWitnesses_card_le_threats_add_common F S T)

theorem abs_closedThreats_sub_witness_sum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) (hpack : ∀ E ∈ F, IsPackingOn E) :
    |((greedyClosedThreats F S T).card : ℝ) -
      (((∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) : ℝ) +
        ((availableTwoAwayWitnesses F S T).card : ℝ) - 2)| ≤
      (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
  have hu : ((greedyClosedThreats F S T).card : ℝ) + 2 ≤
      ((∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) : ℝ) +
        ((availableTwoAwayWitnesses F S T).card : ℝ) := by
    exact_mod_cast card_greedyClosedThreats_add_two_le_witness_sum F S hT hpack
  have hl : ((∑ P ∈ T.1.powersetCard 2, (availableTrianglesContainingPair S P).card) : ℝ) +
        ((availableTwoAwayWitnesses F S T).card : ℝ) ≤
      ((greedyClosedThreats F S T).card : ℝ) + 2 +
        (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
    exact_mod_cast witness_sum_le_closedThreats_add_common F S hT hpack
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem abs_closedThreats_sub_terminal_sum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V} {q : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q) :
    |((greedyClosedThreats F S T).card : ℝ) -
      ((∑ P ∈ T.1.powersetCard 2, ((availableTrianglesContainingPair S P).card : ℝ)) +
        (∑ j ∈ Icc 4 q, ((greedyConfigurationClass
          (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ)) - 2)| ≤
      (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
  have h := abs_closedThreats_sub_witness_sum_le F S hT hpack
  rw [card_availableTwoAwayWitnesses_eq_sum_terminalClasses hS hT hcard] at h
  simpa only [Nat.cast_sum] using h

end

end Erdos207
