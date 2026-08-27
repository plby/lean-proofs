/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStateConsequences
import ErdosProblems.Erdos207.GreedyDeletionIncidence

/-! # Pair-local and common-witness bounds for non-pair threats -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_pairStar_inter_twoAway_le_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : PairOn V) (T : TripleOn V)
    (hpack : ∀ E ∈ F, IsPackingOn E) :
    ((availableTrianglesContainingPair S P.1 ∩ availableTwoAwayForbiddenTriangles F S T).card : ℝ≥0) ≤
      selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w)
        S.chosen := by
  have hsub : availableTrianglesContainingPair S P.1 ∩ availableTwoAwayForbiddenTriangles F S T ⊆
      pairTwoAwayForbiddenTriangles F S.chosen T P := by
    intro U hU
    have hp := mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hU).1
    have ht := (mem_availableTwoAwayForbiddenTriangles_iff.mp (mem_inter.mp hU).2).2
    refine mem_inter.mpr ⟨mem_universeTriplesContainingPair_iff.mpr hp.2,
      mem_sdiff.mpr ⟨ht, ?_⟩⟩
    exact fun hs ↦ disjoint_left.mp (disjoint_pairSharing_twoAway_of_packing F S.chosen T hpack) hs ht
  exact (show ((availableTrianglesContainingPair S P.1 ∩ availableTwoAwayForbiddenTriangles F S T).card : ℝ≥0) ≤
    (pairTwoAwayForbiddenTriangles F S.chosen T P).card by exact_mod_cast card_le_card hsub).trans
      (pairTwoAwayForbidden_count_le_selectedCount F S.chosen T P)

theorem card_twoAway_inter_le_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    {T T' : TripleOn V} (hT : T ∈ S.available) (hT' : T' ∈ S.available) (hne : T ≠ T') :
    ((availableTwoAwayForbiddenTriangles F S T ∩ availableTwoAwayForbiddenTriangles F S T').card : ℝ≥0) ≤
      selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) S.chosen := by
  have hsub : availableTwoAwayForbiddenTriangles F S T ∩ availableTwoAwayForbiddenTriangles F S T' ⊆
      selectedWitnessImage (fun w : CommonThreatWitness F F T T' ↦ w.remainder)
        (fun w ↦ w.bridge) S.chosen := by
    intro U hU
    have h₁ := mem_availableTwoAwayForbiddenTriangles_iff.mp (mem_inter.mp hU).1
    have h₂ := mem_availableTwoAwayForbiddenTriangles_iff.mp (mem_inter.mp hU).2
    exact mem_commonThreatImage_of_twoAway hS hT hT' h₁.1 hne h₁.2 h₂.2
  exact (show ((availableTwoAwayForbiddenTriangles F S T ∩ availableTwoAwayForbiddenTriangles F S T').card : ℝ≥0) ≤
      (selectedWitnessImage (fun w : CommonThreatWitness F F T T' ↦ w.remainder)
        (fun w ↦ w.bridge) S.chosen).card by exact_mod_cast card_le_card hsub).trans
          (card_selectedWitnessImage_le_selectedCount _ _ S.chosen)

theorem abs_twoAway_card_sub_terminal_sum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ}
    (hS : GreedyInvariant F S) {T : TripleOn V} (hT : T ∈ S.available)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q) :
    |((availableTwoAwayForbiddenTriangles F S T).card : ℝ) -
      ∑ j ∈ Icc 4 q,
        ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ)| ≤
      (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
  have hu : (availableTwoAwayForbiddenTriangles F S T).card ≤ (availableTwoAwayWitnesses F S T).card := by
    rw [availableTwoAwayForbiddenTriangles, ← image_availableTwoAwayWitnesses]
    exact card_image_le
  have hl := availableTwoAwayWitnesses_card_le_threats_add_common F S T
  have hu' : ((availableTwoAwayForbiddenTriangles F S T).card : ℝ) ≤
      (availableTwoAwayWitnesses F S T).card := by exact_mod_cast hu
  have hl' : ((availableTwoAwayWitnesses F S T).card : ℝ) ≤
      (availableTwoAwayForbiddenTriangles F S T).card +
        (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen : ℝ) := by
    exact_mod_cast hl
  rw [← Nat.cast_sum, ← card_availableTwoAwayWitnesses_eq_sum_terminalClasses hS hT hcard]
  rw [abs_of_nonpos (sub_nonpos.mpr hu')]
  linarith only [hl']

end

end Erdos207
