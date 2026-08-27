/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ThreatIntersectionCount

/-! # A pair star meets closed threats in a bounded pair-local statistic -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_pair_containing_inter_sharing_le_three
    {V : Type*} [Fintype V] [DecidableEq V] (P : PairOn V) (T : TripleOn V)
    (hPT : ¬ P.1 ⊆ T.1) :
    (universeTriplesContainingPair P.1 ∩ triplesSharingPair T).card ≤ 3 := by
  let C := fun Q : Finset V ↦ universeTriplesContainingPair P.1 ∩ universeTriplesContainingPair Q
  have hsub : universeTriplesContainingPair P.1 ∩ triplesSharingPair T ⊆
      (T.1.powersetCard 2).biUnion C := by
    intro U hU
    obtain ⟨Q, hQ, hUQ⟩ := mem_biUnion.mp
      (triplesSharingPair_subset_pair_union T (mem_inter.mp hU).2)
    exact mem_biUnion.mpr ⟨Q, hQ, mem_inter.mpr ⟨(mem_inter.mp hU).1, hUQ⟩⟩
  have hc : ∀ Q ∈ T.1.powersetCard 2, (C Q).card ≤ 1 := by
    intro Q hQ
    apply card_triplesContaining_distinct_pairs_le_one P.2 (mem_powersetCard.mp hQ).2
    intro he
    exact hPT (he ▸ (mem_powersetCard.mp hQ).1)
  calc
    _ ≤ ((T.1.powersetCard 2).biUnion C).card := card_le_card hsub
    _ ≤ ∑ Q ∈ T.1.powersetCard 2, (C Q).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ T.1.powersetCard 2, 1 := sum_le_sum hc
    _ = 3 := by simp [card_powersetCard, T.2]

theorem card_pairStar_inter_closedThreats_le_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : PairOn V) (T : TripleOn V)
    (hPT : ¬ P.1 ⊆ T.1) (hpack : ∀ E ∈ F, IsPackingOn E) :
    ((availableTrianglesContainingPair S P.1 ∩ greedyClosedThreats F S T).card : ℝ≥0) ≤
      3 + selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w)
        S.chosen := by
  let A := universeTriplesContainingPair P.1 ∩ triplesSharingPair T
  let B := pairTwoAwayForbiddenTriangles F S.chosen T P
  have hsub : availableTrianglesContainingPair S P.1 ∩ greedyClosedThreats F S T ⊆ A ∪ B := by
    intro U hU
    have hp := mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hU).1
    have ht := mem_inter.mp (mem_inter.mp hU).2
    have hUP := mem_universeTriplesContainingPair_iff.mpr hp.2
    rcases mem_union.mp ht.2 with hshare | htwo
    · exact mem_union_left _ (mem_inter.mpr ⟨hUP, hshare⟩)
    · apply mem_union_right
      refine mem_inter.mpr ⟨hUP, mem_sdiff.mpr ⟨htwo, ?_⟩⟩
      intro hshare
      exact disjoint_left.mp (disjoint_pairSharing_twoAway_of_packing F S.chosen T hpack)
        hshare htwo
  have hn := (card_le_card hsub).trans (card_union_le A B)
  have ha : (A.card : ℝ≥0) ≤ 3 := by exact_mod_cast card_pair_containing_inter_sharing_le_three P T hPT
  have hb : (B.card : ℝ≥0) ≤ selectedCount
      (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) S.chosen :=
    pairTwoAwayForbidden_count_le_selectedCount F S.chosen T P
  calc
    _ ≤ (A.card : ℝ≥0) + B.card := by exact_mod_cast hn
    _ ≤ _ := add_le_add ha hb

end

end Erdos207
