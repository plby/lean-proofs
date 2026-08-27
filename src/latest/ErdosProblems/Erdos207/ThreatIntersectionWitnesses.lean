/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ClosedThreatCardinality
import ErdosProblems.Erdos207.TerminalLossCount
import ErdosProblems.Erdos207.SelectedWitnessImage

/-! # Witness images covering the intersection of two closed threat sets -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def pairLocalThreatUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) (root selector : TripleOn V) : TripleSystemOn V :=
  univ.biUnion fun P : PairInsideSelector selector ↦ pairTwoAwayForbiddenTriangles F A root P.1

theorem mem_pairLocalThreatUnion_of_sharing_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {root selector U : TripleOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E)
    (hshare : U ∈ triplesSharingPair selector)
    (htwo : U ∈ twoAwayForbiddenTriangles F A root) : U ∈ pairLocalThreatUnion F A root selector := by
  obtain ⟨P, hP, hUP⟩ := mem_biUnion.mp (triplesSharingPair_subset_pair_union selector hshare)
  let p : PairInsideSelector selector := ⟨⟨P, (mem_powersetCard.mp hP).2⟩, (mem_powersetCard.mp hP).1⟩
  have hn : U ∉ triplesSharingPair root := by
    intro h
    exact disjoint_left.mp (disjoint_pairSharing_twoAway_of_packing F A root hpack) h htwo
  exact mem_biUnion.mpr ⟨p, mem_univ p, mem_inter.mpr ⟨hUP, mem_sdiff.mpr ⟨htwo, hn⟩⟩⟩

theorem card_pairLocalThreatUnion_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) (root selector : TripleOn V) :
    ((pairLocalThreatUnion F A root selector).card : ℝ≥0) ≤
      ∑ P : PairInsideSelector selector, selectedCount
        (fun w : PairTwoAwayThreatWitness V F root P.1 ↦ pairTwoAwayThreatRemainder w) A := by
  have hc : ((pairLocalThreatUnion F A root selector).card : ℝ≥0) ≤
      ∑ P : PairInsideSelector selector, ((pairTwoAwayForbiddenTriangles F A root P.1).card : ℝ≥0) := by
    exact_mod_cast (card_biUnion_le (s := univ)
      (t := fun P : PairInsideSelector selector ↦ pairTwoAwayForbiddenTriangles F A root P.1))
  exact hc.trans (sum_le_sum fun P _ ↦ pairTwoAwayForbidden_count_le_selectedCount F A root P.1)

theorem card_pairLocalThreatUnion_le_three_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) (root selector : TripleOn V) (K : ℝ≥0)
    (hK : ∀ P : PairInsideSelector selector, selectedCount
      (fun w : PairTwoAwayThreatWitness V F root P.1 ↦ pairTwoAwayThreatRemainder w) A ≤ K) :
    ((pairLocalThreatUnion F A root selector).card : ℝ≥0) ≤ 3 * K := by
  refine (card_pairLocalThreatUnion_le_sum F A root selector).trans ?_
  calc
    _ ≤ ∑ _P : PairInsideSelector selector, K := sum_le_sum fun P _ ↦ hK P
    _ = 3 * K := by simp [card_pairInsideSelector]

theorem mem_commonThreatImage_of_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T T' U : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) (hT' : T' ∈ S.available)
    (hU : U ∈ S.available) (hne : T ≠ T')
    (htwo : U ∈ twoAwayForbiddenTriangles F S.chosen T)
    (htwo' : U ∈ twoAwayForbiddenTriangles F S.chosen T') :
    U ∈ selectedWitnessImage (fun w : CommonThreatWitness F F T T' ↦ w.remainder)
      (fun w ↦ w.bridge) S.chosen := by
  obtain ⟨hUT, E, hEF, hUE, hTE, hrest⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo
  obtain ⟨hUT', E', hE'F, hUE', hT'E', hrest'⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo'
  let u : TwoAwayThreatWitness V F T := ⟨(E, U), hEF, hUE, hTE, hUT⟩
  let v : TwoAwayThreatWitness V F T' := ⟨(E', U), hE'F, hUE', hT'E', hUT'⟩
  have hu : u ∈ availableTwoAwayWitnesses F S T := mem_availableTwoAwayWitnesses.mpr ⟨hrest, hU⟩
  have hv : v ∈ availableTwoAwayWitnesses F S T' := mem_availableTwoAwayWitnesses.mpr ⟨hrest', hU⟩
  have hp : E ∩ S.available = {T, U} := availableTwoAwayWitness_part hS hT hu
  have hp' : E' ∩ S.available = {T', U} := availableTwoAwayWitness_part hS hT' hv
  have hcross : T' ∈ E → T' = T := by
    intro h
    have hm : T' ∈ ({T, U} : TripleSystemOn V) := hp ▸ mem_inter.mpr ⟨h, hT'⟩
    rcases mem_insert.mp hm with h | h
    · exact h
    · exact (hUT' (mem_singleton.mp h).symm).elim
  have hcross' : T ∈ E' → T = T' := by
    intro h
    have hm : T ∈ ({T', U} : TripleSystemOn V) := hp' ▸ mem_inter.mpr ⟨h, hT⟩
    rcases mem_insert.mp hm with h | h
    · exact h
    · exact (hUT (mem_singleton.mp h).symm).elim
  have hd : E ≠ E' := by
    intro he
    exact hne (hcross (he ▸ hT'E')).symm
  let w : CommonThreatWitness F F T T' :=
    ⟨U, E, E', hEF, hE'F, hTE, hT'E', hUE, hUE', hUT, hUT', hcross, hcross', hd⟩
  refine mem_selectedWitnessImage.mpr ⟨w, ?_, rfl⟩
  change ((E.erase T).erase U) ∪ ((E'.erase T').erase U) ⊆ S.chosen
  apply union_subset
  · simpa only [erase_right_comm] using hrest
  · simpa only [erase_right_comm] using hrest'

theorem closedThreats_inter_subset_witness_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T T' : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) (hT' : T' ∈ S.available)
    (hne : T ≠ T') (hpack : ∀ E ∈ F, IsPackingOn E) :
    greedyClosedThreats F S T ∩ greedyClosedThreats F S T' ⊆
      ((triplesSharingPair T ∩ triplesSharingPair T') ∪ pairLocalThreatUnion F S.chosen T' T) ∪
        (pairLocalThreatUnion F S.chosen T T' ∪ selectedWitnessImage
          (fun w : CommonThreatWitness F F T T' ↦ w.remainder) (fun w ↦ w.bridge) S.chosen) := by
  intro U hU
  have h₁ := mem_inter.mp (mem_inter.mp hU).1
  have h₂ := mem_inter.mp (mem_inter.mp hU).2
  rcases mem_union.mp h₁.2 with hs | ht <;> rcases mem_union.mp h₂.2 with hs' | ht'
  · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hs, hs'⟩))
  · exact mem_union_left _ (mem_union_right _
      (mem_pairLocalThreatUnion_of_sharing_twoAway hpack hs ht'))
  · exact mem_union_right _ (mem_union_left _
      (mem_pairLocalThreatUnion_of_sharing_twoAway hpack hs' ht))
  · exact mem_union_right _ (mem_union_right _
      (mem_commonThreatImage_of_twoAway hS hT hT' h₁.1 hne ht ht'))

end

end Erdos207
