/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailableTwoAwayWitnesses
import ErdosProblems.Erdos207.FiniteImageCollisions
import ErdosProblems.Erdos207.GreedyCommonThreatPairs

/-! # The multiplicity error in the two-away threat count -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def availableTwoAwayCollisionWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (p : imageCollisions (availableTwoAwayWitnesses F S T) (fun u ↦ u.1.2)) :
    CommonThreatWitness F F T T := by
  have hd := mem_filter.mp p.2
  have hb := hd.2.2
  refine ⟨p.1.1.1.2, p.1.1.1.1, p.1.2.1.1,
    p.1.1.2.1, p.1.2.2.1, p.1.1.2.2.2.1, p.1.2.2.2.2.1,
    p.1.1.2.2.1, ?_, p.1.1.2.2.2.2, p.1.1.2.2.2.2,
    (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  · change p.1.1.1.2 = p.1.2.1.2 at hb
    rw [hb]
    exact p.1.2.2.2.1
  · intro h
    exact hd.2.1 (Subtype.ext (Prod.ext h hb))

theorem availableTwoAwayCollisionWitness_remainder_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (p : imageCollisions (availableTwoAwayWitnesses F S T) (fun u ↦ u.1.2)) :
    (availableTwoAwayCollisionWitness F S T p).remainder ⊆ S.chosen := by
  have hd := mem_filter.mp p.2
  have hp := mem_product.mp hd.1
  have hl := (mem_availableTwoAwayWitnesses.mp hp.1).1
  have hr := (mem_availableTwoAwayWitnesses.mp hp.2).1
  have hb : p.1.1.1.2 = p.1.2.1.2 := hd.2.2
  change ((p.1.1.1.1.erase T).erase p.1.1.1.2) ∪
    ((p.1.2.1.1.erase T).erase p.1.1.1.2) ⊆ S.chosen
  apply union_subset
  · simpa only [twoAwayThreatRemainder, erase_right_comm] using hl
  · rw [hb]
    simpa only [twoAwayThreatRemainder, erase_right_comm] using hr

theorem availableTwoAwayCollisionWitness_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    Function.Injective (availableTwoAwayCollisionWitness F S T) := by
  intro p q h
  have hfirst := congrArg (fun w : CommonThreatWitness F F T T ↦ w.first) h
  have hsecond := congrArg (fun w : CommonThreatWitness F F T T ↦ w.second) h
  have hbridge := congrArg (fun w : CommonThreatWitness F F T T ↦ w.bridge) h
  have hp : p.1.1.1.2 = p.1.2.1.2 := (mem_filter.mp p.2).2.2
  have hq : q.1.1.1.2 = q.1.2.1.2 := (mem_filter.mp q.2).2.2
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (Prod.ext hfirst hbridge)
  · exact Subtype.ext (Prod.ext hsecond (hp.symm.trans (hbridge.trans hq)))

theorem card_availableTwoAway_collisions_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    ((imageCollisions (availableTwoAwayWitnesses F S T) (fun u ↦ u.1.2)).card : ℝ≥0) ≤
      selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen := by
  classical
  have h := sum_le_sum_of_injective_code (availableTwoAwayCollisionWitness F S T)
    (availableTwoAwayCollisionWitness_injective F S T)
    (fun _ ↦ 1) (fun w ↦ if w.remainder ⊆ S.chosen then 1 else 0) (by
      intro p
      rw [if_pos (availableTwoAwayCollisionWitness_remainder_subset F S T p)])
  simpa only [selectedCount, sum_const, card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one] using h

theorem availableTwoAwayWitnesses_card_le_threats_add_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    ((availableTwoAwayWitnesses F S T).card : ℝ≥0) ≤
      ((S.available ∩ twoAwayForbiddenTriangles F S.chosen T).card : ℝ≥0) +
        selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder) S.chosen := by
  have h := card_le_card_image_add_collisions (availableTwoAwayWitnesses F S T) (fun u ↦ u.1.2)
  rw [image_availableTwoAwayWitnesses] at h
  have hcast : ((availableTwoAwayWitnesses F S T).card : ℝ≥0) ≤
      ((S.available ∩ twoAwayForbiddenTriangles F S.chosen T).card : ℝ≥0) +
        ((imageCollisions (availableTwoAwayWitnesses F S T) (fun u ↦ u.1.2)).card : ℝ≥0) := by
    exact_mod_cast h
  exact hcast.trans (add_le_add le_rfl (card_availableTwoAway_collisions_le_selectedCount F S T))

end

end Erdos207
