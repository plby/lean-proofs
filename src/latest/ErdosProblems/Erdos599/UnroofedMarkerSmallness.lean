/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerSpliceGeometry
import ErdosProblems.Erdos599.LadderRecordCardinal

/-!
# Small inessential families at every stage of the actual unroofed ladder

At a nonobstruction stage every inessential successor path was recorded
earlier. Its family is small by the existing injective record-stage bound.
The proved avoiding club and literal persistence give the same bound at
every ordinary stage and its successor. Countable path supports then give
small carriers. No legacy marker-exhaustion predicate is assumed.
-/

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V)

theorem inessentialSuccessor_subset_recordedBefore {a : Stage kappa}
    (ha : a ∉ (ladder G kappa preferred).phi) :
    G.inessentialPaths ((ladder G kappa preferred).successorWarp a) ⊆
      (ladder G kappa preferred).bookkeeping.recordedBefore a := by
  intro p hp
  by_contra hnot
  exact ha ⟨p, hp, hnot⟩

theorem mk_inessentialSuccessor_lt_of_not_mem_phi {a : Stage kappa}
    (ha : a ∉ (ladder G kappa preferred).phi) :
    #(G.inessentialPaths ((ladder G kappa preferred).successorWarp a)) < kappa :=
  (Cardinal.mk_subtype_mono
    (inessentialSuccessor_subset_recordedBefore G kappa preferred ha)).trans_lt
    ((ladder G kappa preferred).mk_recordedBefore_lt a)

variable (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
  (huncountable : aleph0 < kappa) (hG : G.IsUnhindered)

include hNoEnter hkappa huncountable hG in
theorem exists_later_nonobstruction_stage (a : Stage kappa) :
    ∃ b : Stage kappa, a < b ∧ b ∉ (ladder G kappa preferred).phi := by
  obtain ⟨C, hC, hdisj⟩ := not_isStationary_iff.mp
    (ladder_phi_not_stationary G kappa preferred hNoEnter hkappa huncountable hG)
  obtain ⟨b, hb, hab⟩ := Stationary.exists_mem_club_strictlyAbove hkappa hC a
  exact ⟨b, hab, fun hphi ↦ Set.disjoint_left.mp hdisj hphi hb⟩

include hNoEnter hkappa huncountable hG in
theorem mk_inessentialWarpAt_lt (a : Stage kappa) :
    #(G.inessentialPaths ((ladder G kappa preferred).warpAt a)) < kappa := by
  obtain ⟨b, hab, hb⟩ :=
    exists_later_nonobstruction_stage G kappa preferred hNoEnter hkappa huncountable hG a
  have hsub := (ladder_inessential_mono G kappa preferred hNoEnter
    (a := Stage.toExtended a) (b := Stage.toExtended b) hab.le).trans
      (ladder_currentInessentialPersists G kappa preferred hNoEnter b)
  exact (Cardinal.mk_subtype_mono hsub).trans_lt
    (mk_inessentialSuccessor_lt_of_not_mem_phi G kappa preferred hb)

include hNoEnter hkappa huncountable hG in
theorem mk_inessentialSuccessor_lt (a : Stage kappa) :
    #(G.inessentialPaths ((ladder G kappa preferred).successorWarp a)) < kappa := by
  obtain ⟨b, hab, hb⟩ :=
    exists_later_nonobstruction_stage G kappa preferred hNoEnter hkappa huncountable hG a
  have hsub := (ladder_inessential_mono G kappa preferred hNoEnter
    (a := Stage.succExtended a) (b := Stage.toExtended b)
    (show Stage.succExtended a ≤ Stage.toExtended b from
      Order.add_one_le_iff.mpr (show a.1 < b.1 from hab))).trans
      (ladder_currentInessentialPersists G kappa preferred hNoEnter b)
  exact (Cardinal.mk_subtype_mono hsub).trans_lt
    (mk_inessentialSuccessor_lt_of_not_mem_phi G kappa preferred hb)

include hkappa huncountable in
theorem mk_vertexSet_lt_of_small_family (W : Set G.DPath) (hW : #W < kappa) :
    #(G.vertexSet W) < kappa := by
  have heq : G.vertexSet W = ⋃ p ∈ W, p.support := by
    ext x
    simp only [DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [heq]
  exact FamilyTools.mk_biUnion_lt_of_isRegular hkappa hW
    (fun p _ ↦ p.support_countable.le_aleph0.trans_lt huncountable)

include hNoEnter hkappa huncountable hG in
theorem mk_inessentialCarrierAt_lt (a : Stage kappa) :
    #(G.vertexSet (G.inessentialPaths ((ladder G kappa preferred).warpAt a))) < kappa :=
  mk_vertexSet_lt_of_small_family G kappa hkappa huncountable _
    (mk_inessentialWarpAt_lt G kappa preferred hNoEnter hkappa huncountable hG a)

include hNoEnter hkappa huncountable hG in
theorem mk_inessentialSuccessorCarrier_lt (a : Stage kappa) :
    #(G.vertexSet (G.inessentialPaths ((ladder G kappa preferred).successorWarp a))) < kappa :=
  mk_vertexSet_lt_of_small_family G kappa hkappa huncountable _
    (mk_inessentialSuccessor_lt G kappa preferred hNoEnter hkappa huncountable hG a)

#print axioms mk_inessentialSuccessor_lt_of_not_mem_phi
#print axioms mk_inessentialWarpAt_lt
#print axioms mk_inessentialSuccessor_lt
#print axioms mk_inessentialCarrierAt_lt
#print axioms mk_inessentialSuccessorCarrier_lt

end Erdos599.DWeb.UnroofedMarker
