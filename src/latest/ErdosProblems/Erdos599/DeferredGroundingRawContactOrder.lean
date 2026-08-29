/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawBackwardOwner
import ErdosProblems.Erdos599.GroundingSelectedBackwardOrder

/-!
# Blocking order for actual raw forward and backward steps

Relevant fragments avoid all starting records. Thus their contacts with
forward insertions come from the proxy-free suffix. The original gadget
order lemmas apply directly, without claiming an erased-edge identity.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "D" => reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S)

/-- No relevant fragment meets any selected starting record. -/
theorem reservedRawRelevantFragment_disjoint_startingRecord
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0) :
    Disjoint P.path.support (reservedStrongSelectedStartingRecord r).record.support := by
  apply Set.disjoint_left.2
  intro x hxP hxH
  have hparent : P.parent = (reservedStrongSelectedStartingRecord r).record :=
    DWeb.IsWarp.eq_of_mem_support (J).ladder.disjoint P.parent_mem
      (reservedStrongSelectedStartingRecord r).record_mem_ladder (P.support_subset hxP) hxH
  have hblockP := GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
  have hblockH : GroundingCut.blockingPoint J S.cut P ∈
      (reservedStrongSelectedStartingRecord r).record.support :=
    hparent ▸ P.support_subset hblockP
  have hblockBB : GroundingCut.blockingPoint J S.cut P ∈
      reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S) :=
    Or.inr ⟨P, hP, rfl⟩
  exact Set.disjoint_left.1 (reservedStrongSelectedStartingRecord_disjoint_relevantBB r)
    hblockBB hblockH

/-- A backward tail is weakly before its fragment's blocker, or is an old
cut vertex. This applies to the literal un-erased request word. -/
theorem reservedRawBackwardTail_beforeEq_or_mem_CV
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (hxP : e.1 ∈ P.path.support) :
    GroundingCut.BeforeEq P.path e.1 (GroundingCut.blockingPoint J S.cut P) ∨
      e.1 ∈ GroundingCut.CV J S.cut := by
  have hgadget := reservedRawRequestBackward_gadget r he
  exact GroundingSelectedBackwardOrder.strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
    U S K r P ((D).relevantG0_subset_legacyG0 hP) hP.1.2 hgadget.1
    (fun h ↦ hgadget.2 (h.symm ▸ requestAuxVertex_mem_cut r)) hxP

/-- A raw inserted departure from a relevant fragment satisfies the same
boundary-complete order bound. The attachment/proxy case is impossible. -/
theorem reservedRawForwardTail_beforeEq_or_mem_CV
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {x y : V} (he : (x, y) ∈ (reservedRawOwnerAttachment r).forwardEdges)
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x (GroundingCut.blockingPoint J S.cut P) ∨
      x ∈ GroundingCut.CV J S.cut := by
  let A := reservedRawOwnerAttachment r
  have hlegacy := (D).relevantG0_subset_legacyG0 hP
  rcases he with hfirst | htail
  · have hx : x = A.anchor := congrArg Prod.fst (Set.mem_singleton_iff.1 hfirst)
    exact (Set.disjoint_left.1
      (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
      hxP (hx ▸ A.anchor_mem_owner)).elim
  · obtain ⟨⟨a, b, hab, hchoice⟩, _hne⟩ := htail
    have hc := (J).chosenConnector?_eq_some hchoice
    have haTail := (A.tail.edgeSet_subset_support_prod hab).1
    have habOriginal := A.tail_edges_subset hab
    have haNotApex : a ≠ requestAuxVertex r := by
      intro h
      exact (FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) habOriginal)
        (h.trans (strongSelectedPath_finish U S K r).symm)
    rcases hc.1 with hexit | ⟨i, hai, _hxi⟩
    · cases a with
      | old z =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          exact Or.inl
            (GroundingSelectedContactOrder.strongSelectedPath_contact_beforeEq_blockingPoint
              S K r P hlegacy hP.1.2 (A.tail_support_subset haTail) hxP haNotApex)
      | edge z w =>
          have hzx : z = x := Option.some.inj hexit
          subst z
          exact
            GroundingSelectedBackwardOrder.strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
              U S K r P hlegacy hP.1.2 (A.tail_support_subset haTail) haNotApex hxP
      | proxy i => simp at hexit
    · subst a
      exact (A.tail_no_proxy i haTail).elim

/-- The entire simultaneous forward relation satisfies the raw bound. -/
theorem reservedRawGlobalForwardTail_beforeEq_or_mem_CV
    (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    {x y : V}
    (he : (x, y) ∈ reservedRawForwardEdges (L := L) (hL := hL) (S := S))
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x (GroundingCut.blockingPoint J S.cut P) ∨
      x ∈ GroundingCut.CV J S.cut := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 he
  exact reservedRawForwardTail_beforeEq_or_mem_CV r P hP hr hxP

#print axioms reservedRawRelevantFragment_disjoint_startingRecord
#print axioms reservedRawBackwardTail_beforeEq_or_mem_CV
#print axioms reservedRawGlobalForwardTail_beforeEq_or_mem_CV

end Erdos599.DWeb.KappaLadder.Deferred
