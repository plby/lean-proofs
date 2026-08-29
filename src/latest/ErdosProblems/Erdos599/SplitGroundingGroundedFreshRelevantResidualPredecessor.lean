/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardComponentProtection

/-!
# Residual predecessor closure after a terminal forward cut

If the head of a residual ladder edge lies strictly after a cut vertex on
one ladder member, warp disjointness identifies the edge owner with that
member.  Since a path edge joins consecutive occurrences, the edge tail is
weakly after the cut.  This is the residual half of the carrier-component
closure used by the simultaneous forward exchange.

The non-strict hypothesis at the head would be false: an edge entering the
cut vertex may have its tail strictly before the cut.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The tail of a path edge is weakly after every vertex which is strictly
before its head.  The strictness is essential exactly when the compared
vertex is the head itself. -/
theorem GroundingCut.beforeEq_edgeTail_of_before_edgeHead
    {P : Gamma.DPath} {cut x y : V}
    (hxy : (x, y) ∈ P.edgeSet) (hcut : GroundingCut.Before P cut y) :
    GroundingCut.BeforeEq P cut x := by
  rcases hcut.1 with ⟨m, k, hm, hk, hmk⟩
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      have htail : GroundingCut.OccursAt
          (.inl p : Gamma.DPath) n x :=
        ⟨Nat.lt_of_succ_lt hn, hnx⟩
      have hhead : GroundingCut.OccursAt
          (.inl p : Gamma.DPath) (n + 1) y :=
        ⟨hn, hny⟩
      have hkEq : k = n + 1 :=
        GroundingCutDecoder.occursAt_index_injective hk hhead
      have hmNe : m ≠ n + 1 := by
        intro hmEq
        apply hcut.2
        subst m
        rcases hm with ⟨_hmLen, hmVertex⟩
        exact hmVertex.symm.trans hny
      exact ⟨m, n, hm, htail, by omega⟩
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      have htail : GroundingCut.OccursAt
          (.inr r : Gamma.DPath) n x :=
        (congrArg Prod.fst hn).symm
      have hhead : GroundingCut.OccursAt
          (.inr r : Gamma.DPath) (n + 1) y :=
        (congrArg Prod.snd hn).symm
      have hkEq : k = n + 1 :=
        GroundingCutDecoder.occursAt_index_injective hk hhead
      have hmNe : m ≠ n + 1 := by
        intro hmEq
        apply hcut.2
        subst m
        exact hm.symm.trans hhead
      exact ⟨m, n, hm, htail, by omega⟩

/-- A residual edge whose head lies strictly after a cut on a ladder member
has its tail weakly after the cut on that same member.  No switched-relation
survival premise is needed for this intrinsic predecessor fact. -/
theorem residualLadderEdge_tail_beforeEq_of_head_after
    {kappa : Cardinal.{u}} {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    {parent : Gamma.DPath} (hparent : parent ∈ L.ladder.paths)
    {cut : V} {e : V × V}
    (he : e ∈ residualLadderEdges U S)
    (hhead : GroundingCut.Before parent cut e.2) :
    GroundingCut.BeforeEq parent cut e.1 := by
  obtain ⟨owner, howner, heOwner⟩ := he.1
  have hheadParent : e.2 ∈ parent.support := by
    rcases hhead.1 with ⟨_m, _n, _hm, hn, _hmn⟩
    exact GroundingCut.occursAt_mem_support hn
  have hheadOwner : e.2 ∈ owner.support :=
    (owner.edgeSet_subset_support_prod heOwner).2
  have hparentOwner : parent = owner :=
    DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
      hparent howner hheadParent hheadOwner
  rw [hparentOwner] at hhead ⊢
  exact GroundingCut.beforeEq_edgeTail_of_before_edgeHead heOwner hhead

namespace DWeb.KappaLadder

variable {kappa : Cardinal.{u}}
  {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ResidualPredecessorIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ResidualPredecessorControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ResidualPredecessorFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

/-- Canonical terminal-splice specialization.  `same_tail` and switched
survival are retained in the interface used by the component proof, although
the stronger intrinsic residual-edge lemma needs only residual membership
and strict head position. -/
theorem SplitGroundedReducedForwardConflictSpliceData.residualEdge_tail_beforeEq_incomingTail
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ResidualPredecessorControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ResidualPredecessorFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (_same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    {e : V × V}
    (heResidual : e ∈ residualLadderEdges
      (ResidualPredecessorIndexed (L := L) (hL := hL)
        (hground := hground)) S)
    (_heSurvives : e ∈ erasedSelectedSwitchedEdgesAt
      (ResidualPredecessorIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (ResidualPredecessorControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ResidualPredecessorFrontier (L := L) (hL := hL) (S := S)))
    (hhead : GroundingCut.Before state.parent splice.incomingTail e.2) :
    GroundingCut.BeforeEq state.parent splice.incomingTail e.1 := by
  have hparent : state.parent ∈
      (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths := by
    simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
      using state.parent_mem
  exact residualLadderEdge_tail_beforeEq_of_head_after
    (ResidualPredecessorIndexed (L := L) (hL := hL) (hground := hground))
    S hparent heResidual hhead

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingCut.beforeEq_edgeTail_of_before_edgeHead
#print axioms Erdos599.residualLadderEdge_tail_beforeEq_of_head_after
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.residualEdge_tail_beforeEq_incomingTail
