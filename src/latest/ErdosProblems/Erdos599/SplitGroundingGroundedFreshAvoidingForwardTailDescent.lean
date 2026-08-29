/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingForwardHead

/-!
# Rank descent for a fresh-avoiding forward-tail exchange

If a retained forward edge deletes an edge on a component exposed by a
strictly later request, reorient the same deleted-head problem around the
owner of that retained edge.  The recursion key strictly decreases in its
control-rank coordinate.  Consequently only the self-owned forward-tail
case requires the source's last-contact splice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ForwardTailInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ForwardTailIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ForwardTailControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private theorem altDirectionEdge_endpoints_mem_vertexSet
    {D : Digraph V} (Q : Alternating.AltPath D)
    {d : Alternating.Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hlQ, _hld, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  cases Q with
  | trivial v => simp [Alternating.AltPath.links] at hlQ
  | finite T =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩
  | infinite T =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩

/-- A retained forward edge which departs from `Y` makes `Y` an exposed
component of its selected owner. -/
theorem splitGroundedFreshAvoiding_forwardTailOwner_parent_exposed
    (owner : ActiveControlRequestAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (Y : Gamma.DPath)
    (hYL : Y ∈ (ForwardTailInput (L := L) (hL := hL)).ladder.paths)
    (f : V × V)
    (hf : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardTailControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (hftail : f.1 ∈ Y.support) :
    Y ∈ exposedLadderPaths
      (ForwardTailInput (L := L) (hL := hL))
      (strongSelectedPath
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardTailControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)) := by
  let U := ForwardTailIndexed (L := L) (hL := hL) (hground := hground)
  let K := ForwardTailControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let J := ForwardTailInput (L := L) (hL := hL)
  let p := strongSelectedPath U S K (chosenRequest owner.1)
  have hpStart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source
      ⟨chosenRequest owner.1, rfl⟩
  have htailVertex : f.1 ∈
      (selectedErasedCompression U S K
        (chosenRequest owner.1)).path.vertexSet :=
    (altDirectionEdge_endpoints_mem_vertexSet _
      (retainedForwardEdgesAt_subset_directionEdges ∅ _ hf)).1
  have htailCarrier : f.1 ∈ J.decodedVertexCarrier p :=
    GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K (chosenRequest owner.1) htailVertex
  exact J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
    p hpStart hYL htailCarrier hftail

/-- Reclassify a strict lower-rank forward-tail owner as the control of the
same deleted-head state. -/
def SplitGroundedFreshAvoidingRootState.forwardTailLowerRankState
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (u : V)
    (owner : ActiveControlRequestAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
    (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardTailControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (same_tail : u = f.1) :
    L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S) := {
  control := owner
  parent := state.parent
  parent_exposed :=
    L.splitGroundedFreshAvoiding_forwardTailOwner_parent_exposed owner
      state.parent
      (GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
        _ state.parent_exposed)
      f retained (by
        rw [← same_tail]
        exact state.rootPath_support
          (state.rootPath.edgeSet_subset_support_prod parent_edge).1)
  rootPath := state.rootPath
  rootPath_support := state.rootPath_support
  rootPath_edges := state.rootPath_edges
  deleted := state.deleted
  deleted_head_not_rooted := state.deleted_head_not_rooted
  owner := .forwardTail u owner f parent_edge conflict retained same_tail
    (Or.inl rfl) }

/-- Strict owner rank gives a genuine recursive decrease. -/
theorem SplitGroundedFreshAvoidingRootState.forwardTailLowerRankState_precedes
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (u : V)
    (owner : ActiveControlRequestAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
    (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardTailControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (same_tail : u = f.1)
    (rank_lt : controlRank
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        owner.1 < controlRank
          (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
          state.control.1) :
    (state.forwardTailLowerRankState u owner f parent_edge conflict retained
      same_tail).Precedes state := by
  exact Prod.Lex.left _ _ rank_lt

/-- A strict forward-tail owner is eliminated by the existing well-founded
normalizer at the lower-rank state.  Hence the only genuinely new exchange
is the equality branch `owner.1 = state.control.1`. -/
theorem splitGroundedFreshAvoiding_forwardTail_strictOwner_normalized
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (u : V)
    (owner : ActiveControlRequestAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
    (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
      (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardTailControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        (ForwardTailControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (same_tail : u = f.1)
    (_rank_lt : controlRank
        (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
        owner.1 < controlRank
          (ForwardTailIndexed (L := L) (hL := hL) (hground := hground)) S
          state.control.1) :
    L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) :=
  (state.forwardTailLowerRankState u owner f parent_edge conflict retained
    same_tail).normalizeBackward

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingRootState.forwardTailLowerRankState_precedes
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_forwardTail_strictOwner_normalized
