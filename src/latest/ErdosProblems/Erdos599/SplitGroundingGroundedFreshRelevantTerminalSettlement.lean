/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardSpliceNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardAnchorNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantControlNormalization

/-!
# Settling repeated native-frontier terminal descents

A forward-splice or boundary-departure terminal is not a final obstruction.
Both either make genuine route progress or restart normalization at a
strictly earlier point of the same finite ladder path.  Forward anchors
restart the native normalizer, rooted backward owners advance along their
literal selected route, and represented-cut controls enter the stopped-
control normalizer.  Thus no abstract local terminal remains.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev SettlementControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev SettlementRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev SettlementFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev SettlementEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (SettlementControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (SettlementFrontier (L := L) (hL := hL) (S := S))

private abbrev SettlementSources : Set V :=
  Gamma.source \ {
    (SettlementRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- Exact route-order advance obtained from a rooted selected backward-link
exit.  The third branch retains the original and later finite-route indices
and the concrete native-frontier normalization of the later owner. -/
def SplitGroundedFreshRelevantBackwardLinkAdvance
    (owner : ActiveControlRequestAt
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (SettlementControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (SettlementFrontier (L := L) (hL := hL) (S := S)))
    (link : Alternating.Link Gamma.graph) : Prop :=
  (∃ b ∈ SettlementFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ SettlementSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a b) ∨
    (∃ a ∈ SettlementSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SettlementEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a
        (requestExit (chosenRequest owner.1))) ∨
    ∃ (Q : Alternating.FiniteTrace Gamma.graph)
        (i j : Fin (Q.lastIndex + 1))
        (backward : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
        (state : L.SplitGroundedFreshRelevantBackwardState
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)),
      (selectedErasedCompression
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path = .finite Q ∧
      Q.link i = link ∧ Q.link j = backward ∧ i < j ∧
      backward.direction = .backward ∧
      parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
      backward.path.IsSubpathOf parent ∧ state.control = owner ∧
      state.parent = parent ∧
      L.SplitGroundedFreshRelevantBackwardNormalizationResult state

/-- Genuine route progress attached to the exact terminal outcome which
produced it.  This indexing is essential: a rooted frontier point or request
exit is exchange data for that terminal, not coverage of an unrelated failed
frontier point. -/
inductive SplitGroundedFreshRelevantTerminalProgressAt :
    L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) → Prop
  | forwardLinkFirstHit
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := SettlementControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        state.parent state.rootPath state.deleted)
      (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
      (owner_eq : splice.contact.owner.1 = state.control.1)
      (data : L.SplitGroundedFreshRelevantForwardLinkFirstHit
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)
        (SettlementSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) splice.contact.owner) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.forwardSplice state splice same_tail owner_eq)
  | forwardFirstHit
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := SettlementControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        state.parent state.rootPath state.deleted)
      (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
      (owner_eq : splice.contact.owner.1 = state.control.1)
      (data : L.SplitGroundedFreshRelevantForwardFirstHit
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)
        (SettlementSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) state splice) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.forwardSplice state splice same_tail owner_eq)
  | forwardRequestExit
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := SettlementControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        state.parent state.rootPath state.deleted)
      (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
      (owner_eq : splice.contact.owner.1 = state.control.1)
      (owner : ActiveControlRequestAt
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S)))
      (rooted : ∃ a ∈ SettlementSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a
          (requestExit (chosenRequest owner.1)))
      (owner_eq_splice : owner = splice.contact.owner) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.forwardSplice state splice same_tail owner_eq)
  | forwardLaterBackward
      (state0 : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := SettlementControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        state0.parent state0.rootPath state0.deleted)
      (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
      (owner_eq0 : splice.contact.owner.1 = state0.control.1)
      (owner : ActiveControlRequestAt
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S)))
      (Q : Alternating.FiniteTrace Gamma.graph)
      (i j : Fin (Q.lastIndex + 1))
      (forward backward : Alternating.Link Gamma.graph)
      (parent : Gamma.DPath)
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (route_eq : (selectedErasedCompression
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path = .finite Q)
      (forward_eq : Q.link i = forward)
      (backward_eq : Q.link j = backward)
      (index_lt : i < j)
      (forward_direction : forward.direction = .forward)
      (backward_direction : backward.direction = .backward)
      (parent_mem : parent ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths)
      (backward_subpath : backward.path.IsSubpathOf parent)
      (state_control : state.control = owner)
      (state_parent : state.parent = parent)
      (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state)
      (owner_eq_splice : owner = splice.contact.owner) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.forwardSplice state0 splice same_tail owner_eq0)
  | anchorNormalization
      (state0 : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := SettlementControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        state0.parent state0.rootPath state0.deleted)
      (anchor : ActiveRetainedForwardVertexUnrootedOutcome
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S))
        (SettlementSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) splice.contact.owner)
      (owner : ActiveControlRequestAt
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S)))
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (state_control : state.control = owner)
      (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state)
      (owner_eq_splice : owner = splice.contact.owner) :
      SplitGroundedFreshRelevantTerminalProgressAt (.forwardAnchor state0 splice anchor)
  | boundaryFrontier
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (residual : (tail, state.deleted.head) ∈ residualLadderEdges
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S)
      (tail_mem : tail ∈ SettlementFrontier
        (L := L) (hL := hL) (S := S))
      (rooted : ∃ a ∈ SettlementSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a tail) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.boundaryDeparture state tail incoming_mem residual tail_mem)
  | rootedBackwardAdvance
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (owner : ActiveControlRequestAt
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S)))
      (link : Alternating.Link Gamma.graph)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (selected_backward : (tail, state.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (SettlementControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (SettlementFrontier (L := L) (hL := hL) (S := S)) .backward)
      (link_mem : link ∈ (selectedErasedCompression
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (SettlementControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.links)
      (link_direction : link.direction = .backward)
      (edge_mem_link : (tail, state.deleted.head) ∈ link.path.edgeSet)
      (link_subpath : link.path.IsSubpathOf state.parent)
      (rooted : ∃ a ∈ SettlementSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a link.path.start)
      (advance : SplitGroundedFreshRelevantBackwardLinkAdvance owner link) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.rootedBackward state tail owner link incoming_mem selected_backward
          link_mem link_direction edge_mem_link link_subpath rooted)
  | controlNormalization
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (cut_edge : (tail, state.deleted.head) ∈ GroundingCut.CE
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (control : ControlRequest
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (control_eq : control.1 = state.deleted.head)
      (resolution : SplitGroundedRelevantControlResolutionAt
        (SettlementRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (SettlementFrontier (L := L) (hL := hL) (S := S)) control)
      (normalization : L.SplitGroundedFreshRelevantControlNormalizationAt
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) control) :
      SplitGroundedFreshRelevantTerminalProgressAt
        (.control state tail incoming_mem cut_edge control control_eq resolution)

/-- Progress rebased to the state whose normalization is being settled. -/
def SplitGroundedFreshRelevantBackwardProgressResult
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) : Prop :=
  ∃ outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    outcome.terminalState.parent = initial.parent ∧
      GroundingCut.BeforeEq initial.parent
        outcome.terminalState.deleted.head initial.deleted.head ∧
      GroundingCut.BeforeEq initial.parent
        outcome.terminalState.rootPath.finish initial.rootPath.finish ∧
      SplitGroundedFreshRelevantTerminalProgressAt outcome

/-- This predicate is retained as the empty terminal case of the recursive
proof.  Every concrete terminal is converted to exact, outcome-indexed route
or control-normalization progress. -/
def SplitGroundedFreshRelevantBackwardNormalizedOutcome.IsSettled :
    L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) → Prop
  | .control .. => False
  | .rootedBackward .. => False
  | .forwardAnchor .. => False
  | .forwardSplice .. => False
  | .boundaryDeparture .. => False

/-- A settled result remains indexed by its original state and retains the
same-parent/deleted-head ancestry supplied by the main normalizer. -/
def SplitGroundedFreshRelevantBackwardSettledResult
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) : Prop :=
  ∃ outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    outcome.terminalState.parent = initial.parent ∧
      GroundingCut.BeforeEq initial.parent
        outcome.terminalState.deleted.head initial.deleted.head ∧
      GroundingCut.BeforeEq initial.parent
        outcome.terminalState.rootPath.finish initial.rootPath.finish ∧
      outcome.IsSettled

private def settlementPosition
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) : ℕ :=
  freshRelevantPathPosition state.parent state.deleted.head

/-- A terminal outcome attached definitionally to its own state settles by
finite induction on the deleted-head position. -/
private theorem settleSelfTerminal
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hstate : outcome.terminalState = state) :
    L.SplitGroundedFreshRelevantBackwardProgressResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        state ∨
      L.SplitGroundedFreshRelevantBackwardSettledResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        state := by
  let rel := InvImage (fun m n : ℕ ↦ m < n)
    (@settlementPosition V Gamma kappa L hL hground hnotFresh S)
  have hwf : WellFounded rel :=
    InvImage.wf (@settlementPosition V Gamma kappa L hL hground hnotFresh S)
      Nat.lt_wfRel.wf
  induction state using hwf.induction generalizing outcome with
  | h state ih =>
      subst state
      cases outcome with
      | control state tail hin hcut control heq resolution =>
          let normalization := resolution.normalizeFreshRelevant
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) control
          refine Or.inl ⟨(.control state tail hin hcut control heq resolution),
            rfl, ?_, ?_, ?_⟩
          · exact GroundingCut.beforeEq_refl state.deleted_head_mem
          · exact GroundingCut.beforeEq_refl
              (state.rootPath_support state.rootPath.finish_mem_support)
          · exact .controlNormalization state tail hin hcut control heq
              resolution normalization
      | rootedBackward state tail owner link hin hselected hlink hdir heLink
          hsub hroot =>
          have hadvance :
              SplitGroundedFreshRelevantBackwardLinkAdvance owner link :=
            L.splitGroundedFreshRelevant_backwardLinkStart_advances_or_backwardNormalization
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)
              owner link hlink hdir hroot
          refine Or.inl ⟨(.rootedBackward state tail owner link hin hselected
            hlink hdir heLink hsub hroot), rfl, ?_, ?_, ?_⟩
          · exact GroundingCut.beforeEq_refl state.deleted_head_mem
          · exact GroundingCut.beforeEq_refl
              (state.rootPath_support state.rootPath.finish_mem_support)
          · exact .rootedBackwardAdvance state tail owner link hin hselected
              hlink hdir heLink hsub hroot hadvance
      | forwardAnchor state splice anchor =>
          obtain ⟨next, hcontrol, hresult⟩ :=
            SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardAnchor_has_backwardNormalization
              state splice anchor
          refine Or.inl ⟨(.forwardAnchor state splice anchor), rfl, ?_, ?_, ?_⟩
          · exact GroundingCut.beforeEq_refl state.deleted_head_mem
          · exact GroundingCut.beforeEq_refl
              (state.rootPath_support state.rootPath.finish_mem_support)
          · exact .anchorNormalization state splice anchor
              splice.contact.owner next hcontrol hresult rfl
      | forwardSplice state splice same_tail owner_eq =>
          rcases
              SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictNormalization
                state splice same_tail with hhead | hstrict
          · rcases
                SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances_exact
                  state splice hhead with hfrontier | hfinish
            · obtain ⟨firstHit⟩ := hfrontier
              refine Or.inl ⟨(.forwardSplice state splice same_tail owner_eq),
                rfl, ?_, ?_, ?_⟩
              · exact GroundingCut.beforeEq_refl state.deleted_head_mem
              · exact GroundingCut.beforeEq_refl
                  (state.rootPath_support state.rootPath.finish_mem_support)
              · exact .forwardFirstHit state splice same_tail owner_eq firstHit
            · obtain ⟨forward, hforward, hdir, _hedge, hroot⟩ := hfinish
              rcases
                  L.splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization_exact
                    (hL := hL) (hground := hground)
                    (hnotFresh := hnotFresh) (S := S)
                    splice.contact.owner forward hforward hdir hroot with
                hfrontier | hexit |
                  ⟨Q, i, j, backward, parent, next, hroute, hi, hj, hij,
                    hbdir, hparent, hbsub, hcontrol, hnextParent, hnext⟩
              · obtain ⟨firstHit⟩ := hfrontier
                refine Or.inl ⟨(.forwardSplice state splice same_tail owner_eq),
                  rfl, ?_, ?_, ?_⟩
                · exact GroundingCut.beforeEq_refl state.deleted_head_mem
                · exact GroundingCut.beforeEq_refl
                    (state.rootPath_support state.rootPath.finish_mem_support)
                · exact .forwardLinkFirstHit state splice same_tail owner_eq firstHit
              · refine Or.inl ⟨(.forwardSplice state splice same_tail owner_eq),
                  rfl, ?_, ?_, ?_⟩
                · exact GroundingCut.beforeEq_refl state.deleted_head_mem
                · exact GroundingCut.beforeEq_refl
                    (state.rootPath_support state.rootPath.finish_mem_support)
                · exact .forwardRequestExit state splice same_tail owner_eq
                    splice.contact.owner hexit rfl
              · refine Or.inl ⟨(.forwardSplice state splice same_tail owner_eq),
                  rfl, ?_, ?_, ?_⟩
                · exact GroundingCut.beforeEq_refl state.deleted_head_mem
                · exact GroundingCut.beforeEq_refl
                    (state.rootPath_support state.rootPath.finish_mem_support)
                · exact .forwardLaterBackward state splice same_tail owner_eq
                    splice.contact.owner Q i j forward backward parent next
                    hroute hi hj hij hdir hbdir hparent hbsub hcontrol
                    hnextParent hnext rfl
          · obtain ⟨strict⟩ := hstrict
            have hlt : rel strict.outcome.terminalState state := by
              change settlementPosition strict.outcome.terminalState <
                settlementPosition state
              dsimp only [settlementPosition]
              rw [strict.same_parent]
              exact freshRelevantPathPosition_lt_of_before state.parent
                strict.terminal_head_before
            rcases ih strict.outcome.terminalState hlt strict.outcome rfl with
              hprogress | ⟨terminal, hparent, hbefore, hfinish, hsettled⟩
            · obtain ⟨terminal, hparent, hbefore, hfinish,
                  hterminalProgress⟩ :=
                hprogress
              have hbefore' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.deleted.head
                  strict.outcome.terminalState.deleted.head := by
                simpa only [strict.same_parent] using hbefore
              have hfinish' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.rootPath.finish
                  strict.outcome.terminalState.rootPath.finish := by
                simpa only [strict.same_parent] using hfinish
              exact Or.inl ⟨terminal, hparent.trans strict.same_parent,
                GroundingFragmentResidualOrder.beforeEq_trans hbefore'
                  strict.terminal_head_before.1,
                GroundingFragmentResidualOrder.beforeEq_trans
                  hfinish' strict.terminal_finish_beforeEq,
                hterminalProgress⟩
            · have hbefore' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.deleted.head
                  strict.outcome.terminalState.deleted.head := by
                simpa only [strict.same_parent] using hbefore
              have hfinish' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.rootPath.finish
                  strict.outcome.terminalState.rootPath.finish := by
                simpa only [strict.same_parent] using hfinish
              exact Or.inr ⟨terminal, hparent.trans strict.same_parent,
                GroundingFragmentResidualOrder.beforeEq_trans hbefore'
                  strict.terminal_head_before.1,
                GroundingFragmentResidualOrder.beforeEq_trans
                  hfinish' strict.terminal_finish_beforeEq,
                hsettled⟩
      | boundaryDeparture state tail hin hresidual htail =>
          rcases
              SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictNormalization
                state tail hin hresidual htail with hroot | hstrict
          · refine Or.inl ⟨(.boundaryDeparture state tail hin hresidual htail),
              rfl, ?_, ?_, ?_⟩
            · exact GroundingCut.beforeEq_refl state.deleted_head_mem
            · exact GroundingCut.beforeEq_refl
                (state.rootPath_support state.rootPath.finish_mem_support)
            · exact .boundaryFrontier state tail hin hresidual htail hroot
          · obtain ⟨strict⟩ := hstrict
            have hlt : rel strict.outcome.terminalState state := by
              change settlementPosition strict.outcome.terminalState <
                settlementPosition state
              dsimp only [settlementPosition]
              rw [strict.same_parent]
              exact freshRelevantPathPosition_lt_of_before state.parent
                strict.terminal_head_before
            rcases ih strict.outcome.terminalState hlt strict.outcome rfl with
              hprogress | ⟨terminal, hparent, hbefore, hfinish, hsettled⟩
            · obtain ⟨terminal, hparent, hbefore, hfinish,
                  hterminalProgress⟩ :=
                hprogress
              have hbefore' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.deleted.head
                  strict.outcome.terminalState.deleted.head := by
                simpa only [strict.same_parent] using hbefore
              have hfinish' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.rootPath.finish
                  strict.outcome.terminalState.rootPath.finish := by
                simpa only [strict.same_parent] using hfinish
              exact Or.inl ⟨terminal, hparent.trans strict.same_parent,
                GroundingFragmentResidualOrder.beforeEq_trans hbefore'
                  strict.terminal_head_before.1,
                GroundingFragmentResidualOrder.beforeEq_trans
                  hfinish' strict.terminal_finish_beforeEq,
                hterminalProgress⟩
            · have hbefore' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.deleted.head
                  strict.outcome.terminalState.deleted.head := by
                simpa only [strict.same_parent] using hbefore
              have hfinish' : GroundingCut.BeforeEq state.parent
                  terminal.terminalState.rootPath.finish
                  strict.outcome.terminalState.rootPath.finish := by
                simpa only [strict.same_parent] using hfinish
              exact Or.inr ⟨terminal, hparent.trans strict.same_parent,
                GroundingFragmentResidualOrder.beforeEq_trans hbefore'
                  strict.terminal_head_before.1,
                GroundingFragmentResidualOrder.beforeEq_trans
                  hfinish' strict.terminal_finish_beforeEq,
                hsettled⟩

/-- Every indexed normalization result either makes exact route progress or
settles to a represented-cut control.  Both alternatives retain the terminal
state's ancestry back to the original state. -/
theorem SplitGroundedFreshRelevantBackwardNormalizationResult.settleTerminal
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult initial) :
    L.SplitGroundedFreshRelevantBackwardProgressResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        initial ∨
      L.SplitGroundedFreshRelevantBackwardSettledResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        initial := by
  rcases result with ⟨outcome, hparent, hbefore, hfinish⟩
  rcases settleSelfTerminal outcome.terminalState outcome rfl with
    hprogress |
      ⟨terminal, hterminalParent, hterminalBefore, hterminalFinish, hsettled⟩
  · obtain ⟨terminal, hterminalParent, hterminalBefore, hterminalFinish,
        hterminalProgress⟩ := hprogress
    have hterminalBefore' : GroundingCut.BeforeEq initial.parent
        terminal.terminalState.deleted.head outcome.terminalState.deleted.head := by
      simpa only [hparent] using hterminalBefore
    exact Or.inl ⟨terminal, hterminalParent.trans hparent,
      GroundingFragmentResidualOrder.beforeEq_trans hterminalBefore' hbefore,
      GroundingFragmentResidualOrder.beforeEq_trans
        (by simpa only [hparent] using hterminalFinish) hfinish,
      hterminalProgress⟩
  · have hterminalBefore' : GroundingCut.BeforeEq initial.parent
        terminal.terminalState.deleted.head outcome.terminalState.deleted.head := by
      simpa only [hparent] using hterminalBefore
    exact Or.inr ⟨terminal, hterminalParent.trans hparent,
      GroundingFragmentResidualOrder.beforeEq_trans hterminalBefore' hbefore,
      GroundingFragmentResidualOrder.beforeEq_trans
        (by simpa only [hparent] using hterminalFinish) hfinish,
      hsettled⟩

/-- No terminal remains genuinely settled after controls and rooted backward
owners are converted to their exact native-frontier progress data. -/
theorem SplitGroundedFreshRelevantBackwardSettledResult.false
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (result : L.SplitGroundedFreshRelevantBackwardSettledResult
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) initial) : False := by
  rcases result with ⟨outcome, _hparent, _hbefore, _hfinish, hsettled⟩
  cases outcome <;>
    simp only [SplitGroundedFreshRelevantBackwardNormalizedOutcome.IsSettled]
      at hsettled

/-- Final local settlement theorem: every normalization result produces
exact, original-state-indexed route or control-normalization progress.  No
abstract provider or terminal residual remains.  These progress branches
are inputs to the family-level exchange; they are not asserted to cover the
original failed frontier point individually. -/
theorem SplitGroundedFreshRelevantBackwardNormalizationResult.terminalProgress
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (result : L.SplitGroundedFreshRelevantBackwardNormalizationResult initial) :
    L.SplitGroundedFreshRelevantBackwardProgressResult
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) initial := by
  rcases result.settleTerminal with hprogress | hsettled
  · exact hprogress
  · exact False.elim (hsettled.false initial)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizationResult.terminalProgress
