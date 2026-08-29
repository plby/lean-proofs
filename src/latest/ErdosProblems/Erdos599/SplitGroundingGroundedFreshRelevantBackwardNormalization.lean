/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingRelevantFailure
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantForwardConflict

/-!
# Native-frontier normalization of relevant backward owners

The source-first grounding dispatcher is stopped at its actual relevant
frontier, not at the empty set.  A deleted incoming edge owned by a selected
backward link therefore has to be normalized in that same relation.

For the canonical fresh-avoiding controls, every such link has a finite
allowed-source prefix on its limiting-ladder parent.  If the link start is
not rooted, the prefix has a new unrooted last-deleted head.  The new state
has smaller control rank, or (for a self owner) lies strictly earlier on the
same directed parent.  This file performs that well-founded recursion and
retains the three honest native-frontier terminal cases: an unrooted control,
a forward splice, or a literal departure from the stopping frontier.
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

private abbrev FreshRelevantBackwardInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshRelevantBackwardIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshRelevantBackwardControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshRelevantBackwardRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshRelevantBackwardFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev FreshRelevantBackwardEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (FreshRelevantBackwardIndexed (L := L) (hL := hL)
      (hground := hground)) S
    (FreshRelevantBackwardControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))

private abbrev FreshRelevantBackwardSources : Set V :=
  Gamma.source \ {
    (FreshRelevantBackwardRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

noncomputable def freshRelevantPathPosition
    (P : Gamma.DPath) (x : V) : ℕ := by
  classical
  exact if hx : x ∈ P.support then
    Nat.find ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)
  else 0

theorem occursAt_freshRelevantPathPosition
    (P : Gamma.DPath) {x : V} (hx : x ∈ P.support) :
    GroundingCut.OccursAt P (freshRelevantPathPosition P x) x := by
  classical
  rw [freshRelevantPathPosition, dif_pos hx]
  exact Nat.find_spec
    ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)

theorem freshRelevantPathPosition_lt_of_before
    (P : Gamma.DPath) {x y : V} (hxy : GroundingCut.Before P x y) :
    freshRelevantPathPosition P x < freshRelevantPathPosition P y := by
  rcases hxy.1 with ⟨m, n, hmx, hny, hmn⟩
  have hx : x ∈ P.support := GroundingCut.occursAt_mem_support hmx
  have hy : y ∈ P.support := GroundingCut.occursAt_mem_support hny
  have hxm : freshRelevantPathPosition P x = m :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_freshRelevantPathPosition P hx) hmx
  have hyn : freshRelevantPathPosition P y = n :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_freshRelevantPathPosition P hy) hny
  rw [hxm, hyn]
  apply lt_of_le_of_ne hmn
  intro hnm
  apply hxy.2
  have hsame : GroundingCut.OccursAt P m y := by
    simpa only [hnm] using hny
  cases P with
  | inl p => exact hmx.2.symm.trans hsame.2
  | inr r => exact hmx.symm.trans hsame

theorem freshRelevantWalk_beforeEq_of_edgeSet_subset
    (P : Gamma.DPath) {a b : V} (q : Walk Gamma.graph a b)
    (ha : a ∈ P.support) (hq : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.BeforeEq P a b := by
  induction q with
  | nil => exact GroundingCut.beforeEq_refl ha
  | @cons a c b hac q ih =>
      have hacP : (a, c) ∈ P.edgeSet := by
        apply hq
        simp
      have hcP : c ∈ P.support :=
        (P.edgeSet_subset_support_prod hacP).2
      have hqP : q.edgeSet ⊆ P.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inr he
      exact GroundingFragmentResidualOrder.beforeEq_trans
        (GroundingCut.beforeEq_of_mem_edgeSet hacP) (ih hcP hqP)

theorem freshRelevantFiniteSubpath_start_beforeEq_of_mem
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P q.start x := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.firstHit ({x} : Set V) m
  have hrStart : r.start = q.start := rfl
  have hrFinish : r.finish = x := by
    exact Set.mem_singleton_iff.mp
      (q.firstHit_finish_mem ({x} : Set V) m)
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.firstHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hstart : q.start ∈ P.support := hsub.1 q.start_mem_support
  simpa only [hrStart, hrFinish] using
    freshRelevantWalk_beforeEq_of_edgeSet_subset
      P r.walk hstart hrEdges

/-- A vertex of a finite subpath precedes its endpoint on the ambient
directed path. -/
theorem freshRelevantFiniteSubpath_mem_beforeEq_finish
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P x q.finish := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.lastHit ({x} : Set V) m
  have hrStart : r.start = x := by
    exact Set.mem_singleton_iff.mp
      (q.lastHit_start_mem ({x} : Set V) m)
  have hrFinish : r.finish = q.finish := rfl
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.lastHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hrStartP : r.start ∈ P.support := by
    simpa only [hrStart] using hsub.1 hx
  simpa only [hrStart, hrFinish] using
    freshRelevantWalk_beforeEq_of_edgeSet_subset
      P r.walk hrStartP hrEdges

theorem freshRelevantBackwardLink_start_before_head
    (P : Gamma.DPath) (link : Alternating.Link Gamma.graph)
    (hsub : link.path.IsSubpathOf P) {u z : V}
    (huz : (u, z) ∈ link.path.edgeSet) :
    GroundingCut.Before P link.path.start z := by
  refine ⟨freshRelevantFiniteSubpath_start_beforeEq_of_mem
    P link.path hsub ((link.path.edgeSet_subset_support_prod huz).2), ?_⟩
  exact Ne.symm (FinitePath.target_ne_start_of_mem_edgeSet link.path huz)

private theorem freshRelevantAltDirectionEdge_endpoints_mem_vertexSet
    {D : Digraph V} (Q : Alternating.AltPath D)
    {d : Alternating.Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨link, hlink, _hdirection, hedge⟩ := he
  have hends := link.path.edgeSet_subset_support_prod hedge
  cases Q with
  | trivial v => simp [Alternating.AltPath.links] at hlink
  | finite T =>
      obtain ⟨j, rfl⟩ := hlink
      exact ⟨Set.mem_iUnion.2 ⟨j, hends.1⟩,
        Set.mem_iUnion.2 ⟨j, hends.2⟩⟩
  | infinite T =>
      obtain ⟨j, rfl⟩ := hlink
      exact ⟨Set.mem_iUnion.2 ⟨j, hends.1⟩,
        Set.mem_iUnion.2 ⟨j, hends.2⟩⟩

/-- A retained forward edge departing from a limiting-ladder component
exposes that component to its active owner, at the actual relevant stopping
frontier. -/
theorem splitGroundedFreshRelevant_forwardOwner_parent_exposed
    (owner : ActiveControlRequestAt
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S)))
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (f : V × V)
    (hf : f ∈ retainedForwardEdgesAt
      (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
      (selectedErasedCompression
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (hftail : f.1 ∈ parent.support) :
    parent ∈ exposedLadderPaths
      (FreshRelevantBackwardInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)) := by
  let U := FreshRelevantBackwardIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := FreshRelevantBackwardControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let J := FreshRelevantBackwardInput (L := L) (hL := hL)
  let p := strongSelectedPath U S K (chosenRequest owner.1)
  have hpStart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source
      ⟨chosenRequest owner.1, rfl⟩
  have htailVertex : f.1 ∈
      (selectedErasedCompression U S K
        (chosenRequest owner.1)).path.vertexSet :=
    (freshRelevantAltDirectionEdge_endpoints_mem_vertexSet _
      (retainedForwardEdgesAt_subset_directionEdges
        (FreshRelevantBackwardFrontier
          (L := L) (hL := hL) (S := S)) _ hf)).1
  have htailCarrier : f.1 ∈ J.decodedVertexCarrier p :=
    GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K (chosenRequest owner.1) htailVertex
  exact J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
    p hpStart hparent htailCarrier hftail

/-- One concrete unrooted deleted-head problem on an exposed limiting-ladder
parent, in the relation stopped at the actual relevant frontier. -/
structure SplitGroundedFreshRelevantBackwardState where
  control : ActiveControlRequestAt
    (FreshRelevantBackwardIndexed (L := L) (hL := hL)
      (hground := hground)) S
    (FreshRelevantBackwardControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
  parent : Gamma.DPath
  parent_mem : parent ∈ L.limitWarp
  parent_exposed : parent ∈ exposedLadderPaths
    (FreshRelevantBackwardInput (L := L) (hL := hL))
    (strongSelectedPath
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest control.1))
  rootPath : FinitePath Gamma.graph
  rootPath_start_rooted : ∃ a ∈ FreshRelevantBackwardSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a rootPath.start
  rootPath_finish_not_rooted : ¬ ∃ a ∈ FreshRelevantBackwardSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a rootPath.finish
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (FreshRelevantBackwardEdges (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ FreshRelevantBackwardSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a deleted.head
  resolution : SplitGroundedRelevantDeletedResolutionAt
    (L := L) (hL := hL) (hground := hground) (S := S)
    (K := FreshRelevantBackwardControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
    parent rootPath deleted

/-- Constructor from the exact selected-backward leaf produced by the
relevant source-first dispatcher.  The native frontier and canonical
fresh controls are fixed in the result, so no At-empty transport appears
in this entry point. -/
def mkSplitGroundedFreshRelevantBackwardState
    (control : ActiveControlRequestAt
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S)))
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hexposed : parent ∈ exposedLadderPaths
      (FreshRelevantBackwardInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest control.1)))
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ FreshRelevantBackwardSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a p.start)
    (hfinish : ¬ ∃ a ∈ FreshRelevantBackwardSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a p.finish)
    (hsupport : p.support ⊆ parent.support)
    (hedges : p.edgeSet ⊆ parent.edgeSet)
    (D : LastDeletedHead p
      (FreshRelevantBackwardEdges (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)))
    (hDnot : ¬ ∃ a ∈ FreshRelevantBackwardSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a D.head)
    (tail : V) (hin : (tail, D.head) ∈ p.edgeSet)
    (hselected : (tail, D.head) ∈ erasedSelectedDirectionEdgesAt
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
      .backward)
    (link : Alternating.Link Gamma.graph)
    (hlink : link ∈ (selectedErasedCompression
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest control.1)).path.links)
    (hdir : link.direction = .backward)
    (heLink : (tail, D.head) ∈ link.path.edgeSet)
    (hsub : link.path.IsSubpathOf parent) :
    L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) where
  control := control
  parent := parent
  parent_mem := hparent
  parent_exposed := hexposed
  rootPath := p
  rootPath_start_rooted := hstart
  rootPath_finish_not_rooted := hfinish
  rootPath_support := hsupport
  rootPath_edges := hedges
  deleted := D
  deleted_head_not_rooted := hDnot
  resolution := .geometric (.backward tail hin hselected control link
    hlink hdir heLink hsub hexposed)

/-- The current deleted head is a point of its exposed parent. -/
theorem SplitGroundedFreshRelevantBackwardState.deleted_head_mem
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    state.deleted.head ∈ state.parent.support := by
  obtain ⟨u, hu, _⟩ := state.deleted.deleted_incoming
  exact state.rootPath_support
    (state.rootPath.edgeSet_subset_support_prod hu).2

/-- The deleted head precedes the endpoint of its concrete root segment on
the exposed parent.  This elementary order fact is the continuation base
for carrying a terminal component exchange back to the original failed
endpoint. -/
theorem SplitGroundedFreshRelevantBackwardState.deleted_head_beforeEq_finish
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    GroundingCut.BeforeEq state.parent state.deleted.head
      state.rootPath.finish := by
  exact freshRelevantFiniteSubpath_mem_beforeEq_finish
    state.parent state.rootPath
      ⟨state.rootPath_support, state.rootPath_edges⟩
      state.deleted.head_mem_parent

/-- Lexicographic rank/parent-position key for native-frontier backward
normalization. -/
def SplitGroundedFreshRelevantBackwardState.recursionKey
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    Stationary.Below kappa × ℕ :=
  (controlRank
      (FreshRelevantBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S state.control.1,
    freshRelevantPathPosition state.parent state.deleted.head)

def SplitGroundedFreshRelevantBackwardState.Precedes :
    L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) →
      L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) → Prop :=
  (Prod.Lex (fun a b : Stationary.Below kappa ↦ a < b)
    (fun m n : ℕ ↦ m < n)).onFun
      SplitGroundedFreshRelevantBackwardState.recursionKey

theorem SplitGroundedFreshRelevantBackwardState.precedes_wellFounded :
    WellFounded (@SplitGroundedFreshRelevantBackwardState.Precedes
      V Gamma kappa L hL hground hnotFresh S) := by
  exact InvImage.wf SplitGroundedFreshRelevantBackwardState.recursionKey
    (wellFounded_lt.prod_lex wellFounded_lt)

/-- Terminal native-frontier outcomes after all unrooted selected backward
owners have been recursively expanded. -/
inductive SplitGroundedFreshRelevantBackwardNormalizedOutcome : Type u
  | control
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (cut_edge : (tail, state.deleted.head) ∈ GroundingCut.CE
        (FreshRelevantBackwardInput (L := L) (hL := hL)) S.cut)
      (control : ControlRequest
        (FreshRelevantBackwardInput (L := L) (hL := hL)) S.cut)
      (control_eq : control.1 = state.deleted.head)
      (resolution : SplitGroundedRelevantControlResolutionAt
        (FreshRelevantBackwardRecord (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
        control)
  | rootedBackward
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (owner : ActiveControlRequestAt
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S)))
      (link : Alternating.Link Gamma.graph)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (selected_backward : (tail, state.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (FreshRelevantBackwardIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (FreshRelevantBackwardControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
          .backward)
      (link_mem : link ∈ (selectedErasedCompression
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.links)
      (link_direction : link.direction = .backward)
      (edge_mem_link : (tail, state.deleted.head) ∈ link.path.edgeSet)
      (link_subpath : link.path.IsSubpathOf state.parent)
      (rooted : ∃ a ∈ FreshRelevantBackwardSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a link.path.start)
  | forwardSplice
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
        state.parent state.rootPath state.deleted)
      (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
      (owner_eq : splice.contact.owner.1 = state.control.1)
  | forwardAnchor
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
        state.parent state.rootPath state.deleted)
      (anchor : ActiveRetainedForwardVertexUnrootedOutcome
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (FreshRelevantBackwardControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
        (FreshRelevantBackwardSources (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        splice.contact.owner)
  | boundaryDeparture
      (state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (tail : V)
      (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
      (residual : (tail, state.deleted.head) ∈ residualLadderEdges
        (FreshRelevantBackwardIndexed (L := L) (hL := hL)
          (hground := hground)) S)
      (tail_mem : tail ∈ FreshRelevantBackwardFrontier
        (L := L) (hL := hL) (S := S))

/-- A rooted segment-local contact in a terminal forward-splice state lies
strictly before that state's last deleted head.  The positive finish-root
alternative is ruled out by the finish-unrooted certificate carried by the
state itself. -/
theorem splitGroundedFreshRelevant_forwardSplice_contact_before_head
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := FreshRelevantBackwardControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (hroot : ∃ a ∈ FreshRelevantBackwardSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.segmentLastContact.vertex) :
    GroundingCut.Before (.inl state.rootPath : Gamma.DPath)
      splice.segmentLastContact.vertex state.deleted.head :=
  splice.before_head_of_unrooted_finish
    state.deleted_head_not_rooted state.rootPath_finish_not_rooted hroot

/-- The terminal state carried by a normalized outcome. -/
def SplitGroundedFreshRelevantBackwardNormalizedOutcome.terminalState :
    L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) →
      L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)
  | .control state _ _ _ _ _ _ => state
  | .rootedBackward state _ _ _ _ _ _ _ _ _ _ => state
  | .forwardSplice state _ _ _ => state
  | .forwardAnchor state _ _ => state
  | .boundaryDeparture state _ _ _ _ => state

/-- A normalization result indexed by its original problem.  Besides the
terminal local outcome, it preserves the original parent, proves that the
terminal deleted head is no later than the original deleted head, and keeps
the terminal finite-segment endpoint no later than the original endpoint.
The final field is the continuation certificate needed to extend a local
component exchange back to the original failed frontier point. -/
inductive SplitGroundedFreshRelevantBackwardNormalizationResult
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) : Prop
  | mk
      (outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (same_parent : outcome.terminalState.parent = initial.parent)
      (terminal_head_beforeEq : GroundingCut.BeforeEq initial.parent
        outcome.terminalState.deleted.head initial.deleted.head)
      (terminal_finish_beforeEq : GroundingCut.BeforeEq initial.parent
        outcome.terminalState.rootPath.finish initial.rootPath.finish)

private theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.selfResult
    (outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hstate : outcome.terminalState = state) :
    L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  refine SplitGroundedFreshRelevantBackwardNormalizationResult.mk outcome ?_ ?_ ?_
  · rw [hstate]
  · rw [hstate]
    exact GroundingCut.beforeEq_refl state.deleted_head_mem
  · rw [hstate]
    exact GroundingCut.beforeEq_refl
      (state.rootPath_support state.rootPath.finish_mem_support)

theorem splitGroundedFreshRelevant_deletedHead_before_oldHead
    (parent : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hqSupport : q.support ⊆ parent.support)
    (hqEdges : q.edgeSet ⊆ parent.edgeSet)
    (D : LastDeletedHead q
      (FreshRelevantBackwardEdges (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)))
    (link : Alternating.Link Gamma.graph)
    (hfinish : q.finish = link.path.start)
    (hsub : link.path.IsSubpathOf parent)
    {u z : V} (huz : (u, z) ∈ link.path.edgeSet) :
    GroundingCut.Before parent D.head z := by
  obtain ⟨v, hv, _⟩ := D.deleted_incoming
  have hheadPrefix : D.head ∈ q.support :=
    (q.edgeSet_subset_support_prod hv).2
  have hheadStart : GroundingCut.BeforeEq parent D.head link.path.start := by
    let m : q.walk.Meets ({D.head} : Set V) :=
      ⟨D.head, hheadPrefix, Set.mem_singleton D.head⟩
    let r := q.lastHit ({D.head} : Set V) m
    have hrStart : r.start = D.head := by
      exact Set.mem_singleton_iff.mp
        (q.lastHit_start_mem ({D.head} : Set V) m)
    have hrEdges : r.edgeSet ⊆ parent.edgeSet :=
      (q.lastHit_edgeSet_subset ({D.head} : Set V) m).trans hqEdges
    have hrFinish : r.finish = q.finish := rfl
    have hrStartParent : r.start ∈ parent.support := by
      simpa only [hrStart] using hqSupport hheadPrefix
    simpa only [hrStart, hrFinish, hfinish] using
      freshRelevantWalk_beforeEq_of_edgeSet_subset
        parent r.walk hrStartParent hrEdges
  have hstartOld : GroundingCut.Before parent link.path.start z :=
    freshRelevantBackwardLink_start_before_head parent link hsub huz
  refine ⟨GroundingFragmentResidualOrder.beforeEq_trans
    hheadStart hstartOld.1, ?_⟩
  intro heq
  apply hstartOld.2
  apply GroundingCutDecoder.beforeEq_antisymm hstartOld.1
  simpa only [heq] using hheadStart

private def splitGroundedFreshRelevant_normalizeBackwardStep
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (previous : ∀ next : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      next.Precedes state →
        L.SplitGroundedFreshRelevantBackwardNormalizationResult next) :
    L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  cases state.resolution with
  | control tail hin hcut =>
      let request : Request
          (FreshRelevantBackwardInput (L := L) (hL := hL)) S.cut :=
        .inr ⟨(tail, state.deleted.head), (GroundingCut.mem_CE.mp hcut).1⟩
      let control : ControlRequest
          (FreshRelevantBackwardInput (L := L) (hL := hL)) S.cut :=
        ⟨state.deleted.head, ⟨request, rfl⟩⟩
      have hcontrol : control.1 = state.deleted.head := rfl
      have hcontrolNot : ¬ ∃ a ∈ FreshRelevantBackwardSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a control.1 := by
        simpa only [hcontrol] using state.deleted_head_not_rooted
      let resolution := L.splitGroundedRelevantControlResolutionAt
        (FreshRelevantBackwardRecord (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (FreshRelevantBackwardFrontier (L := L) (hL := hL) (S := S))
        control hcontrolNot
      let terminal := SplitGroundedFreshRelevantBackwardNormalizedOutcome.control
        state tail hin hcut control hcontrol resolution
      exact terminal.selfResult state rfl
  | geometric outcome =>
      cases outcome with
      | backward tail hin hselected owner link hlink hdir heLink hsub hexposed =>
          by_cases hroot : ∃ a ∈ FreshRelevantBackwardSources
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S),
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
                (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S)) a link.path.start
          · let terminal :=
              SplitGroundedFreshRelevantBackwardNormalizedOutcome.rootedBackward
                state tail owner link hin hselected hlink hdir heLink hsub hroot
            exact terminal.selfResult state rfl
          · obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
              L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
                hL hground hnotFresh S (chosenRequest owner.1) link hlink hdir
                state.parent state.parent_mem hsub
            have hqRoot : ∃ a ∈ FreshRelevantBackwardSources
                (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S),
              Relation.ReflTransGen
                (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
                  (L := L) (hL := hL) (hground := hground)
                  (hnotFresh := hnotFresh) (S := S)) a q.start :=
              ⟨q.start, hqStart, .refl⟩
            have hqNot : ¬ ∃ a ∈ FreshRelevantBackwardSources
                (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S),
              Relation.ReflTransGen
                (fun x y ↦ (x, y) ∈ FreshRelevantBackwardEdges
                  (L := L) (hL := hL) (hground := hground)
                  (hnotFresh := hnotFresh) (S := S)) a q.finish := by
              intro h
              apply hroot
              simpa only [hqFinish] using h
            let R := FreshRelevantBackwardRecord (L := L) (hL := hL)
              (hground := hground) (hnotFresh := hnotFresh) (S := S)
            obtain ⟨D, hDnot⟩ :=
              R.exists_unrootedLastDeletedHead_sourceFirstTotal
                (FreshRelevantBackwardFrontier
                  (L := L) (hL := hL) (S := S)) q hqRoot hqNot
            have hparentInput : state.parent ∈
                (FreshRelevantBackwardInput (L := L) (hL := hL)).ladder.paths := by
              simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
                using state.parent_mem
            let resolution := L.splitGroundedRelevantDeletedResolutionAt
              (FreshRelevantBackwardFrontier
                (L := L) (hL := hL) (S := S))
              state.parent hparentInput q hqSupport hqEdges D
            let next : L.SplitGroundedFreshRelevantBackwardState
                (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) := {
              control := owner
              parent := state.parent
              parent_mem := state.parent_mem
              parent_exposed := hexposed
              rootPath := q
              rootPath_start_rooted := hqRoot
              rootPath_finish_not_rooted := hqNot
              rootPath_support := hqSupport
              rootPath_edges := hqEdges
              deleted := D
              deleted_head_not_rooted := hDnot
              resolution := resolution }
            have hrank := selectedOwnerCore_activeBackward_eq_or_rank_lt
              (FreshRelevantBackwardIndexed (L := L) (hL := hL)
                (hground := hground)) S
              (FreshRelevantBackwardControls (L := L) (hL := hL)
                (hground := hground) (hnotFresh := hnotFresh) (S := S))
              (FreshRelevantBackwardFrontier
                (L := L) (hL := hL) (S := S))
              state.control owner state.parent state.parent_exposed
              link hlink hdir hsub
            have hnext : next.Precedes state := by
              rcases hrank with heq | hlt
              · have howner : owner = state.control := Subtype.ext heq
                subst owner
                exact Prod.Lex.right _
                  (freshRelevantPathPosition_lt_of_before state.parent
                    (splitGroundedFreshRelevant_deletedHead_before_oldHead
                      state.parent q hqSupport hqEdges D link hqFinish
                        hsub heLink))
              · exact Prod.Lex.left _ _ hlt
            have hnextFinish : GroundingCut.BeforeEq state.parent
                next.rootPath.finish state.rootPath.finish := by
              dsimp only [next]
              rw [hqFinish]
              exact GroundingFragmentResidualOrder.beforeEq_trans
                (freshRelevantBackwardLink_start_before_head
                  state.parent link hsub heLink).1
                state.deleted_head_beforeEq_finish
            rcases previous next hnext with
              ⟨terminal, hsame, hbefore, hfinishBefore⟩
            exact SplitGroundedFreshRelevantBackwardNormalizationResult.mk
              terminal hsame
              (GroundingFragmentResidualOrder.beforeEq_trans hbefore
                (splitGroundedFreshRelevant_deletedHead_before_oldHead
                  state.parent q hqSupport hqEdges D link hqFinish
                    hsub heLink).1)
              (GroundingFragmentResidualOrder.beforeEq_trans
                (by simpa only [show next.parent = state.parent from rfl]
                  using hfinishBefore)
                hnextFinish)
      | forwardLastContact splice =>
          rcases splice.sameTail_or_unrootedAnchor
              state.deleted_head_not_rooted with htail | hanchor
          · have hftail : splice.contact.forwardEdge.1 ∈
                state.parent.support := by
              rw [← htail]
              exact state.rootPath_support
                (state.rootPath.edgeSet_subset_support_prod
                  splice.incoming_mem).1
            have hexposed :=
              L.splitGroundedFreshRelevant_forwardOwner_parent_exposed
                splice.contact.owner state.parent state.parent_mem
                splice.contact.forwardEdge splice.contact.retained hftail
            have hrank := selectedOwnerCore_activeForwardTail_eq_or_rank_lt
              (FreshRelevantBackwardIndexed (L := L) (hL := hL)
                (hground := hground)) S
              (FreshRelevantBackwardControls (L := L) (hL := hL)
                (hground := hground) (hnotFresh := hnotFresh) (S := S))
              (FreshRelevantBackwardFrontier
                (L := L) (hL := hL) (S := S))
              (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
              state.control splice.contact.owner state.parent
              state.parent_exposed splice.contact.retained hftail
            rcases hrank with heq | hlt
            · let terminal :=
                SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice
                  state splice htail heq
              exact terminal.selfResult state rfl
            · let next : L.SplitGroundedFreshRelevantBackwardState
                  (hL := hL) (hground := hground)
                  (hnotFresh := hnotFresh) (S := S) := {
                control := splice.contact.owner
                parent := state.parent
                parent_mem := state.parent_mem
                parent_exposed := hexposed
                rootPath := state.rootPath
                rootPath_start_rooted := state.rootPath_start_rooted
                rootPath_finish_not_rooted := state.rootPath_finish_not_rooted
                rootPath_support := state.rootPath_support
                rootPath_edges := state.rootPath_edges
                deleted := state.deleted
                deleted_head_not_rooted := state.deleted_head_not_rooted
                resolution := .geometric (.forwardLastContact splice) }
              have hnext : next.Precedes state := Prod.Lex.left _ _ hlt
              rcases previous next hnext with
                ⟨terminal, hsame, hbefore, hfinishBefore⟩
              exact SplitGroundedFreshRelevantBackwardNormalizationResult.mk
                terminal hsame hbefore hfinishBefore
          · let terminal :=
              SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardAnchor
                state splice hanchor
            exact terminal.selfResult state rfl
      | boundaryDeparture tail hin hresidual htail =>
          let terminal :=
            SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture
              state tail hin hresidual htail
          exact terminal.selfResult state rfl

/-- Total well-founded elimination of repeated unrooted backward owners in
the canonical fresh relation stopped at the relevant source-first frontier. -/
noncomputable def SplitGroundedFreshRelevantBackwardState.normalize
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) :
    L.SplitGroundedFreshRelevantBackwardNormalizationResult state :=
  WellFounded.fix
    SplitGroundedFreshRelevantBackwardState.precedes_wellFounded
    (fun state previous ↦
      splitGroundedFreshRelevant_normalizeBackwardStep state previous) state

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardState.normalize
