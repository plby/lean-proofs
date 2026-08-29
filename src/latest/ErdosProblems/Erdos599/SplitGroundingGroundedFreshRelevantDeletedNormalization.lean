/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantBackwardNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantCutAvoidingFailure

/-!
# Native-frontier normalization of a source-first deleted edge

The source-first dispatcher retains one concrete deleted incoming edge on a
finite ladder segment.  If that edge is selected backward, the exposed owner
can be fed directly to the well-founded `(control rank, path position)`
normalizer.  This file records that composition while keeping the original
parent, segment, and deleted head definitionally recoverable.  The two other
honest outcomes remain the selected last-contact splice and a literal
departure from the stopping frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation
open PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshDeletedIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshDeletedInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshDeletedControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshDeletedRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshDeletedFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev FreshDeletedEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (FreshDeletedIndexed (L := L) (hL := hL) (hground := hground)) S
    (FreshDeletedControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (FreshDeletedFrontier (L := L) (hL := hL) (S := S))

private abbrev FreshDeletedSources : Set V :=
  Gamma.source \ {
    (FreshDeletedRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- A selected-backward source-first leaf together with its indexed
well-founded normalization.  The equalities make the original geometry
available without dependent rewriting through the recursive state. -/
structure SplitGroundedFreshRelevantBackwardNormalizationAt
    (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (FreshDeletedEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))) where
  state : L.SplitGroundedFreshRelevantBackwardState
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
  parent_eq : state.parent = parent
  rootPath_eq : state.rootPath = p
  deleted_eq : HEq state.deleted D
  result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state

/-- A forward-conflict leaf with the complete native-frontier state from
which it arose.  Retaining the state is essential: the splice alone forgets
the rooted finite segment and its unrooted endpoint, so it cannot be used by
the ancestry-preserving terminal normalizer. -/
structure SplitGroundedFreshRelevantForwardNormalizationAt
    (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (FreshDeletedEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))) where
  state : L.SplitGroundedFreshRelevantBackwardState
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
  parent_eq : state.parent = parent
  rootPath_eq : state.rootPath = p
  deleted_eq : HEq state.deleted D
  splice : SplitGroundedReducedForwardConflictSpliceData
    (L := L) (hL := hL) (hground := hground) (S := S)
    (K := FreshDeletedControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (FreshDeletedFrontier (L := L) (hL := hL) (S := S))
    state.parent state.rootPath state.deleted
  result : L.SplitGroundedFreshRelevantBackwardNormalizationResult state

/-- Exact result of normalizing one source-first deleted edge at the actual
relevant frontier. -/
inductive SplitGroundedFreshRelevantDeletedNormalizationAt
    (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (FreshDeletedEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))) : Prop
  | backward
      (data : L.SplitGroundedFreshRelevantBackwardNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) parent p D)
  | forwardSplice
      (data : L.SplitGroundedFreshRelevantForwardNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) parent p D)
  | boundaryDeparture
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (residual : (tail, D.head) ∈ residualLadderEdges
        (FreshDeletedIndexed (L := L) (hL := hL) (hground := hground)) S)
      (sourcePath : FinitePath Gamma.graph)
      (source_start : sourcePath.start ∈ Gamma.source)
      (source_finish : sourcePath.finish = tail)
      (source_roof : sourcePath.support ⊆
        (L.splitGroundedPopularAuxiliaryInput hL.legal).roofRegion)
      (tail_relevant : tail ∈ L.splitGroundedRelevantBB hL.legal S.cut)
      (source_first : ∀ x ∈ sourcePath.walk.support.dropLast,
        x ∉ L.splitGroundedRelevantBB hL.legal S.cut)

/-- Feed the selected-backward constructor of the source-first deleted
classifier into the canonical native-frontier recursion. -/
theorem splitGroundedFreshRelevant_normalizeDeletedOutcome
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ FreshDeletedSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshDeletedEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a p.start)
    (hfinish : ¬ ∃ a ∈ FreshDeletedSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshDeletedEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a p.finish)
    (hsupport : p.support ⊆ parent.support)
    (hedges : p.edgeSet ⊆ parent.edgeSet)
    (D : LastDeletedHead p
      (FreshDeletedEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)))
    (hDnot : ¬ ∃ a ∈ FreshDeletedSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshDeletedEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a D.head)
    (outcome :
      SplitGroundedUnusedRecord.SplitGroundedRelevantSourceFirstDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := FreshDeletedControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        parent p D) :
    L.SplitGroundedFreshRelevantDeletedNormalizationAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) parent p D := by
  cases outcome with
  | backward tail hin hselected owner link hlink hdir heLink hsub hexposed =>
      let state := L.mkSplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
        owner parent hparent hexposed p hstart hfinish hsupport hedges D hDnot
        tail hin hselected link hlink hdir heLink hsub
      exact .backward {
        state := state
        parent_eq := rfl
        rootPath_eq := rfl
        deleted_eq := HEq.rfl
        result := state.normalize }
  | forwardSplice splice =>
      let U := FreshDeletedIndexed (L := L) (hL := hL)
        (hground := hground)
      let K := FreshDeletedControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)
      let J := FreshDeletedInput (L := L) (hL := hL)
      let r := chosenRequest splice.contact.owner.1
      let trace := selectedRequestTrace U S K r
      let E := trace.erasedRoute
      have hpStart : (strongSelectedPath U S K r).start ∈ J.lambda.source :=
        (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
      have hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
          SignedEdge.Valid (Gamma := Gamma) s := by
        intro s hs
        exact trace.valid s (E.steps_sublist.subset hs)
      have hxRoute : splice.contact.lastContact.vertex ∈
          (selectedErasedCompression U S K r).path.vertexSet := by
        have hx := E.vertexChain_subset_compressionOfValid_vertexSet hvalid
          splice.contact.lastContact.vertex_mem_chain
        simpa only [E, trace, selectedErasedCompression,
          EndpointTrace.erasedCompression] using hx
      have hxCarrier : splice.contact.lastContact.vertex ∈
          J.decodedVertexCarrier (strongSelectedPath U S K r) :=
        GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
          U S K r hxRoute
      have hparentInput : parent ∈ J.ladder.paths := by
        simpa only [J, FreshDeletedInput, splitGroundedPopularAuxiliaryInput,
          limitWarp] using hparent
      have hexposed : parent ∈ exposedLadderPaths J
          (strongSelectedPath U S K r) :=
        J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
          (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
          _ hpStart hparentInput hxCarrier splice.contact.lastContact.vertex_mem
      let state : L.SplitGroundedFreshRelevantBackwardState
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S) := {
        control := splice.contact.owner
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
        resolution := .geometric (.forwardLastContact splice) }
      exact .forwardSplice {
        state := state
        parent_eq := rfl
        rootPath_eq := rfl
        deleted_eq := HEq.rfl
        splice := splice
        result := state.normalize }
  | boundaryDeparture tail hin hresidual sourcePath hsource hsourceFinish
      hroof hrelevant hfirst =>
      exact .boundaryDeparture tail hin hresidual sourcePath hsource
        hsourceFinish hroof hrelevant hfirst

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_normalizeDeletedOutcome
