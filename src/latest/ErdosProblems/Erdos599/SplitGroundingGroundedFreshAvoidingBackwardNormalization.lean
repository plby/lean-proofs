/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingBackwardDescent

/-!
# Normalization of fresh-avoiding backward-owner root failures

An unrooted selected backward anchor has another classified deleted head on
its canonical original-source prefix.  Repeating this construction terminates:
the owning request rank drops, or the new head lies strictly to the left on
the same parent.  The terminal outcomes below retain precisely the positive
cut, rooted-backward, and forward-exchange data needed by the global switch.
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

private abbrev FreshNormalizeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshNormalizeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshNormalizeControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshNormalizeRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshNormalizeEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

/-- Terminal result after recursively expanding every unrooted selected
backward anchor.  A retained forward head is kept separate from a same-tail
exchange because the two cases have different global insertion behavior. -/
inductive SplitGroundedFreshAvoidingBackwardNormalizedOutcome : Prop
  | cut
      (state : L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (u : V) (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
      (cut_edge : (u, state.deleted.head) ∈ GroundingCut.CE
        (FreshNormalizeInput (L := L) (hL := hL)) S.cut)
  | rootedBackwardOwner
      (state : L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (u : V)
      (owner : ActiveControlRequestAt
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (link : Link Gamma.graph) (parent : Gamma.DPath)
      (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
      (selected_edge : (u, state.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshNormalizeControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S)) ∅
          .backward)
      (link_mem : link ∈ (selectedErasedCompression
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.links)
      (direction : link.direction = .backward)
      (link_edge : (u, state.deleted.head) ∈ link.path.edgeSet)
      (parent_mem : parent ∈
        (FreshNormalizeInput (L := L) (hL := hL)).ladder.paths)
      (subpath : link.path.IsSubpathOf parent)
      (parent_eq : parent = state.parent)
      (owner_rank : owner.1 = state.control.1 ∨
        controlRank
          (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
          owner.1 < controlRank
            (FreshNormalizeIndexed (L := L) (hL := hL)
              (hground := hground)) S state.control.1)
      (rooted : ∃ a ∈ Gamma.source \ {
          (FreshNormalizeRecord (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)).record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshNormalizeEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a link.path.start)
  | forwardTailExchange
      (state : L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (u : V)
      (owner : ActiveControlRequestAt
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (f : V × V)
      (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
      (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression
          (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path)
      (same_tail : u = f.1)
      (owner_rank : owner.1 = state.control.1 ∨
        controlRank
          (FreshNormalizeIndexed (L := L) (hL := hL)
            (hground := hground)) S owner.1 <
          controlRank
            (FreshNormalizeIndexed (L := L) (hL := hL)
              (hground := hground)) S state.control.1)
  | retainedForwardHead
      (state : L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (u : V)
      (owner : ActiveControlRequestAt
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (f : V × V)
      (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
      (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
        (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression
          (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path)
      (head_eq : state.deleted.head = f.2)

private def splitGroundedFreshAvoiding_normalizeBackwardStep
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (previous : ∀ next : L.SplitGroundedFreshAvoidingRootState
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S),
      next.Precedes state →
        L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) :
    L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := by
  cases howner : state.owner with
  | cut u hparent hcut =>
      exact .cut state u hparent hcut
  | backward u d l parent hparent hselected hl hldir hlink
      hparentMem hsub hparentEq hrank =>
      by_cases hroot : ∃ a ∈ Gamma.source \ {
          (FreshNormalizeRecord (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)).record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshNormalizeEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a l.path.start
      · exact .rootedBackwardOwner state u d l parent hparent hselected
          hl hldir hlink hparentMem hsub hparentEq hrank hroot
      · have hparentLimit : parent ∈ L.limitWarp := by
          simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
            using hparentMem
        let data := Classical.choice
          (L.exists_splitGroundedFreshAvoidingBackwardDeletedData
            (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
            (S := S) (chosenRequest d.1) l hl hldir parent
            hparentLimit hsub hroot)
        let next : L.SplitGroundedFreshAvoidingRootState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) := {
          control := d
          parent := parent
          parent_exposed :=
            L.splitGroundedFreshAvoiding_backwardParent_exposed
              d l hl hldir parent hparentLimit hsub
          rootPath := data.rootPath
          rootPath_support := data.rootPath_support
          rootPath_edges := data.rootPath_edges
          deleted := data.deleted
          deleted_head_not_rooted := data.deleted_head_not_rooted
          owner := data.ownerOutcome d l hl hldir parent hsub }
        have hnext : next.Precedes state := by
          rcases hrank with heq | hlt
          · have hdc : d = state.control := Subtype.ext heq
            have hparentState : parent = state.parent := hparentEq
            subst d
            subst parent
            exact Prod.Lex.right _
              (splitGroundedFreshAvoidingPathPosition_lt_of_before
                state.parent
                (data.deletedHead_before_oldHead hsub hlink))
          · exact Prod.Lex.left _ _ hlt
        exact previous next hnext
  | forwardTail u d f hparent hconflict hf htail hrank =>
      exact .forwardTailExchange state u d f hparent hconflict hf htail hrank
  | retainedHead u d f hparent hconflict hf hhead =>
      exact .retainedForwardHead state u d f hparent hconflict hf hhead

/-- Total well-founded elimination of repeated unrooted backward owners. -/
noncomputable def SplitGroundedFreshAvoidingRootState.normalizeBackward
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) :=
  WellFounded.fix SplitGroundedFreshAvoidingRootState.precedes_wellFounded
    (fun state previous ↦
      splitGroundedFreshAvoiding_normalizeBackwardStep state previous) state

/-- Initial selected-route anchor data embeds into the common recursion. -/
def SplitGroundedFreshAvoidingInitialDeletedData.toRootState
    (c : ActiveControlRequestAt
      (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (data : L.SplitGroundedFreshAvoidingInitialDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1)) :
    L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) where
  control := c
  parent := data.parent
  parent_exposed := data.parent_exposed c
  rootPath := data.rootPath
  rootPath_support := data.rootPath_support
  rootPath_edges := data.rootPath_edges
  deleted := data.deleted
  deleted_head_not_rooted := data.deleted_head_not_rooted
  owner := data.ownerOutcome c

/-- Backward-link anchor data embeds into the same recursion. -/
def SplitGroundedFreshAvoidingBackwardDeletedData.toRootState
    (c : ActiveControlRequestAt
      (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (FreshNormalizeIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshNormalizeControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hsub : l.path.IsSubpathOf parent)
    (data : L.SplitGroundedFreshAvoidingBackwardDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1) l parent) :
    L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) where
  control := c
  parent := parent
  parent_exposed :=
    L.splitGroundedFreshAvoiding_backwardParent_exposed
      c l hl hldir parent data.parent_mem hsub
  rootPath := data.rootPath
  rootPath_support := data.rootPath_support
  rootPath_edges := data.rootPath_edges
  deleted := data.deleted
  deleted_head_not_rooted := data.deleted_head_not_rooted
  owner := data.ownerOutcome c l hl hldir parent hsub

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingRootState.normalizeBackward
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingInitialDeletedData.toRootState
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingBackwardDeletedData.toRootState
