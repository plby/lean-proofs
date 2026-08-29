/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirstTotal
import ErdosProblems.Erdos599.GroundingStoppedControlRootClassification
import ErdosProblems.Erdos599.GroundingStoppedActiveControlPrefix
import ErdosProblems.Erdos599.GroundingStoppedActiveForwardRootClassification
import ErdosProblems.Erdos599.GroundingSelectedOwnerRankCore

/-!
# Native-frontier resolution of an unrooted split grounding control

The source-first totalizer deliberately retains an unrooted old control
instead of assuming that all controls survive stopping.  This file expands
that leaf in the actual relation stopped at `T`.  Active controls retain their
concrete prefix outcome; an unrooted retained contact is reduced to an active
request anchor; and an inactive control retains both its finite exposed-parent
obstruction and the exact four-way deleted-edge resolution.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ControlResolutionInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ControlResolutionIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ControlResolutionEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (ControlResolutionIndexed (L := L) (hL := hL) (hground := hground))
      S K T

private abbrev ControlResolutionSources
    (R : L.SplitGroundedUnusedRecord hL hground S K) : Set V :=
  Gamma.source \ {R.record.initial}

/-- Rank-oriented form of the finite deleted edge exposed by an inactive
control.  A selected backward owner is either the absorbing active control
itself or has strictly smaller control rank. -/
inductive SplitGroundedRelevantInactiveResolutionAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut)
    (data : InactiveStoppedRootObstructionDataAt S K T
      (ControlResolutionSources R) c) : Prop
  | control
      (tail : V)
      (incoming_mem : (tail, data.deleted.head) ∈ data.segment.edgeSet)
      (cut_edge : (tail, data.deleted.head) ∈
        GroundingCut.CE (ControlResolutionInput (L := L) (hL := hL)) S.cut)
  | backward
      (tail : V)
      (incoming_mem : (tail, data.deleted.head) ∈ data.segment.edgeSet)
      (selected_backward : (tail, data.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (ControlResolutionIndexed (L := L) (hL := hL)
            (hground := hground)) S K T .backward)
      (owner : ActiveControlRequestAt
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T)
      (link : Alternating.Link Gamma.graph)
      (link_mem : link ∈ (selectedErasedCompression
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K (chosenRequest owner.1)).path.links)
      (link_direction : link.direction = .backward)
      (edge_mem_link : (tail, data.deleted.head) ∈ link.path.edgeSet)
      (link_subpath : link.path.IsSubpathOf data.parent)
      (owner_parent_exposed : data.parent ∈ exposedLadderPaths
        (ControlResolutionInput (L := L) (hL := hL))
        (strongSelectedPath
          (ControlResolutionIndexed (L := L) (hL := hL)
            (hground := hground)) S K (chosenRequest owner.1)))
      (owner_eq_or_rank_lt : owner.1 = data.absorber.1 ∨
        controlRank
            (ControlResolutionIndexed (L := L) (hL := hL)
              (hground := hground)) S owner.1 <
          controlRank
            (ControlResolutionIndexed (L := L) (hL := hL)
              (hground := hground)) S data.absorber.1)
  | forwardSplice
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T data.parent data.segment data.deleted)
  | boundaryDeparture
      (tail : V)
      (incoming_mem : (tail, data.deleted.head) ∈ data.segment.edgeSet)
      (residual : (tail, data.deleted.head) ∈ residualLadderEdges
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S)
      (tail_mem : tail ∈ T)

/-- Exact native-`T` alternatives for one unrooted represented-cut control.
No activity or reachability fact is transported from the empty frontier. -/
inductive SplitGroundedRelevantControlResolutionAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut) :
    Prop
  | active
      (control : ActiveControlRequestAt
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T)
      (control_eq : control.1 = c)
      (control_not_rooted : ¬ ∃ a ∈ ControlResolutionSources R,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlResolutionEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1)
      (outcome : ActiveControlAtUnrootedPrefixOutcome
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T
        (ControlResolutionSources R) control)
  | retained
      (control : ActiveControlRequestAt
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T)
      (vertex : V)
      (vertex_retained : vertex ∈ retainedForwardVerticesAt T
        (selectedErasedCompression
          (ControlResolutionIndexed (L := L) (hL := hL)
            (hground := hground)) S K
          (chosenRequest control.1)).path)
      (vertex_not_rooted : ¬ ∃ a ∈ ControlResolutionSources R,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlResolutionEdges
          (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a vertex)
      (control_not_rooted : ¬ ∃ a ∈ ControlResolutionSources R,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlResolutionEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1)
      (outcome : ActiveRetainedForwardVertexUnrootedOutcome
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T
        (ControlResolutionSources R) control)
  | inactive
      (data : InactiveStoppedRootObstructionDataAt S K T
        (ControlResolutionSources R) c)
      (control_not_rooted : ¬ ∃ a ∈ ControlResolutionSources R,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ControlResolutionEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1)
      (resolution : SplitGroundedRelevantInactiveResolutionAt R T c data)

/-- The original stopped control remains unrooted in every refined
constructor.  Keeping this fact is essential when a rooted first-frontier
prefix is later converted into a strict dependency rather than discarded. -/
theorem SplitGroundedRelevantControlResolutionAt.control_not_rooted
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {T : Set V}
    {c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut}
    (resolution : SplitGroundedRelevantControlResolutionAt R T c) :
    ¬ ∃ a ∈ ControlResolutionSources R,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ControlResolutionEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a c.1 := by
  cases resolution with
  | active _ _ hnot _ => exact hnot
  | retained _ _ _ _ hnot _ => exact hnot
  | inactive _ hnot _ => exact hnot

private theorem InactiveStoppedRootObstructionDataAt.segment_support_subset_parent
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut)
    (data : InactiveStoppedRootObstructionDataAt S K T
      (ControlResolutionSources R) c) :
    data.segment.support ⊆ data.parent.support := by
  intro x hx
  by_cases hxFinish : x = data.segment.finish
  · rw [hxFinish, data.segment_finish]
    rcases data.contact_before_control with
      ⟨_m, _n, _hcontact, hcontrol, _hmn⟩
    exact GroundingCut.occursAt_mem_support hcontrol
  · obtain ⟨y, hxy⟩ :=
      data.segment.walk.exists_outgoing_edge_of_mem_of_ne_finish hx hxFinish
    exact (data.parent.edgeSet_subset_support_prod
      (data.segment_edges hxy)).1

private theorem resolveInactiveStoppedRootObstructionAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut)
    (data : InactiveStoppedRootObstructionDataAt S K T
      (ControlResolutionSources R) c) :
    SplitGroundedRelevantInactiveResolutionAt R T c data := by
  have hparent : data.parent ∈
      (ControlResolutionInput (L := L) (hL := hL)).ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
        _ data.parent_exposed
  let resolution :=
    L.splitGroundedRelevantDeletedResolutionAt T data.parent hparent
      data.segment (data.segment_support_subset_parent R T c)
        data.segment_edges data.deleted
  cases resolution with
  | control tail hin hcut => exact .control tail hin hcut
  | geometric outcome =>
      cases outcome with
      | backward tail hin hselected owner link hlink hdir heLink hsub hexposed =>
          exact .backward tail hin hselected owner link hlink hdir heLink hsub
            hexposed
            (selectedOwnerCore_activeBackward_eq_or_rank_lt
              (ControlResolutionIndexed (L := L) (hL := hL)
                (hground := hground)) S K T data.absorber owner
                  data.parent data.parent_exposed link hlink hdir hsub)
      | forwardLastContact splice => exact .forwardSplice splice
      | boundaryDeparture tail hin hresidual htail =>
          exact .boundaryDeparture tail hin hresidual htail

/-- Resolve an unrooted control at the same stopping frontier.  The inactive
branch is immediately refined to the strengthened deleted-edge geometry,
including the oriented forward-splice certificate. -/
theorem splitGroundedRelevantControlResolutionAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (c : ControlRequest (ControlResolutionInput (L := L) (hL := hL)) S.cut)
    (hnot : ¬ ∃ a ∈ ControlResolutionSources R,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ControlResolutionEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a c.1) :
    SplitGroundedRelevantControlResolutionAt R T c := by
  rcases controlAt_unrooted_cases K
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      T (ControlResolutionSources R) c hnot with
    hactive | hretained | hinactive
  · let control : ActiveControlRequestAt
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T := ⟨c, hactive⟩
    exact .active control rfl hnot
      (activeControlAt_unrooted_prefix_outcome
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T
        (ControlResolutionSources R) control hnot)
  · obtain ⟨control, vertex, hvertex, hvertexNot⟩ := hretained
    exact .retained control vertex hvertex hvertexNot hnot
      (activeRequestAt_retainedForwardVertex_unrooted_outcome
        (ControlResolutionIndexed (L := L) (hL := hL)
          (hground := hground)) S K T
        (ControlResolutionSources R) control hvertex hvertexNot)
  · let data := hinactive.some
    exact .inactive data hnot
      (resolveInactiveStoppedRootObstructionAt R T c data)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedRelevantControlResolutionAt
