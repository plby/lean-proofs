/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteSuffix
import ErdosProblems.Erdos599.SplitGroundingGroundedReducedRootNormalization

/-!
# Last-contact data for a reduced-frontier forward conflict

The source-correct root dispatcher is stopped at an arbitrary final
frontier `T`.  A forward-conflict leaf there already contains a retained
forward edge of one active selected route at that same frontier.  If the
conflict identifies either endpoint of the deleted parent edge with the
corresponding endpoint of the selected edge, that endpoint is a literal
contact between the selected signed route and the old parent.

This module chooses the final such contact and records the honest
direction-preserving alternating suffix.  It does not assume that the
discarded old-parent tail is boundary-free.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
open PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ReducedContactIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Positive owner and final-contact data extracted from one actual
forward-conflict deletion in the relation stopped at `T`. -/
structure SplitGroundedReducedForwardConflictLastContact
    (T : Set V) (parent : Gamma.DPath) where
  owner : ActiveControlRequestAt
    (ReducedContactIndexed (L := L) (hL := hL) (hground := hground)) S K T
  forwardEdge : V × V
  retained : forwardEdge ∈ retainedForwardEdgesAt T
    (selectedErasedCompression
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K (chosenRequest owner.1)).path
  lastContact :
    (selectedRequestTrace
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K (chosenRequest owner.1)).erasedRoute.LastContact parent.support

/-- The exact incidence retained from the deleted incoming parent edge.
The coarser last-contact datum above is enough to normalize the selected
route, but the tail/head alternative is needed to decide whether the splice
returns through the tail of the retained selected edge or replaces the
deleted head itself. -/
structure SplitGroundedReducedForwardConflictSpliceData
    (T : Set V) (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K T)) where
  contact : SplitGroundedReducedForwardConflictLastContact
    (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T parent
  incomingTail : V
  incoming_mem : (incomingTail, D.head) ∈ p.edgeSet
  endpointConflict : incomingTail = contact.forwardEdge.1 ∨
    D.head = contact.forwardEdge.2
  segmentLastContact :
    (selectedRequestTrace
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K (chosenRequest contact.owner.1)).erasedRoute.LastContact p.support

namespace SplitGroundedReducedForwardConflictLastContact

variable {T : Set V} {parent : Gamma.DPath}

private abbrev trace
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :=
  selectedRequestTrace
    (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
    S K (chosenRequest D.owner.1)

/-- The normalized suffix begins at the final old-parent contact. -/
theorem suffix_initial
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :
    (D.lastContact.suffixCompressionOfValid
      (fun {_s} hs ↦ D.trace.valid _
        (D.trace.erasedRoute.steps_sublist.subset hs))).path.initial =
      D.lastContact.vertex := by
  exact D.trace.erasedRoute.suffixCompressionOfValid_initial_eq
    D.lastContact.vertex D.lastContact.vertex_mem_chain _

/-- The normalized suffix retains the selected request exit. -/
theorem suffix_terminal
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :
    (D.lastContact.suffixCompressionOfValid
      (fun {_s} hs ↦ D.trace.valid _
        (D.trace.erasedRoute.steps_sublist.subset hs))).path.terminal? =
      some (requestExit (chosenRequest D.owner.1)) := by
  exact D.trace.erasedRoute.suffixCompressionOfValid_terminal_eq
    D.lastContact.vertex D.lastContact.vertex_mem_chain _

/-- After normalization the selected suffix never returns to the old
parent away from its splice vertex. -/
theorem suffix_meets_parent_only_at_vertex
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent)
    {v : V}
    (hvSuffix : v ∈ (D.lastContact.suffixCompressionOfValid
      (fun {_s} hs ↦ D.trace.valid _
        (D.trace.erasedRoute.steps_sublist.subset hs))).path.vertexSet)
    (hvParent : v ∈ parent.support) :
    v = D.lastContact.vertex := by
  exact D.lastContact.eq_vertex_of_mem_suffixCompression_vertexSet_of_mem
    (fun {_s} hs ↦ D.trace.valid _
      (D.trace.erasedRoute.steps_sublist.subset hs)) hvSuffix hvParent

end SplitGroundedReducedForwardConflictLastContact

namespace SplitGroundedReducedForwardConflictSpliceData

variable {T : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
  {D : LastDeletedHead p
    (erasedSelectedSwitchedEdgesAt
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K T)}

/-- The segment-local final contact lies no later than the finite segment's
terminal.  Unlike the whole-parent contact, it can therefore be used at a
nonempty stopping frontier. -/
theorem segmentLastContact_beforeEq_finish
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D) :
    GroundingCut.BeforeEq (.inl p : Gamma.DPath)
      data.segmentLastContact.vertex p.finish := by
  exact GroundingCut.beforeEq_terminal (P := (.inl p : Gamma.DPath)) rfl
    data.segmentLastContact.vertex_mem

/-- Exact positional split between the surviving-suffix head and the final
selected-route contact on the finite segment. -/
theorem segmentLastContact_beforeEq_head_or_head_beforeEq
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D) :
    GroundingCut.BeforeEq (.inl p : Gamma.DPath)
        data.segmentLastContact.vertex D.head ∨
      GroundingCut.BeforeEq (.inl p : Gamma.DPath)
        D.head data.segmentLastContact.vertex := by
  have hhead : D.head ∈ p.support :=
    (p.edgeSet_subset_support_prod data.incoming_mem).2
  exact GroundingCut.beforeEq_total data.segmentLastContact.vertex_mem hhead

end SplitGroundedReducedForwardConflictSpliceData

/-- Every forward-conflict class in the corrected reduced root normal form
has an actual active selected owner and a final contact with the old
parent, at the same stopping frontier `T`. -/
theorem exists_splitGroundedReducedForwardConflictSpliceData
    (T : Set V) (parent : Gamma.DPath)
    {p : FinitePath Gamma.graph} (hpParent : p.support ⊆ parent.support)
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K T))
    (u : V) (huParent : (u, D.head) ∈ p.edgeSet)
    (hconflict : (u, D.head) ∈ forwardConflictCutEdgesAt
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K T) :
    Nonempty (SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
      T parent p D) := by
  obtain ⟨_huResidual, f, hf, htail | hhead⟩ := hconflict
  all_goals
    simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at hf
    obtain ⟨owner, howner⟩ := hf
    let trace := selectedRequestTrace
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K (chosenRequest owner.1)
    let E := trace.erasedRoute
    have hfDirection : f ∈ (selectedErasedCompression
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest owner.1)).path.directionEdges .forward :=
      retainedForwardEdgesAt_subset_directionEdges T _ howner
    have hfEdge : f ∈ (selectedErasedCompression
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest owner.1)).path.edgeSet := by
      rw [(selectedErasedCompression
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest owner.1)).path.edgeSet_eq_directionEdges_union]
      exact Or.inl hfDirection
    have hfEnds : f.1 ∈ E.vertexChain ∧ f.2 ∈ E.vertexChain := by
      have hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
          SignedEdge.Valid (Gamma := Gamma) s := by
        intro s hs
        exact trace.valid s (E.steps_sublist.subset hs)
      apply E.compressionOfValid_edge_endpoints_mem_vertexChain hvalid
      change f ∈ trace.erasedCompression.path.edgeSet
      simpa only [trace, E, selectedErasedCompression,
        EndpointTrace.erasedCompression] using hfEdge
  · have huSupport : u ∈ parent.support :=
      hpParent (p.edgeSet_subset_support_prod huParent).1
    have huSegment : u ∈ p.support :=
      (p.edgeSet_subset_support_prod huParent).1
    have hcontact : ∃ i : Fin E.vertexChain.length,
        E.vertexChain[i] ∈ parent.support := by
      obtain ⟨i, hi⟩ := List.get_of_mem hfEnds.1
      refine ⟨i, ?_⟩
      change E.vertexChain.get i ∈ parent.support
      rw [hi, ← htail]
      exact huSupport
    have hsegmentContact : ∃ i : Fin E.vertexChain.length,
        E.vertexChain[i] ∈ p.support := by
      obtain ⟨i, hi⟩ := List.get_of_mem hfEnds.1
      refine ⟨i, ?_⟩
      change E.vertexChain.get i ∈ p.support
      rw [hi, ← htail]
      exact huSegment
    exact ⟨{
      contact := {
        owner := owner
        forwardEdge := f
        retained := howner
        lastContact := (E.exists_lastContact parent.support hcontact).some }
      incomingTail := u
      incoming_mem := huParent
      endpointConflict := Or.inl htail
      segmentLastContact :=
        (E.exists_lastContact p.support hsegmentContact).some }⟩
  · have hheadSupport : D.head ∈ parent.support :=
      hpParent (p.edgeSet_subset_support_prod huParent).2
    have hheadSegment : D.head ∈ p.support :=
      (p.edgeSet_subset_support_prod huParent).2
    have hcontact : ∃ i : Fin E.vertexChain.length,
        E.vertexChain[i] ∈ parent.support := by
      obtain ⟨i, hi⟩ := List.get_of_mem hfEnds.2
      refine ⟨i, ?_⟩
      change E.vertexChain.get i ∈ parent.support
      rw [hi, ← hhead]
      exact hheadSupport
    have hsegmentContact : ∃ i : Fin E.vertexChain.length,
        E.vertexChain[i] ∈ p.support := by
      obtain ⟨i, hi⟩ := List.get_of_mem hfEnds.2
      refine ⟨i, ?_⟩
      change E.vertexChain.get i ∈ p.support
      rw [hi, ← hhead]
      exact hheadSegment
    exact ⟨{
      contact := {
        owner := owner
        forwardEdge := f
        retained := howner
        lastContact := (E.exists_lastContact parent.support hcontact).some }
      incomingTail := u
      incoming_mem := huParent
      endpointConflict := Or.inr hhead
      segmentLastContact :=
        (E.exists_lastContact p.support hsegmentContact).some }⟩

/-- Coarse final-contact data, retained as a compatibility projection for
the existing reduced-root normalizers. -/
theorem exists_splitGroundedReducedForwardConflictLastContact
    (T : Set V) (parent : Gamma.DPath)
    {p : FinitePath Gamma.graph} (hpParent : p.support ⊆ parent.support)
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
        S K T))
    (u : V) (huParent : (u, D.head) ∈ p.edgeSet)
    (hconflict : (u, D.head) ∈ forwardConflictCutEdgesAt
      (ReducedContactIndexed (L := L) (hL := hL) (hground := hground))
      S K T) :
    Nonempty (SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
      T parent) := by
  exact ⟨(L.exists_splitGroundedReducedForwardConflictSpliceData
    T parent hpParent D u huParent hconflict).some.contact⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedReducedForwardConflictSpliceData
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedReducedForwardConflictLastContact
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.suffix_meets_parent_only_at_vertex
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.segmentLastContact_beforeEq_head_or_head_beforeEq
