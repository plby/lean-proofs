/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedLastContact
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Literal component splice at a selected route's final owner contact

The source-faithful duplicate-start repair keeps the initial prefix of the
starting ladder component through the selected route's final contact, then
continues with the suffix of that selected route.  This module packages the
two literal pieces and their one-point intersection.

No boundary-avoidance statement is included: a point of the final stopping
frontier may lie on the discarded old-owner tail.  Transporting or replacing
such a point is the remaining global exchange obligation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ComponentSpliceIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

namespace SplitGroundedReducedForwardConflictLastContact

variable {T : Set V} {parent : Gamma.DPath}

private abbrev trace
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :=
  selectedRequestTrace
    (ComponentSpliceIndexed (L := L) (hL := hL) (hground := hground))
    S K (chosenRequest D.owner.1)

/-- The canonical alternating selected-route suffix beginning at the final
contact with the old owner. -/
noncomputable def normalizedSuffix
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) : ErasedSignedRoute.ErasedCompression (Gamma := Gamma)
      (D.trace.erasedRoute.suffixFrom D.lastContact.vertex
        D.lastContact.vertex_mem_chain) :=
  D.lastContact.suffixCompressionOfValid
    (fun {_s} hs ↦ D.trace.valid _
      (D.trace.erasedRoute.steps_sublist.subset hs))

@[simp] theorem normalizedSuffix_initial
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :
    D.normalizedSuffix.path.initial = D.lastContact.vertex := by
  exact D.suffix_initial

@[simp] theorem normalizedSuffix_terminal
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :
    D.normalizedSuffix.path.terminal? =
      some (requestExit (chosenRequest D.owner.1)) := by
  exact D.suffix_terminal

/-- Every edge of the normalized suffix is an edge of the original selected
compression, preserving its selected-route provenance. -/
theorem normalizedSuffix_edgeSet_subset_selected
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent) :
    D.normalizedSuffix.path.edgeSet ⊆
      (selectedErasedCompression
        (ComponentSpliceIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest D.owner.1)).path.edgeSet := by
  have hsubset := D.trace.erasedRoute.suffixCompressionOfValid_edgeSet_subset
    D.lastContact.vertex D.lastContact.vertex_mem_chain
      (fun {_s} hs ↦ D.trace.valid _
        (D.trace.erasedRoute.steps_sublist.subset hs))
  simpa only [normalizedSuffix,
    ErasedSignedRoute.LastContact.suffixCompressionOfValid, trace,
    selectedErasedCompression, EndpointTrace.erasedCompression] using hsubset

/-- Forward and backward colours are both preserved by the last-contact
normalization.  Thus the suffix can replace the original selected route in
a simultaneous switch without reclassifying any retained edge. -/
theorem normalizedSuffix_directionEdges_subset_selected
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent)
    (d : Alternating.Direction) :
    D.normalizedSuffix.path.directionEdges d ⊆
      (selectedErasedCompression
        (ComponentSpliceIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest D.owner.1)).path.directionEdges d := by
  have hsubset :=
    D.trace.erasedRoute.suffixCompressionOfValid_directionEdges_subset
      D.lastContact.vertex D.lastContact.vertex_mem_chain
        (fun {_s} hs ↦ D.trace.valid _
          (D.trace.erasedRoute.steps_sublist.subset hs)) d
  simpa only [normalizedSuffix,
    ErasedSignedRoute.LastContact.suffixCompressionOfValid, trace,
    selectedErasedCompression, EndpointTrace.erasedCompression] using hsubset

/-- The normalized selected suffix never returns to its old owner away from
the chosen splice vertex. -/
theorem normalizedSuffix_meets_parent_only_at_vertex
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent)
    {v : V} (hvSuffix : v ∈ D.normalizedSuffix.path.vertexSet)
    (hvParent : v ∈ parent.support) :
    v = D.lastContact.vertex := by
  exact D.suffix_meets_parent_only_at_vertex hvSuffix hvParent

end SplitGroundedReducedForwardConflictLastContact

/-- Literal source-repair data for one selected route.  The record retains
the actual old owner, the final-contact certificate (and hence active request
and retained selected edge), its finite initial prefix, and the canonical
no-return selected suffix. -/
structure SplitGroundedLastContactComponentSplice (T : Set V) where
  oldOwner : Gamma.DPath
  contact : SplitGroundedReducedForwardConflictLastContact
    (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
      T oldOwner
  oldPrefix : FinitePath Gamma.graph
  oldPrefix_start : oldPrefix.start = oldOwner.initial
  oldPrefix_finish : oldPrefix.finish = contact.lastContact.vertex
  oldPrefix_support : oldPrefix.support ⊆ oldOwner.support
  oldPrefix_edges : oldPrefix.edgeSet ⊆ oldOwner.edgeSet
  prefix_suffix_inter : oldPrefix.support ∩
      contact.normalizedSuffix.path.vertexSet ⊆
    {contact.lastContact.vertex}

namespace SplitGroundedLastContactComponentSplice

variable {T : Set V}

/-- The literal vertex carrier of the replacement component. -/
def replacementCarrier
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T) :
    Set V := X.oldPrefix.support ∪ X.contact.normalizedSuffix.path.vertexSet

/-- The retained old prefix and the normalized selected suffix join at the
literal final-contact vertex. -/
theorem join_vertex
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T) :
    X.oldPrefix.finish = X.contact.normalizedSuffix.path.initial := by
  rw [X.oldPrefix_finish, X.contact.normalizedSuffix_initial]

/-- The component replacement still begins at the original ladder owner. -/
theorem replacement_initial
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T) :
    X.oldPrefix.start = X.oldOwner.initial :=
  X.oldPrefix_start

/-- The component replacement ends at the selected request exit. -/
theorem replacement_terminal
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T) :
    X.contact.normalizedSuffix.path.terminal? =
      some (requestExit (chosenRequest X.contact.owner.1)) :=
  X.contact.normalizedSuffix_terminal

/-- If the old starting owner avoids a frontier, then so does the retained
old prefix. -/
theorem oldPrefix_disjoint_frontier
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T)
    {B : Set V} (howner : Disjoint B X.oldOwner.support) :
    Disjoint B X.oldPrefix.support :=
  howner.mono_right X.oldPrefix_support

/-- Under old-owner frontier avoidance, every frontier point of the new
component lies on the selected suffix.  Hence discarding the old owner tail
does not lose a frontier point attributable to that owner. -/
theorem frontier_mem_normalizedSuffix
    (X : SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T)
    {B : Set V} (howner : Disjoint B X.oldOwner.support)
    {b : V} (hbB : b ∈ B) (hb : b ∈ X.replacementCarrier) :
    b ∈ X.contact.normalizedSuffix.path.vertexSet := by
  rcases hb with hbPrefix | hbSuffix
  · exact False.elim (Set.disjoint_left.mp
      (X.oldPrefix_disjoint_frontier howner) hbB hbPrefix)
  · exact hbSuffix

end SplitGroundedLastContactComponentSplice

/-- Construct the literal old-prefix/selected-suffix replacement from the
last-contact certificate already stored in a forward-conflict splice. -/
theorem SplitGroundedReducedForwardConflictSpliceData.exists_componentSplice
    {T : Set V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt
        (ComponentSpliceIndexed (L := L) (hL := hL) (hground := hground))
        S K T)}
    (data : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D) :
    Nonempty (SplitGroundedLastContactComponentSplice
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T) := by
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent
      data.contact.lastContact.vertex_mem
  refine ⟨{
    oldOwner := parent
    contact := data.contact
    oldPrefix := q
    oldPrefix_start := hqStart
    oldPrefix_finish := hqFinish
    oldPrefix_support := hqSupport
    oldPrefix_edges := hqEdges
    prefix_suffix_inter := ?_ }⟩
  intro v hv
  have hvEq := data.contact.normalizedSuffix_meets_parent_only_at_vertex
    hv.2 (hqSupport hv.1)
  simpa only [hvEq, Set.mem_singleton_iff]

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.exists_componentSplice
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.normalizedSuffix_meets_parent_only_at_vertex
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.normalizedSuffix_directionEdges_subset_selected
