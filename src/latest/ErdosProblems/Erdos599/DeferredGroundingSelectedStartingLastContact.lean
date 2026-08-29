/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedTerminalContactOwner
import ErdosProblems.Erdos599.GroundingErasedRouteSuffix

/-!
# Last-contact repair at an actual deferred selected starting record

For the final reserved controls, every selected request starts on a named
grounded inessential limiting record whose whole carrier avoids the common
relevant boundary.  This file performs the source-faithful first half of the
simultaneous transaction: retain that record from its source to the final
contact of the erased selected route, and keep only the selected suffix from
that contact onward.

The retained prefix and selected suffix meet only at the splice vertex.  In
particular, discarding the old record tail loses no relevant boundary point.
No compatibility or realization premise is introduced.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Ladder Stationary
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "T" =>
  reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S)

/-- The literal source-prefix/final-contact data for one request of the
actual final deferred selector. -/
structure ReservedStrongSelectedStartingLastContact
    (r : Request J S.cut) where
  lastContact : (selectedRequestTrace U S K r).erasedRoute.LastContact
    (reservedStrongSelectedStartingRecord r).record.support
  oldPrefix : FinitePath Gamma.graph
  oldPrefix_start :
    oldPrefix.start = (reservedStrongSelectedStartingRecord r).record.initial
  oldPrefix_source : oldPrefix.start ∈ Gamma.source
  oldPrefix_finish : oldPrefix.finish = lastContact.vertex
  oldPrefix_support :
    oldPrefix.support ⊆ (reservedStrongSelectedStartingRecord r).record.support
  oldPrefix_edges :
    oldPrefix.edgeSet ⊆ (reservedStrongSelectedStartingRecord r).record.edgeSet

namespace ReservedStrongSelectedStartingLastContact

variable {r : Request (popularAuxiliaryInput L hL.legal) S.cut}

private abbrev trace
    (_X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :=
  selectedRequestTrace U S K r

/-- The honest selected alternating suffix beginning at the final contact
with the actual starting record. -/
noncomputable def normalizedSuffix
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma)
      (X.trace.erasedRoute.suffixFrom X.lastContact.vertex
        X.lastContact.vertex_mem_chain) :=
  X.lastContact.suffixCompressionOfValid
    (fun {_s} hs ↦ X.trace.valid _
      (X.trace.erasedRoute.steps_sublist.subset hs))

@[simp] theorem normalizedSuffix_initial
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.normalizedSuffix.path.initial = X.lastContact.vertex := by
  exact X.normalizedSuffix.initial_eq

@[simp] theorem normalizedSuffix_terminal
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.normalizedSuffix.path.terminal? = some (requestExit r) := by
  exact X.normalizedSuffix.terminal_eq

/-- The suffix uses only edges already present in the actual selected
compression. -/
theorem normalizedSuffix_edgeSet_subset_selected
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.normalizedSuffix.path.edgeSet ⊆
      (selectedErasedCompression U S K r).path.edgeSet := by
  have hsubset :=
    X.trace.erasedRoute.suffixCompressionOfValid_edgeSet_subset
      X.lastContact.vertex X.lastContact.vertex_mem_chain
      (fun {_s} hs ↦ X.trace.valid _
        (X.trace.erasedRoute.steps_sublist.subset hs))
  simpa only [normalizedSuffix,
    ErasedSignedRoute.LastContact.suffixCompressionOfValid,
    trace, selectedErasedCompression,
    EndpointTrace.erasedCompression] using hsubset

/-- The forward/backward colour of every retained suffix edge agrees with
the original selected compression. -/
theorem normalizedSuffix_directionEdges_subset_selected
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (d : Direction) :
    X.normalizedSuffix.path.directionEdges d ⊆
      (selectedErasedCompression U S K r).path.directionEdges d := by
  have hsubset :=
    X.trace.erasedRoute.suffixCompressionOfValid_directionEdges_subset
      X.lastContact.vertex X.lastContact.vertex_mem_chain
      (fun {_s} hs ↦ X.trace.valid _
        (X.trace.erasedRoute.steps_sublist.subset hs)) d
  simpa only [normalizedSuffix,
    ErasedSignedRoute.LastContact.suffixCompressionOfValid,
    trace, selectedErasedCompression,
    EndpointTrace.erasedCompression] using hsubset

/-- The normalized suffix cannot return to the discarded starting record
away from the splice vertex. -/
theorem normalizedSuffix_meets_record_only_at_contact
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    {v : V} (hvSuffix : v ∈ X.normalizedSuffix.path.vertexSet)
    (hvRecord : v ∈ (reservedStrongSelectedStartingRecord r).record.support) :
    v = X.lastContact.vertex := by
  exact X.lastContact.eq_vertex_of_mem_suffixCompression_vertexSet_of_mem
    (fun {_s} hs ↦ X.trace.valid _
      (X.trace.erasedRoute.steps_sublist.subset hs)) hvSuffix hvRecord

/-- The two retained pieces have exactly one possible common vertex. -/
theorem oldPrefix_inter_normalizedSuffix_subset_contact
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.oldPrefix.support ∩ X.normalizedSuffix.path.vertexSet ⊆
      {X.lastContact.vertex} := by
  intro v hv
  have hvEq := X.normalizedSuffix_meets_record_only_at_contact
    hv.2 (X.oldPrefix_support hv.1)
  simpa only [Set.mem_singleton_iff] using hvEq

/-- The retained old prefix, and indeed the whole discarded old-record
tail, contains no point of the final relevant stopping boundary. -/
theorem oldPrefix_disjoint_relevantBB
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Disjoint T X.oldPrefix.support :=
  (reservedStrongSelectedStartingRecord_disjoint_relevantBB r).mono_right
    X.oldPrefix_support

theorem discardedRecord_disjoint_relevantBB
    (_X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Disjoint T (reservedStrongSelectedStartingRecord r).record.support :=
  reservedStrongSelectedStartingRecord_disjoint_relevantBB r

end ReservedStrongSelectedStartingLastContact

/-- Every actual final selected request admits the literal source-prefix /
last-contact repair at its named starting record. -/
theorem exists_reservedStrongSelectedStartingLastContact
    (r : Request J S.cut) :
    Nonempty (ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) := by
  let trace := selectedRequestTrace U S K r
  let E := trace.erasedRoute
  have hlen : 0 < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  let i : Fin E.vertexChain.length := ⟨0, hlen⟩
  have hi : E.vertexChain[i] = trace.initial := by
    change E.vertexChain.get i = trace.initial
    have hzero := E.routeVertex_zero
    unfold ErasedSignedRoute.routeVertex at hzero
    simpa only [i, List.getD_eq_get E.vertexChain (requestExit r) i] using hzero
  have hcontact : ∃ j : Fin E.vertexChain.length,
      E.vertexChain[j] ∈
        (reservedStrongSelectedStartingRecord r).record.support := by
    refine ⟨i, ?_⟩
    rw [hi]
    exact strongSelectedRequestTrace_initial_mem_startingRecord r
  let C : E.LastContact
      (reservedStrongSelectedStartingRecord r).record.support :=
    (E.exists_lastContact
      (reservedStrongSelectedStartingRecord r).record.support hcontact).some
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (reservedStrongSelectedStartingRecord r).record C.vertex_mem
  refine ⟨{
    lastContact := C
    oldPrefix := q
    oldPrefix_start := hqStart
    oldPrefix_source := ?_
    oldPrefix_finish := hqFinish
    oldPrefix_support := hqSupport
    oldPrefix_edges := hqEdges }⟩
  rw [hqStart]
  exact reservedStrongSelectedStartingRecord_grounded r

/-- Along the actual last-contact-normalized suffix, every essential owner
is either genuinely source-grounded or is the displayed terminal component.
Thus the source repair introduces no further essential hanging root. -/
theorem canonicalDeferredLadder_startingLastContact_essentialOwner_grounded_or_terminal
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    {x : V} (hxSuffix : x ∈ X.normalizedSuffix.path.vertexSet)
    (hxY : x ∈ Y.support) :
    Y.initial ∈ Gamma.source ∨ Y = Z := by
  let lad := canonicalDeferredLadder Gamma kappa preferred
  let input := popularAuxiliaryInput lad hL.legal
  let indexed := popularAuxiliaryIndexed lad hL
  let controls := reservedGroundedCarrierControls lad hL S
  let trace := selectedRequestTrace indexed S controls r
  let erased := trace.erasedRoute
  have hvalid : ∀ {s : SignedEdge V}, s ∈ erased.steps →
      SignedEdge.Valid (Gamma := Gamma) s := by
    intro s hs
    exact trace.valid s (erased.steps_sublist.subset hs)
  have hvalidSuffix : ∀ {s : SignedEdge V},
      s ∈ (erased.suffixFrom X.lastContact.vertex
        X.lastContact.vertex_mem_chain).steps →
      SignedEdge.Valid (Gamma := Gamma) s := by
    intro s hs
    exact hvalid (erased.suffixFrom_steps_subset
      X.lastContact.vertex X.lastContact.vertex_mem_chain hs)
  have hxSuffix' : x ∈
      ((erased.suffixFrom X.lastContact.vertex
        X.lastContact.vertex_mem_chain).compressionOfValid
          hvalidSuffix).path.vertexSet := by
    simpa only [ReservedStrongSelectedStartingLastContact.normalizedSuffix,
      ErasedSignedRoute.LastContact.suffixCompressionOfValid,
      ErasedSignedRoute.suffixCompressionOfValid,
      trace, erased, indexed, controls, lad] using hxSuffix
  have hxSuffixChain : x ∈
      (erased.suffixFrom X.lastContact.vertex
        X.lastContact.vertex_mem_chain).vertexChain := by
    exact (erased.suffixFrom X.lastContact.vertex
      X.lastContact.vertex_mem_chain).compressionOfValid_vertexSet_subset_vertexChain
        hvalidSuffix hxSuffix'
  have hxChain : x ∈ erased.vertexChain :=
    erased.suffixFrom_vertexChain_subset X.lastContact.vertex
      X.lastContact.vertex_mem_chain hxSuffixChain
  have hxSelected : x ∈
      (selectedErasedCompression indexed S controls r).path.vertexSet := by
    have hxCompression :=
      erased.vertexChain_subset_compressionOfValid_vertexSet
      hvalid hxChain
    simpa only [erased, trace, selectedErasedCompression,
      EndpointTrace.erasedCompression] using hxCompression
  have hxCarrier : x ∈ input.decodedVertexCarrier
      (strongSelectedPath indexed S controls r) := by
    exact GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      indexed S controls r hxSelected
  rcases
      canonicalDeferredLadder_reservedStrongSelected_essentialOwner_contact_grounded_or_apex
        preferred hkappa huncountable hNoEnter hL S r Y hY hxCarrier hxY with
    hgrounded | hapex
  · exact Or.inl hgrounded
  · have hYEssential : Y ∈ Gamma.essentialWarpPart lad.limitWarp := by
      simpa only [lad, input, popularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder, limitWarp] using hY
    exact Or.inr
      (eq_terminalOwner_of_requestAuxVertex_mem_ladderTrace
        input r (W := lad.limitWarp) (by
          simpa only [lad, input, popularAuxiliaryInput, limitWarp] using
            (popularAuxiliaryInput lad hL.legal).ladder.disjoint)
        Y Z hYEssential.1
        hZ hapex hexit)

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_reservedStrongSelectedStartingLastContact
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.normalizedSuffix_meets_record_only_at_contact
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.discardedRecord_disjoint_relevantBB
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_startingLastContact_essentialOwner_grounded_or_terminal
