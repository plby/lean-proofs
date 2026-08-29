/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning
import ErdosProblems.Erdos599.GroundingErasedSourceGeometry
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Source prefixes for the final deferred strong selector

The final deferred controls attach each selected request to an actual
grounded limiting-ladder record.  The common relevant boundary is chosen to
avoid that whole record.  This file records the resulting finite original
source prefix to the initial vertex of the decoded selected route.

This is the unique non-boundary starting term of the simultaneous
same-owner component transaction.  No edge-survival or realization premise
is included: later last-contact exchange may replace part of this prefix.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
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

private theorem selectedRequestTrace_initial_of_start_old
    (r : Request J S.cut) (x : V)
    (hstart : (strongSelectedPath U S K r).start = .old x) :
    (selectedRequestTrace U S K r).initial = x := by
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈
      (popularAuxiliaryInput L hL.legal).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToExit
        p hpSource y.1 _).initial = x
      apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToExit_initial_of_start_old
      exact hstart
  | inr e =>
      change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry
        p hpSource e.1.1 e.1.2 _).initial = x
      apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry_initial_of_start_old
      exact hstart

private theorem selectedRequestTrace_initial_mem_proxyPath
    (r : Request J S.cut) (i : infiniteRecords L)
    (hstart : (strongSelectedPath U S K r).start = .proxy i) :
    (selectedRequestTrace U S K r).initial ∈
      ((popularAuxiliaryInput L hL.legal).proxyPath i).support := by
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈
      (popularAuxiliaryInput L hL.legal).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToExit
        p hpSource y.1 _).initial ∈
        ((popularAuxiliaryInput L hL.legal).proxyPath i).support
      apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
      exact hstart
  | inr e =>
      change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry
        p hpSource e.1.1 e.1.2 _).initial ∈
        ((popularAuxiliaryInput L hL.legal).proxyPath i).support
      apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
      exact hstart

/-- The decoded selected route begins on its literal deferred starting
record.  This statement retains the exact record rather than only an
existential limiting-warp member. -/
theorem strongSelectedRequestTrace_initial_mem_startingRecord
    (r : Request J S.cut) :
    (selectedRequestTrace U S K r).initial ∈
      (reservedStrongSelectedStartingRecord r).record.support := by
  let R := reservedStrongSelectedStartingRecord r
  rcases R.represents with
      ⟨q, hrecord, hsource⟩ | ⟨i, hrecord, hsource⟩
  · have hstart : (strongSelectedPath U S K r).start = .old q.finish := by
      change (reservedStrongSelectedSource r).1 = .old q.finish
      exact hsource
    have hinitial := selectedRequestTrace_initial_of_start_old r q.finish hstart
    rw [hrecord, hinitial]
    exact q.finish_mem_support
  · have hstart : (strongSelectedPath U S K r).start = .proxy i := by
      change (reservedStrongSelectedSource r).1 = .proxy i
      exact hsource
    rw [hrecord]
    exact selectedRequestTrace_initial_mem_proxyPath r i hstart

/-- A final strong-selected request has a finite original-web prefix from a
genuine source to its decoded initial vertex, entirely inside its actual
starting record and disjoint from the final relevant stopping frontier. -/
theorem exists_strongSelectedRequest_rootPrefix
    (r : Request J S.cut) :
    ∃ q : FinitePath Gamma.graph,
      q.start = (reservedStrongSelectedStartingRecord r).record.initial ∧
        q.start ∈ Gamma.source ∧
        q.finish = (selectedRequestTrace U S K r).initial ∧
        q.support ⊆ (reservedStrongSelectedStartingRecord r).record.support ∧
        q.edgeSet ⊆ (reservedStrongSelectedStartingRecord r).record.edgeSet ∧
        Disjoint q.support T := by
  let R := reservedStrongSelectedStartingRecord r
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix R.record
      (strongSelectedRequestTrace_initial_mem_startingRecord r)
  refine ⟨q, hqStart, ?_, hqFinish, hqSupport, hqEdges, ?_⟩
  · rw [hqStart]
    exact reservedStrongSelectedStartingRecord_grounded r
  · exact
      (reservedStrongSelectedStartingRecord_disjoint_relevantBB r).symm.mono
        hqSupport Set.Subset.rfl

/-- Both endpoints of the canonical starting prefix lie outside the common
stopping frontier. -/
theorem strongSelectedRequestTrace_initial_not_mem_relevantBB
    (r : Request J S.cut) :
    (selectedRequestTrace U S K r).initial ∉ T := by
  intro hT
  exact Set.disjoint_left.mp
    (reservedStrongSelectedStartingRecord_disjoint_relevantBB r)
    hT (strongSelectedRequestTrace_initial_mem_startingRecord r)

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.strongSelectedRequestTrace_initial_mem_startingRecord
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_strongSelectedRequest_rootPrefix
