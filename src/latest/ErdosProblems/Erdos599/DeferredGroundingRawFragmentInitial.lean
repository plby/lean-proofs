/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingHangingSingleton
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Actual initial vertices of backward-changed cut fragments

Groundedness of a parent is not groundedness of every cut fragment.
The actual initial is a source, or is the head of a deleted cut edge.
In the latter case the corresponding real request has strictly later
selection rank. No termination of increasing ordinal ranks is asserted.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (S : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))

local notation "L" => canonicalDeferredLadder Gamma kappa preferred
local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL

include hkappa huncountable hNoEnter in
/-- The actual initial of a backward-changed fragment is grounded or has
a genuine cut predecessor. No inherited-parent predicate is used. -/
theorem canonicalDeferredLadder_rawBackwardFragment_source_or_cutPredecessor
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ GroundingCut.fragments J S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet) :
    P.path.initial ∈ Gamma.source ∨ GroundingConcreteControls.hasCutPredecessor J S.cut P := by
  have hground := canonicalDeferredLadder_rawBackwardOwner_grounded
    preferred hkappa huncountable hNoEnter hL S r P.parent_mem he (P.edges_subset heP)
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      J S.cut P hP with hinitial | hcut
  · exact Or.inl (hinitial ▸ hground)
  · exact Or.inr hcut

include hkappa huncountable hNoEnter in
/-- The cut-predecessor and actual-source cases are mutually exclusive. -/
theorem canonicalDeferredLadder_rawBackwardFragment_source_iff_no_cutPredecessor
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ GroundingCut.fragments J S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet) :
    P.path.initial ∈ Gamma.source ↔
      ¬ GroundingConcreteControls.hasCutPredecessor J S.cut P := by
  constructor
  · rintro hsource ⟨f, _hfCut, hfParent, hfHead⟩
    exact hNoEnter (P.parent.edgeSet_subset_adj hfParent) (hfHead ▸ hsource)
  · intro hnoCut
    exact (canonicalDeferredLadder_rawBackwardFragment_source_or_cutPredecessor
      preferred hkappa huncountable hNoEnter hL S r P hP he heP).resolve_right hnoCut

include hkappa huncountable hNoEnter in
/-- An actual ungrounded fragment initial is precisely the head of a cut
edge, hence the vertex of an actual later request on the same parent. -/
theorem canonicalDeferredLadder_rawBackwardFragment_not_source_later_request
    (r : Request J S.cut) (P : (J).Fragment) (hP : P ∈ GroundingCut.fragments J S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heP : e ∈ P.path.edgeSet)
    (hnot : P.path.initial ∉ Gamma.source) :
    ∃ (f : V × V) (hfCut : f ∈ GroundingCut.CE J S.cut),
      f ∈ P.parent.edgeSet ∧ f.2 = P.path.initial ∧
      requestVertex (Sum.inr (⟨f, hfCut.1⟩ : edgeRequests J S.cut)) = P.path.initial ∧
      GroundingAssembly.requestRank U S r <
        GroundingAssembly.requestRank U S (Sum.inr ⟨f, hfCut.1⟩) := by
  obtain ⟨f, hfCut, hfParent, hfHead⟩ :=
    (canonicalDeferredLadder_rawBackwardFragment_source_or_cutPredecessor
      preferred hkappa huncountable hNoEnter hL S r P hP he heP).resolve_left hnot
  refine ⟨f, hfCut, hfParent, hfHead, hfHead, ?_⟩
  exact reservedRawBackwardOwner_rank_lt_of_apex_mem r (.inr ⟨f, hfCut.1⟩)
    P.parent_mem he (P.edges_subset heP)
    ((PopularSwitching.edge_mem_ladderTrace_iff J P.parent f.1 f.2).2 hfParent)

#print axioms canonicalDeferredLadder_rawBackwardFragment_source_or_cutPredecessor
#print axioms canonicalDeferredLadder_rawBackwardFragment_not_source_later_request

end Erdos599.DWeb.KappaLadder.Deferred
