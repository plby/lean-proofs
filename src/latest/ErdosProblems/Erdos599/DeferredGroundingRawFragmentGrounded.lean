/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawFragmentInitial

/-!
# Intrinsic grounding of every actually backward-changed surviving fragment

The refined real selector avoids the cut-reachable carriers. An actual
backward edge on a cut-preceded fragment would lie in such a carrier,
because its whole parent trace avoids the request apex. Thus the fragment
has no cut predecessor, and its own initial is an original source.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Actual selection avoids the cut-reachable carriers, without any
canonical-ladder hypothesis. -/
theorem reservedStrongSelectedPath_avoids_cutReachableCarrier
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut) :
    Disjoint (strongSelectedPath (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) r).support
        (GroundingCutReachableOwnerAvoidance.carrier S r) := by
  apply Set.disjoint_left.2
  intro z hzPath hzCarrier
  apply strongSelectedPath_not_mem_hangingFragment (popularAuxiliaryIndexed L hL) S
    (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨z, hzPath, hzCarrier⟩))))

/-- No surviving fragment actually changed backwards has a cut edge
immediately preceding it on its reference parent. -/
theorem reservedRawBackwardFragment_no_cutPredecessor
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut)
    (P : (popularAuxiliaryInput L hL.legal).Fragment)
    (hP : P ∈ GroundingCut.fragments (popularAuxiliaryInput L hL.legal) S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (heP : e ∈ P.path.edgeSet) :
    ¬ GroundingConcreteControls.hasCutPredecessor (popularAuxiliaryInput L hL.legal) S.cut P := by
  rintro ⟨s, hsC, hsParent, hsHead⟩
  have hapex := reservedRawBackwardOwner_apex_not_mem r
    P.parent_mem he (P.edges_subset heP)
  have hcarrier := GroundingCutReachableOwnerAvoidance.edge_mem_carrier_of_cutPredecessor
    S r P hP hapex hsC hsParent hsHead heP
  exact Set.disjoint_left.1 (reservedStrongSelectedPath_avoids_cutReachableCarrier r)
    (reservedRawRequestBackward_gadget r he).1 hcarrier

/-- Intrinsic, source-faithful grounding: the fragment's own initial is
an original source, not merely the initial of its parent. -/
theorem canonicalDeferredLadder_rawBackwardFragment_grounded
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (P : (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal).Fragment)
    (hP : P ∈ GroundingCut.fragments
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r)
    (heP : e ∈ P.path.edgeSet) : P.path.initial ∈ Gamma.source := by
  exact (canonicalDeferredLadder_rawBackwardFragment_source_or_cutPredecessor
    preferred hkappa huncountable hNoEnter hL S r P hP he heP).resolve_right
      (reservedRawBackwardFragment_no_cutPredecessor r P hP he heP)

#print axioms reservedStrongSelectedPath_avoids_cutReachableCarrier
#print axioms reservedRawBackwardFragment_no_cutPredecessor
#print axioms canonicalDeferredLadder_rawBackwardFragment_grounded

end Erdos599.DWeb.KappaLadder.Deferred
