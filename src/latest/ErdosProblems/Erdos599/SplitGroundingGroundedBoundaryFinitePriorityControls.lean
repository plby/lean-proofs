/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFiniteExchange
import ErdosProblems.Erdos599.GroundingRequestAvoidingControls

/-!
# Priority controls for a private finite exchange

A private finite exchange meets the popular cut only at its finite-source
start.  That start is not a request: old requests explicitly exclude the
finite source set, and edge requests use a different gadget constructor.
Thus every genuine request fan may be reselected to avoid the literal
support of the private route.  Hidden decoded-component contacts are not
discarded here; they remain visible to the switched-relation normalizer.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev PriorityInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev PriorityIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- The finite old source at the private exchange start cannot itself be a
request apex. -/
theorem requestAuxVertex_ne_old_of_mem_finiteSource
    (c : V) (hc : c ∈ (PriorityInput (L := L) (hL := hL)).finiteSource)
    (r : Request (PriorityInput (L := L) (hL := hL)) S.cut) :
    requestAuxVertex r ≠
      (.old c : (PriorityInput (L := L) (hL := hL)).LV) := by
  cases r with
  | inl x =>
      intro heq
      have hxc : x.1 = c :=
        PopularAuxiliary.Input.LambdaVertex.old.inj heq
      exact x.2.2 (hxc ▸ hc)
  | inr e =>
      intro heq
      cases heq

/-- Every request apex misses the literal support of a private finite
exchange.  This deliberately makes no claim about the larger decoded
collision carrier. -/
theorem requestAuxVertex_not_mem_privateSupport
    (c : V) (hc : c ∈ (PriorityInput (L := L) (hL := hL)).finiteSource)
    (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
    (hqPrivate : q.support ∩ S.cut =
      {(.old c : (PriorityInput (L := L) (hL := hL)).LV)})
    (r : Request (PriorityInput (L := L) (hL := hL)) S.cut) :
    requestAuxVertex r ∉ q.support := by
  intro hsupport
  have hinter : requestAuxVertex r ∈ q.support ∩ S.cut :=
    ⟨hsupport, requestAuxVertex_mem_cut r⟩
  have heq : requestAuxVertex r =
      (.old c : (PriorityInput (L := L) (hL := hL)).LV) := by
    simpa only [hqPrivate, Set.mem_singleton_iff] using hinter
  exact requestAuxVertex_ne_old_of_mem_finiteSource c hc r heq

/-- Refine any grounded selector so all later request routes avoid the
literal auxiliary support of one private finite exchange. -/
noncomputable def splitGroundedPrivateSupportAvoidingControls
    (K : GroundingSelection.Controls S)
    (c : V) (hc : c ∈ (PriorityInput (L := L) (hL := hL)).finiteSource)
    (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
    (hqPrivate : q.support ∩ S.cut =
      {(.old c : (PriorityInput (L := L) (hL := hL)).LV)}) :
    GroundingSelection.Controls S :=
  GroundingRequestAvoidingControls.addCountableRequestAvoidance K q.support
    q.support_finite.countable
    (requestAuxVertex_not_mem_privateSupport c hc q hqPrivate)

/-- Every strong path selected after the priority refinement is literally
support-disjoint from the private exchange. -/
theorem splitGroundedPrivateSupportAvoidingStrongSelectedPath_disjoint
    (K : GroundingSelection.Controls S)
    (c : V) (hc : c ∈ (PriorityInput (L := L) (hL := hL)).finiteSource)
    (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
    (hqPrivate : q.support ∩ S.cut =
      {(.old c : (PriorityInput (L := L) (hL := hL)).LV)})
    (r : Request (PriorityInput (L := L) (hL := hL)) S.cut) :
    Disjoint
      (GroundingSimultaneousDecode.strongSelectedPath
        (PriorityIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedPrivateSupportAvoidingControls K c hc q hqPrivate)
        r).support q.support := by
  exact GroundingRequestAvoidingControls.strongSelectedPath_support_disjoint
    (PriorityIndexed (L := L) (hL := hL) (hground := hground)) S K
    q.support q.support_finite.countable
    (requestAuxVertex_not_mem_privateSupport c hc q hqPrivate) r

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.requestAuxVertex_not_mem_privateSupport
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedPrivateSupportAvoidingStrongSelectedPath_disjoint
