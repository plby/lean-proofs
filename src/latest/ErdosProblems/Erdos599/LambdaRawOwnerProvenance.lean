/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerSuffix
import ErdosProblems.Erdos599.GroundingErasedSwitchRelation

/-!
# Raw attachment provenance in its original auxiliary path

Every inserted forward edge is an actual proper deterministic connector
of the original path. Its endpoints therefore remain in the raw decoded
carrier. Removing the starting owner also removes the only possible
proxy/reference overlap, so all inserted edges are outside the reference.
-/

noncomputable section

namespace Erdos599.PopularAuxiliary.Input.RawOwnerAttachment

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I} {H : Gamma.DPath}
variable {p : FinitePath L.lambda.graph} (A : L.RawOwnerAttachment H p)

theorem forwardEdges_subset_original_properConnectors :
    A.forwardEdges ⊆ L.properSelectedConnectorEdges p := by
  intro e he
  rcases he with he | he
  · have heq : e = (A.anchor, A.nextVertex) := Set.mem_singleton_iff.1 he
    subst e
    exact ⟨⟨A.origin, A.tail.start, A.origin_arc, A.connector_eq⟩, A.anchor_ne_next⟩
  · obtain ⟨⟨a, b, hab, hchoice⟩, hne⟩ := he
    exact ⟨⟨a, b, A.tail_edges_subset hab, hchoice⟩, hne⟩

theorem forwardEdges_endpoints_mem_originalCarrier {e : V × V}
    (he : e ∈ A.forwardEdges) :
    e.1 ∈ L.decodedVertexCarrier p ∧ e.2 ∈ L.decodedVertexCarrier p :=
  L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p
    (Or.inr (A.forwardEdges_subset_original_properConnectors he).1)

/-- The suffix has no proxy, and its initial connector leaves its owner;
neither type of insertion can itself be a reference edge. -/
theorem forwardEdges_disjoint_reference
    (hL : L.HasBoundaryIncidence) (hH : H ∈ L.ladder.paths) :
    Disjoint A.forwardEdges L.familyEdges := by
  apply Set.disjoint_left.2
  intro e he href
  rcases he with he | he
  · have heq : e = (A.anchor, A.nextVertex) := Set.mem_singleton_iff.1 he
    subst e
    exact A.next_not_mem_owner (H.edgeSet_subset_support_prod
      (L.referenceEdge_mem_owner_of_tail hH href A.anchor_mem_owner)).2
  · obtain ⟨⟨a, b, hab, hchoice⟩, _hne⟩ := he
    have hne : a ≠ b := GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet
      (P := (Sum.inl A.tail : L.lambda.DPath)) hab
    obtain ⟨i, rfl, _hnode, _hi⟩ := hL.forward_reference_classification
      (A.tail.edgeSet_subset_adj hab) hne (L.chosenConnector?_eq_some hchoice) href
    exact A.tail_no_proxy i (A.tail.edgeSet_subset_support_prod hab).1

#print axioms forwardEdges_endpoints_mem_originalCarrier
#print axioms forwardEdges_disjoint_reference

end Erdos599.PopularAuxiliary.Input.RawOwnerAttachment
