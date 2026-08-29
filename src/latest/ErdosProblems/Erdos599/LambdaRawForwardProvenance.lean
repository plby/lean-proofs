/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaDecoder
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# Reference-edge provenance before erasing a Lambda route

A raw forward connector can itself be a reference edge only on the first
proxy-to-edge arc. This is a property of the actual six arc classes and
auxiliary path simplicity, not a normalization hypothesis on decoded words.
Keeping the raw backward gadgets is important for the companion components
in the eventual simultaneous switch.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

/-- The two endpoint incidence facts satisfied by the actual Section 8
auxiliary. They are deliberately not built into the general `Input`. -/
structure HasBoundaryIncidence : Prop where
  finite_source_sink : ∀ ⦃x : V⦄, x ∈ L.finiteSource →
    ¬ HasOutgoing L.familyEdges x
  target_marker_root : ∀ ⦃x : V⦄, x ∈ L.targetMarkers →
    ¬ HasIncoming L.familyEdges x

/-- The reference relation is locally biunique. -/
theorem raw_familyEdges_biUnique :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ L.familyEdges) := by
  simpa only [familyEdges, Alternating.familyEdges, Set.mem_ofPred_eq,
    Set.mem_iUnion, exists_prop] using IsWarp.familyEdges_biUnique L.ladder.disjoint

/-- No reference edge is a loop, even when the ambient digraph has loops. -/
theorem raw_familyEdge_ne {x y : V} (he : (x, y) ∈ L.familyEdges) :
    x ≠ y := by
  obtain ⟨p, _hp, hep⟩ := he
  exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet hep

variable {L}

theorem HasBoundaryIncidence.noOutgoing_oldForward
    (hL : L.HasBoundaryIncidence) {x : V}
    (hx : x ∈ L.offLadder ∪ L.finiteSource) :
    ¬ HasOutgoing L.familyEdges x := by
  rcases hx with hx | hx
  · rintro ⟨y, p, hp, hxy⟩
    exact hx.2 ⟨p, hp, (p.edgeSet_subset_support_prod hxy).1⟩
  · exact hL.finite_source_sink hx

theorem HasBoundaryIncidence.noIncoming_oldForward
    (hL : L.HasBoundaryIncidence) {x : V}
    (hx : x ∈ L.offLadder ∪ L.targetMarkers) :
    ¬ HasIncoming L.familyEdges x := by
  rcases hx with hx | hx
  · rintro ⟨y, p, hp, hyx⟩
    exact hx.2 ⟨p, hp, (p.edgeSet_subset_support_prod hyx).2⟩
  · exact hL.target_marker_root hx

/-- The only reference edge that can be decoded forwards on a non-loop
auxiliary arc is the initial proxy attachment to that very edge gadget. -/
theorem HasBoundaryIncidence.forward_reference_classification
    (hL : L.HasBoundaryIncidence) {a b : L.LV} {x y : V}
    (hab : L.lambda.graph.Adj a b) (hne : a ≠ b)
    (hc : L.ForwardConnector a b x y)
    (he : (x, y) ∈ L.familyEdges) :
    ∃ i : I, a = .proxy i ∧ b = .edge x y ∧
      x ∈ (L.proxyPath i).support := by
  change L.LambdaAdj a b at hab
  rcases hab with hVV | hEV | hVE | hEE | hIV | hIE
  · obtain ⟨q, r, rfl, rfl, hq, _hr, _hqr⟩ := hVV
    have hqx : q = x := by simpa using hc.1
    subst x
    exact False.elim (hL.noOutgoing_oldForward hq ⟨y, he⟩)
  · obtain ⟨q, r, z, rfl, rfl, _hqr, hz⟩ := hEV
    have hqx : q = x := by simpa using hc.1
    have hzy : z = y := by simpa using hc.2.1
    subst x
    subst y
    rcases hz with rfl | ⟨hz, _hqz⟩
    · exact False.elim (L.raw_familyEdge_ne he rfl)
    · exact False.elim (hL.noIncoming_oldForward hz ⟨q, he⟩)
  · obtain ⟨q, r, z, rfl, rfl, _hrz, hq⟩ := hVE
    have hqx : q = x := by simpa using hc.1
    have hzy : z = y := by simpa using hc.2.1
    subst x
    subst y
    rcases hq with rfl | ⟨hq, _hqz⟩
    · exact False.elim (L.raw_familyEdge_ne he rfl)
    · exact False.elim (hL.noOutgoing_oldForward hq ⟨z, he⟩)
  · obtain ⟨q, r, w, z, rfl, rfl, hqr, hwz, _hqz⟩ := hEE
    have hqx : q = x := by simpa using hc.1
    have hzy : z = y := by simpa using hc.2.1
    subst x
    subst y
    have hrz : r = z := L.raw_familyEdges_biUnique.2 hqr he
    have hwq : w = q := L.raw_familyEdges_biUnique.1 hwz he
    exact False.elim (hne (by rw [hrz, hwq]))
  · obtain ⟨i, z, rfl, rfl, hz, _hattach⟩ := hIV
    have hzy : z = y := by simpa using hc.2.1
    subst y
    exact False.elim (hL.noIncoming_oldForward hz ⟨x, he⟩)
  · obtain ⟨i, w, z, rfl, rfl, hwz, _hattach⟩ := hIE
    have hzy : z = y := by simpa using hc.2.1
    subst y
    have hwx : w = x := L.raw_familyEdges_biUnique.1 hwz he
    have hxi : x ∈ (L.proxyPath i).support := by simpa using hc.1
    exact ⟨i, rfl, by rw [hwx], hxi⟩

/-- On a source-starting finite route, every forward reference edge uses
the starting proxy, and the represented backward gadget is retained. -/
theorem HasBoundaryIncidence.connector_reference_at_start
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {e : V × V}
    (he : e ∈ L.connectorEdges p) (href : e ∈ L.familyEdges) :
    ∃ i : I, p.start = .proxy i ∧
      (.proxy i, .edge e.1 e.2) ∈ p.edgeSet ∧
      e.1 ∈ (L.proxyPath i).support ∧ e ∈ L.representedEdges p := by
  obtain ⟨a, b, hab, hc⟩ := he
  have hne : a ≠ b :=
    GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet
      (P := (Sum.inl p : L.lambda.DPath)) hab
  obtain ⟨i, rfl, rfl, hxi⟩ :=
    hL.forward_reference_classification (p.edgeSet_subset_adj hab) hne hc href
  have hstart : p.start = .proxy i :=
    L.proxy_mem_support_eq_start p hs
      (p.edgeSet_subset_support_prod hab).1
  exact ⟨i, hstart, hab, hxi, (p.edgeSet_subset_support_prod hab).2, href⟩

/-- Ordinary finite-source routes have disjoint raw forward and reference
edge sets; no physical loop erasure is used. -/
theorem HasBoundaryIncidence.connectorEdges_disjoint_familyEdges_of_start_old
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {x : V} (hstart : p.start = .old x) :
    Disjoint (L.connectorEdges p) L.familyEdges := by
  apply Set.disjoint_left.2
  intro e he href
  obtain ⟨i, hi, _⟩ := hL.connector_reference_at_start p hs he href
  rw [hstart] at hi
  cases hi

/-- The deterministic raw decoder has at most one forward reference edge.
Both candidates must be decoded from the same first auxiliary arc. -/
theorem HasBoundaryIncidence.selected_reference_subsingleton
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) :
    (L.selectedConnectorEdges p ∩ L.familyEdges).Subsingleton := by
  intro e he f hf
  obtain ⟨a, b, hab, heChoice⟩ := he.1
  obtain ⟨c, d, hcd, hfChoice⟩ := hf.1
  have habne : a ≠ b :=
    GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet
      (P := (Sum.inl p : L.lambda.DPath)) hab
  have hcdne : c ≠ d :=
    GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet
      (P := (Sum.inl p : L.lambda.DPath)) hcd
  obtain ⟨i, rfl, rfl, _hxi⟩ :=
    hL.forward_reference_classification (p.edgeSet_subset_adj hab) habne
      (L.chosenConnector?_eq_some heChoice) he.2
  obtain ⟨j, rfl, rfl, _hxj⟩ :=
    hL.forward_reference_classification (p.edgeSet_subset_adj hcd) hcdne
      (L.chosenConnector?_eq_some hfChoice) hf.2
  have hi : LambdaVertex.proxy i = p.start :=
    (L.proxy_mem_support_eq_start p hs (p.edgeSet_subset_support_prod hab).1).symm
  have hj : LambdaVertex.proxy j = p.start :=
    (L.proxy_mem_support_eq_start p hs (p.edgeSet_subset_support_prod hcd).1).symm
  have hij : i = j := LambdaVertex.proxy.inj (hi.trans hj.symm)
  subst j
  have hheads : LambdaVertex.edge e.1 e.2 = (LambdaVertex.edge f.1 f.2 : L.LV) :=
    (Alternating.FinitePath.edgeSet_biUnique p).2 hab hcd
  have hargs := LambdaVertex.edge.inj hheads
  exact Prod.ext hargs.1 hargs.2

/-- Every exceptional reference-forward connector is also present among
the raw backward gadgets. -/
theorem HasBoundaryIncidence.selected_reference_subset_represented
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) :
    L.selectedConnectorEdges p ∩ L.familyEdges ⊆ L.representedEdges p := by
  intro e he
  obtain ⟨_i, _hi, _hedge, _hattach, hrepresented⟩ :=
    hL.connector_reference_at_start p hs
      (L.selectedConnectorEdges_subset_connectorEdges p he.1) he.2
  exact hrepresented

end PopularAuxiliary.Input
end Erdos599

#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.forward_reference_classification
#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.selected_reference_subsingleton
#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.selected_reference_subset_represented
