/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawSignedBalance

/-!
# Exact boundary of the actual finite-source raw switch

All degree and balance hypotheses come from the original auxiliary path.
Repeated physical vertices and all untouched companion reference edges are
retained. This file decodes through the exit of the last gadget; an edge-cut
entry stop is a distinct construction and is not silently identified here.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I}

/-- The raw backward relation inherits biuniqueness from the reference. -/
theorem representedEdges_biUnique (p : FinitePath L.lambda.graph) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ L.representedEdges p) :=
  ⟨fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.1 h₁.2 h₂.2,
    fun _ _ _ h₁ h₂ ↦ L.raw_familyEdges_biUnique.2 h₁.2 h₂.2⟩

/-- Exact signed endpoint balance for an actual raw finite-source path. -/
theorem HasBoundaryIncidence.raw_direction_balance_of_start_old
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {s t : V}
    (hstart : p.start = .old s) (hexit : L.gadgetExit p.finish = some t) (x : V) :
    edgeBalance (L.properSelectedConnectorEdges p) x -
      edgeBalance (L.representedEdges p) x = propInt (x = s) - propInt (x = t) := by
  have hproxy := no_proxy_of_start_old p hs hstart
  have hF : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .forward (L.decodeProperSteps p)) := by
    rw [decodeProperSteps_forwardEdges]
    exact ⟨hL.properSelectedConnectorEdges_leftUnique p,
      hL.properSelectedConnectorEdges_rightUnique_of_no_proxy p hproxy⟩
  have hB : Relator.BiUnique
      (fun a b ↦ (a, b) ∈ directedSignedEdgeSet .backward (L.decodeProperSteps p)) := by
    rw [decodeProperSteps_backwardEdges p hs]
    exact representedEdges_biUnique p
  have hentry : L.gadgetEntry p.start = some s := by rw [hstart]; rfl
  have hrun : RunsFromTo s t (L.decodeProperSteps p) :=
    (L.decodeWalkSteps_runs_from_entry p.walk hentry hexit).filter_selfLoops
  have hbal := hrun.edgeBalance_forward_sub_backward
    (hL.decodeProperSteps_nodup p) hF hB x
  simpa only [decodeProperSteps_forwardEdges, decodeProperSteps_backwardEdges p hs] using hbal

/-- Inserted proper forward edges are disjoint from the retained raw
reference, because every incoming reference conflict is already removed. -/
theorem HasBoundaryIncidence.raw_retained_disjoint_forward
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph) :
    Disjoint (L.familyEdges \ L.representedEdges p) (L.properSelectedConnectorEdges p) := by
  apply Set.disjoint_left.2
  intro e he hforward
  exact he.2 (hL.incoming_reference_represented p hforward he.1)

/-- The entire raw switched relation has the exact expected endpoint
balance. No additional conflict deletion or balance premise is supplied. -/
theorem HasBoundaryIncidence.rawSwitchedEdges_balance_of_start_old
    (hL : L.HasBoundaryIncidence) (p : FinitePath L.lambda.graph)
    (hs : p.start ∈ L.lambda.source) {s t : V}
    (hstart : p.start = .old s) (hexit : L.gadgetExit p.finish = some t) (x : V) :
    edgeBalance (L.rawSwitchedEdges p) x = edgeBalance L.familyEdges x +
      propInt (x = s) - propInt (x = t) := by
  have hswitch := hL.rawSwitchedEdges_biUnique_of_start_old p hs hstart
  have hcalc := edgeBalance_sdiff_union_eq_add_sub
    (L.representedEdges_subset_familyEdges p)
    L.raw_familyEdges_biUnique.2 L.raw_familyEdges_biUnique.1
    hswitch.2 hswitch.1 (hL.raw_retained_disjoint_forward p) x
  have hdelta := hL.raw_direction_balance_of_start_old p hs hstart hexit x
  change edgeBalance ((L.familyEdges \ L.representedEdges p) ∪
    L.properSelectedConnectorEdges p) x = _
  omega

end PopularAuxiliary.Input
end Erdos599

#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.raw_direction_balance_of_start_old
#print axioms
  Erdos599.PopularAuxiliary.Input.HasBoundaryIncidence.rawSwitchedEdges_balance_of_start_old
