/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingTraversal
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# Boundary alignment closes the missing matching contacts

The bipartite symmetric-difference traversal marks every reference contact
which is incident with a reference-only matching edge.  There are only two
ways in which a vertex on the reference warp can fail to have such an
incident edge at the endpoint of a forward-only edge: the forward source is
a reference terminal, or the forward target is a reference initial.

Consequently the ordinary boundary inclusions
`initialSet Y ⊆ initialSet W` and
`terminalFrontier Y ⊆ terminalFrontier W` rule out exactly the two
wrong-parity contacts.  This is the literal matching-level contact theorem;
it precedes identity contraction or path projection.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath Alternating Blueprint.LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The source-contact statement with the exact endpoint exclusion exposed.
This is the form used when boundary geometry rules out the bad endpoint for
one concrete ambient edge without proving a global frontier inclusion. -/
theorem exclusive_reference_outgoing_of_source_mem_of_not_terminal
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxY : x ∈ Gamma.vertexSet Y)
    (hxNotTerminalY : x ∉ Gamma.terminalFrontier Y) :
    ∃ z, (x, z) ∈ familyEdges Y ∧ Exclusive Y W x z := by
  have hxOutgoing : ∃ z, (x, z) ∈ familyEdges Y := by
    by_contra hno
    apply hxNotTerminalY
    rw [isWarp_terminalFrontier_eq_noOutgoing hY]
    exact ⟨hxY, hno⟩
  obtain ⟨z, hxzY⟩ := hxOutgoing
  refine ⟨z, hxzY, matchingEdge_actual hxzY, ?_⟩
  intro hxzW
  have hyz : y = z :=
    (matchingEdge_biUnique hW).2 hxy.1 hxzW
  subst z
  exact hxy.2 (matchingEdge_actual hxzY)

/-- The target-contact statement with the exact endpoint exclusion exposed. -/
theorem exclusive_reference_incoming_of_target_mem_of_not_initial
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : Exclusive W Y x y)
    (hyY : y ∈ Gamma.vertexSet Y)
    (hyNotInitialY : y ∉ Gamma.initialSet Y) :
    ∃ z, (z, y) ∈ familyEdges Y ∧ Exclusive Y W z y := by
  have hyIncoming : ∃ z, (z, y) ∈ familyEdges Y := by
    by_contra hno
    apply hyNotInitialY
    rw [isWarp_initialSet_eq_noIncoming hY]
    exact ⟨hyY, hno⟩
  obtain ⟨z, hzyY⟩ := hyIncoming
  refine ⟨z, hzyY, matchingEdge_actual hzyY, ?_⟩
  intro hzyW
  have hxz : x = z :=
    (matchingEdge_biUnique hW).1 hxy.1 hzyW
  subst z
  exact hxy.2 (matchingEdge_actual hzyY)

/-- A forward-only matching edge exposes a reference-only matching edge at
its source whenever that source belongs to the reference warp and reference
terminals are also terminals of the forward warp. -/
theorem exclusive_reference_outgoing_of_source_mem
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hterminal : Gamma.terminalFrontier Y ⊆ Gamma.terminalFrontier W)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxyW : (x, y) ∈ familyEdges W)
    (hxY : x ∈ Gamma.vertexSet Y) :
    ∃ z, Exclusive Y W x z := by
  have hxNotTerminalW : x ∉ Gamma.terminalFrontier W := by
    intro hxTerminal
    exact (isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier hW
      hxTerminal) ⟨y, hxyW⟩
  have hxNotTerminalY : x ∉ Gamma.terminalFrontier Y :=
    fun hx ↦ hxNotTerminalW (hterminal hx)
  obtain ⟨z, _hzY, hz⟩ :=
    exclusive_reference_outgoing_of_source_mem_of_not_terminal
      hW hY hxy hxY hxNotTerminalY
  exact ⟨z, hz⟩

/-- Dually, a forward-only matching edge exposes a reference-only matching
edge at its target whenever that target belongs to the reference warp and
reference initials are also initials of the forward warp. -/
theorem exclusive_reference_incoming_of_target_mem
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxyW : (x, y) ∈ familyEdges W)
    (hyY : y ∈ Gamma.vertexSet Y) :
    ∃ z, Exclusive Y W z y := by
  have hyNotInitialW : y ∉ Gamma.initialSet W := by
    intro hyInitial
    exact (isWarp_noIncoming_familyEdges_of_mem_initialSet hW hyInitial)
      ⟨x, hxyW⟩
  have hyNotInitialY : y ∉ Gamma.initialSet Y :=
    fun hy ↦ hyNotInitialW (hinitial hy)
  obtain ⟨z, _hzY, hz⟩ :=
    exclusive_reference_incoming_of_target_mem_of_not_initial
      hW hY hxy hyY hyNotInitialY
  exact ⟨z, hz⟩

/-- Exact endpoint exclusions expose literal reference edges together with
their exclusive matching certificates. -/
theorem actualExclusive_forward_contacts_of_endpoint_exclusion
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxNotTerminalY : x ∉ Gamma.terminalFrontier Y)
    (hyNotInitialY : y ∉ Gamma.initialSet Y) :
    (x ∈ Gamma.vertexSet Y →
      ∃ z, (x, z) ∈ familyEdges Y ∧ Exclusive Y W x z) ∧
      (y ∈ Gamma.vertexSet Y →
        ∃ z, (z, y) ∈ familyEdges Y ∧ Exclusive Y W z y) := by
  exact ⟨fun hx ↦
    exclusive_reference_outgoing_of_source_mem_of_not_terminal
      hW hY hxy hx hxNotTerminalY,
    fun hy ↦
      exclusive_reference_incoming_of_target_mem_of_not_initial
        hW hY hxy hy hyNotInitialY⟩

/-- Exact per-edge wrong-parity exclusions are enough to mark every
reference contact at a literal forward-only matching edge. -/
theorem exclusive_forward_contacts_of_endpoint_exclusion
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxNotTerminalY : x ∉ Gamma.terminalFrontier Y)
    (hyNotInitialY : y ∉ Gamma.initialSet Y) :
    (x ∈ Gamma.vertexSet Y → ∃ z, Exclusive Y W x z) ∧
      (y ∈ Gamma.vertexSet Y → ∃ z, Exclusive Y W z y) := by
  exact ⟨fun hx ↦
    let ⟨z, _hzY, hz⟩ :=
      exclusive_reference_outgoing_of_source_mem_of_not_terminal
        hW hY hxy hx hxNotTerminalY
    ⟨z, hz⟩,
    fun hy ↦
      let ⟨z, _hzY, hz⟩ :=
        exclusive_reference_incoming_of_target_mem_of_not_initial
          hW hY hxy hy hyNotInitialY
      ⟨z, hz⟩⟩

/-- Both endpoint-contact alternatives for a literal forward-only matching
edge.  These are precisely the antecedents consumed by
`FiniteTraversal.forward_contact_covered` and its infinite analogue. -/
theorem exclusive_forward_contacts_of_boundary
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier Y ⊆ Gamma.terminalFrontier W)
    {x y : V} (hxy : Exclusive W Y x y)
    (hxyW : (x, y) ∈ familyEdges W) :
    (x ∈ Gamma.vertexSet Y → ∃ z, Exclusive Y W x z) ∧
      (y ∈ Gamma.vertexSet Y → ∃ z, Exclusive Y W z y) := by
  exact ⟨fun hx ↦
    exclusive_reference_outgoing_of_source_mem hW hY hterminal hxy hxyW hx,
    fun hy ↦
      exclusive_reference_incoming_of_target_mem hW hY hinitial hxy hxyW hy⟩

#print axioms exclusive_reference_outgoing_of_source_mem
#print axioms exclusive_reference_incoming_of_target_mem
#print axioms actualExclusive_forward_contacts_of_endpoint_exclusion
#print axioms exclusive_forward_contacts_of_endpoint_exclusion
#print axioms exclusive_forward_contacts_of_boundary

end TwoWarpMatchingTraversal
end Erdos599
