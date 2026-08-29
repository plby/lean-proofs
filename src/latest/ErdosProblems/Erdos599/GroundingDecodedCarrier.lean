/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# Original-vertex carriers of auxiliary grounding routes

This small definition layer is deliberately placed before the active-control
recursion.  Activity has to distinguish a component which was merely exposed
somewhere from a vertex which lies weakly after an actual decoded contact.
The latter is the source-faithful absorption condition in Assertion 8.22.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

/-- The original vertices represented by one auxiliary gadget.  A proxy
represents the full support of its recorded limiting-ladder path. -/
def gadgetCarrier : L.LV → Set V
  | .old x => {x}
  | .edge x y => {x, y}
  | .proxy i => (L.proxyPath i).support

@[simp] theorem gadgetCarrier_old (x : V) :
    L.gadgetCarrier (.old x) = {x} := rfl

@[simp] theorem gadgetCarrier_edge (x y : V) :
    L.gadgetCarrier (.edge x y) = {x, y} := rfl

@[simp] theorem gadgetCarrier_proxy (i : I) :
    L.gadgetCarrier (.proxy i) = (L.proxyPath i).support := rfl

/-- The total original-vertex carrier represented by the gadgets in an
auxiliary finite path. -/
def decodedVertexCarrier (p : FinitePath L.lambda.graph) : Set V :=
  ⋃ a ∈ (p.support : Set L.LV), L.gadgetCarrier a

/-- The exact original vertices incident with a decoded edge of an auxiliary
path.  Unlike `decodedVertexCarrier`, this does not treat every vertex of a
starting proxy component as a route contact: only endpoints of edges which
the deterministic decoder actually uses are retained. -/
def decodedRouteIncidentCarrier (p : FinitePath L.lambda.graph) : Set V :=
  {x | (∃ e ∈ L.decodedRouteEdges p, x = e.1 ∨ x = e.2) ∨
    ∃ a ∈ p.support, L.gadgetEntry a = some x}

theorem mem_decodedRouteIncidentCarrier_iff
    (p : FinitePath L.lambda.graph) (x : V) :
    x ∈ L.decodedRouteIncidentCarrier p ↔
      (∃ e ∈ L.decodedRouteEdges p, x = e.1 ∨ x = e.2) ∨
        ∃ a ∈ p.support, L.gadgetEntry a = some x :=
  Iff.rfl

/-- Both endpoints of a genuinely decoded edge belong to the exact incident
carrier. -/
theorem decodedRouteEdge_endpoints_mem_decodedRouteIncidentCarrier
    (p : FinitePath L.lambda.graph) {e : V × V}
    (he : e ∈ L.decodedRouteEdges p) :
    e.1 ∈ L.decodedRouteIncidentCarrier p ∧
      e.2 ∈ L.decodedRouteIncidentCarrier p := by
  exact ⟨Or.inl ⟨e, he, Or.inl rfl⟩,
    Or.inl ⟨e, he, Or.inr rfl⟩⟩

end PopularAuxiliary.Input
end Erdos599
