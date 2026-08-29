/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerCutRecords

/-!
# The actual residual graph after cutting reference edges

Only reference edges represented in the cut are removed from the matching;
off-reference identities remain matched. Both ports of an off-reference
cut vertex are deleted. Cut marker ports and cut-edge heads remain as dead
ends, while cut-edge tails remain free sending ports. Destinations are
exactly the receiving ports of markers outside the cut.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def cutOffVertices (C : Set L.Vertex) : Set V :=
  {x | ∃ hx : x ∉ G.vertexSet L.reference.paths, Vertex.off ⟨x, hx⟩ ∈ C}

def residualMatching (C : Set L.Vertex) (x y : V) : Prop :=
  ((x, y) ∈ familyEdges L.reference.paths ∧ (x, y) ∉ L.cutEdges C) ∨
    (x = y ∧ x ∉ G.vertexSet L.reference.paths)

def portAvailable (C : Set L.Vertex) : Port V → Prop
  | .inl x => x ∉ L.cutOffVertices C
  | .inr x => x ∉ L.cutOffVertices C

def residualStep (C : Set L.Vertex) : Port V → Port V → Prop
  | .inl x, .inr y =>
      x ∉ L.cutOffVertices C ∧ y ∉ L.cutOffVertices C ∧
        (G.graph.Adj x y ∨ x = y) ∧ ¬ L.residualMatching C x y
  | .inr y, .inl x =>
      y ∉ L.cutOffVertices C ∧ x ∉ L.cutOffVertices C ∧ L.residualMatching C x y
  | _, _ => False

def residualGraph (C : Set L.Vertex) : Digraph (Port V) where
  Adj := L.residualStep C

/-- Escape uses a finite walk; loop erasure gives an equivalent finite
simple path with the same endpoints. -/
def Escapes (C : Set L.Vertex) (p : Port V) : Prop :=
  ∃ y : L.markers, Vertex.marker y ∉ C ∧
    Nonempty (Walk (L.residualGraph C) p (.inr y.1))

def escapeRegion (C : Set L.Vertex) : Set V :=
  {x | L.Escapes C (.inl x)}

theorem residualMatching_subset_reference (C : Set L.Vertex) {x y : V}
    (h : L.residualMatching C x y) : referenceMatching L.reference.paths x y :=
  h.imp And.left id

theorem not_mem_cutOff_of_mem_reference (C : Set L.Vertex) {x : V}
    (hx : x ∈ G.vertexSet L.reference.paths) : x ∉ L.cutOffVertices C := by
  rintro ⟨hoff, _⟩
  exact hoff hx

theorem residualMatching_not_of_cutEdge (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ L.cutEdges C) : ¬ L.residualMatching C x y := by
  rintro (⟨_, hnot⟩ | ⟨_, hoff⟩)
  · exact hnot he
  · exact hoff (familyEdges_subset_vertexSet_prod L.reference.paths
      (L.cutEdges_subset_reference C he)).1

theorem residualMatching_noOutgoing_cutTail (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ L.cutEdges C) (z : V) : ¬ L.residualMatching C x z := by
  intro hz
  have hzy : z = y := (referenceMatching_biUnique L.reference.disjoint).2
    (L.residualMatching_subset_reference C hz) (Or.inl (L.cutEdges_subset_reference C he))
  exact L.residualMatching_not_of_cutEdge C he (hzy ▸ hz)

theorem residualMatching_noIncoming_cutHead (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ L.cutEdges C) (z : V) : ¬ L.residualMatching C z y := by
  intro hz
  have hzx : z = x := (referenceMatching_biUnique L.reference.disjoint).1
    (L.residualMatching_subset_reference C hz) (Or.inl (L.cutEdges_subset_reference C he))
  exact L.residualMatching_not_of_cutEdge C he (hzx ▸ hz)

/-- A removed reference edge leaves a receiving head with no outgoing
residual step, including any attempted off-reference identity step. -/
theorem no_residualStep_from_cutHead (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ L.cutEdges C) (p : Port V) :
    ¬ L.residualStep C (.inr y) p := by
  cases p with
  | inl z => exact fun h ↦ L.residualMatching_noIncoming_cutHead C he z h.2.2
  | inr z => exact id

/-- Its sending tail cannot be entered by a residual step. -/
theorem no_residualStep_to_cutTail (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ L.cutEdges C) (p : Port V) :
    ¬ L.residualStep C p (.inl x) := by
  cases p with
  | inl z => exact id
  | inr z => exact fun h ↦ L.residualMatching_noOutgoing_cutTail C he z h.2.2

theorem no_residualStep_from_marker (C : Set L.Vertex)
    (y : L.markers) (p : Port V) : ¬ L.residualStep C (.inr y.1) p := by
  cases p with
  | inl x =>
      intro h
      exact L.marker_receiving_unmatched y x (L.residualMatching_subset_reference C h.2.2)
  | inr x => exact id

/-- A retained residual matching edge has a concrete, uncut contracted
vertex representing both ports. Off-reference availability is used only
in the identity case. -/
theorem exists_uncut_matchingVertex (C : Set L.Vertex) {x y : V}
    (hxy : L.residualMatching C x y) (hx : x ∉ L.cutOffVertices C) :
    ∃ a : L.Vertex, L.sending a = some x ∧ L.receiving a = some y ∧ a ∉ C := by
  rcases hxy with ⟨he, heNotCut⟩ | ⟨rfl, hoff⟩
  · refine ⟨.edge ⟨(x, y), he⟩, rfl, rfl, ?_⟩
    intro hC
    exact heNotCut ⟨he, hC⟩
  · refine ⟨.off ⟨x, hoff⟩, rfl, rfl, ?_⟩
    intro hC
    exact hx ⟨hoff, hC⟩

/-- A reference matching edge into an uncut represented receiving port
has not been removed. This rules out a spurious new forward crossing of a
deleted matching edge in a successful residual escape. -/
theorem referenceMatching_residual_of_receiver_uncut
    (C : Set L.Vertex) {a : L.Vertex} {x y : V}
    (ha : L.receiving a = some y) (haC : a ∉ C)
    (hxy : referenceMatching L.reference.paths x y) :
    L.residualMatching C x y := by
  rcases hxy with he | hoff
  · refine Or.inl ⟨he, ?_⟩
    rintro ⟨he', heC⟩
    have howner : (Vertex.edge ⟨(x, y), he'⟩ : L.Vertex) = a :=
      L.receiving_unique rfl ha
    exact haC (howner ▸ heC)
  · exact Or.inr hoff

#print axioms no_residualStep_from_cutHead
#print axioms no_residualStep_to_cutTail
#print axioms exists_uncut_matchingVertex
#print axioms referenceMatching_residual_of_receiver_uncut

end Erdos599.GroundingAllMarkerAuxiliary.Input
