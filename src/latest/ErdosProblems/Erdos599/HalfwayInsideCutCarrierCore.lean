/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutConstruction

/-!
# Focused inside-cut carrier geometry

This is the dependency-minimal carrier portion of the canonical inside cut.
It deliberately avoids the obsolete aggregate stage-geometry import.  The
carrier retains the vertices swallowed by the cut and the uncovered roots
and sinks of the complementary outside relation, including isolated
attachment vertices.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Alternating.RelationDecomposition

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace FocusedInsideCut

/-- Honest later-row edges whose two endpoints were swallowed by the cut. -/
def edge (W : Set Gamma.DPath) (X : Set V) : Set (V × V) :=
  familyEdges W ∩ (X ×ˢ X)

/-- Exact inside carrier, including uncovered outside roots and sinks even
when they are isolated after edge restriction. -/
def carrier (Y W : Set Gamma.DPath) (X : Set V) : Set V :=
  (Gamma.vertexSet W ∩ X) ∪
    (CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \ Gamma.initialSet Y) ∪
    (CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \ Gamma.vertexSet Y)

theorem outsideCarrier_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    outsideCarrier W X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · exact hx.1
  · obtain ⟨y, hxy | hyx⟩ := hx
    · exact (familyEdges_subset_vertexSet_prod W
        (outsideFamilyEdges_subset W X hxy)).1
    · exact (familyEdges_subset_vertexSet_prod W
        (outsideFamilyEdges_subset W X hyx)).2

theorem cutInitial_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨_hxX, y, hxy⟩ := hx
    exact (familyEdges_subset_vertexSet_prod W
      (outsideFamilyEdges_subset W X hxy)).1
  · exact outsideCarrier_subset_vertexSet W X hx.1

theorem cutTerminal_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨_hxX, y, hyx⟩ := hx
    exact (familyEdges_subset_vertexSet_prod W
      (outsideFamilyEdges_subset W X hyx)).2
  · exact outsideCarrier_subset_vertexSet W X hx.1

theorem carrier_subset_vertexSet (Y W : Set Gamma.DPath) (X : Set V) :
    carrier Y W X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact hx.1
  · exact cutInitial_subset_vertexSet W X hx.1
  · exact cutTerminal_subset_vertexSet W X hx.1

theorem edge_endpoints (W : Set Gamma.DPath) (X : Set V)
    {e : V × V} (he : e ∈ edge W X) :
    e.1 ∈ carrier Y W X ∧ e.2 ∈ carrier Y W X := by
  exact ⟨Or.inl (Or.inl
      ⟨(familyEdges_subset_vertexSet_prod W he.1).1, he.2.1⟩),
    Or.inl (Or.inl
      ⟨(familyEdges_subset_vertexSet_prod W he.1).2, he.2.2⟩)⟩

theorem edge_in_graph (W : Set Gamma.DPath) (X : Set V) :
    edge W X ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  exact familyEdges_subset_adj W he.1

/-- Exact blueprint realization of the focused inside relation and carrier. -/
structure Geometry (W : Set Gamma.DPath) (X : Set V) where
  blueprint : LinkageBlueprint Gamma Y kappa
  edgeSet_eq : blueprint.edgeSet = edge W X
  vertexSet_eq : blueprint.vertexSet = carrier Y W X

/-- The focused inside geometry follows just from the honest later-row warp. -/
theorem exists_geometry (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) :
    Nonempty (Geometry (Y := Y) (kappa := kappa) W X) := by
  let E : Set (V × V) := edge W X
  let K : Set V := carrier Y W X
  have hgraph : E ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
    intro e he
    exact original_adj_imaginaryGraph (edge_in_graph W X he)
  have hendpoints : ∀ e ∈ E, e.1 ∈ K ∧ e.2 ∈ K := by
    intro e he
    exact edge_endpoints W X he
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨D, hD⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      hW ⟨D, hD.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hW ⟨R, fun n ↦ (hR n).1⟩
  obtain ⟨O, hOE, hOK⟩ := exists_forwardOrientation_exact
    E K hgraph hendpoints hunique hcycle hreverse
  exact ⟨{
    blueprint := orientationBlueprint O
    edgeSet_eq := by rw [orientationBlueprint_edgeSet, hOE]
    vertexSet_eq := by rw [orientationBlueprint_vertexSet, hOK] }⟩

#print axioms exists_geometry

end FocusedInsideCut
end Erdos599.Blueprint.LinkageBlueprint
