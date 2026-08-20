/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ConcretePolarVertexDegree
import ErdosProblems.Erdos735.ProjectiveConcreteExtraction

/-!
# Concrete polar cellulation

This module packages the literal oriented polar endpoints and genuine polar
face cycles into `SignVector.BoundaryExtraction`.  All topology, Euler, and
face-degree fields have already been proved.  The constructor isolates the
single remaining one-skeleton statement: the number of literal strict edges
at an oriented projective vertex is twice its projective line multiplicity.
-/

open Classical
noncomputable section

namespace Erdos735.ConcretePolarCellulation

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross SignVector.PolarFace
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B
abbrev Vertex (B : Finset Point) := ConcretePolarOrientedVertex.OrientedVertex B

/-- The literal polar cellulation, conditional only on its local vertex
degree identity. -/
noncomputable def boundaryExtractionOfVertexDegree
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (vertex_degree :
      letI : Nonempty (Line B) := ⟨⟨a, ha⟩⟩
      let hspan := span_normalVec_range_eq_top_of_noncollinear_triple
        B ha hb hc hncol
      ∀ v : Vertex B,
        (concreteVertexEdges hspan v).card =
          2 * lineMultiplicity (OnLine B) v.1) :
    BoundaryExtraction (normals B) (normals_ne_zero B) := by
  letI : Nonempty (Line B) := ⟨⟨a, ha⟩⟩
  let hspan := span_normalVec_range_eq_top_of_noncollinear_triple
    B ha hb hc hncol
  let counted := ProjectiveBoundaryExtraction.concreteBoundaryExtraction
    B ha hb hc hncol
  exact
    { Vertex := Vertex B
      instFintypeVertex := inferInstance
      instDecidableEqVertex := inferInstance
      blueMultiplicity := fun v ↦ lineMultiplicity (OnLine B) v.1
      edgeVertices := concreteEdgeVertices hspan
      vertexEdges := concreteVertexEdges hspan
      vertexEdge_iff := fun v e ↦ mem_concreteVertexEdges_iff hspan v e
      edgeVertices_card := concreteEdgeVertices_card hspan
      vertexEdges_card := vertex_degree
      blueMultiplicity_two_le := fun v ↦ two_le_lineMultiplicity B v.1
      faceBoundary := faceBoundary (normals B) normal_cross hspan
      faceBoundary_nodup := faceBoundary_nodup (normals B) normal_cross hspan
      faceBoundary_toFinset := faceBoundary_toFinset (normals B) normal_cross hspan
      faceDegree_three_le := by
        intro f
        rw [← List.toFinset_card_of_nodup
          (faceBoundary_nodup (normals B) normal_cross hspan f),
          faceBoundary_toFinset (normals B) normal_cross hspan f]
        exact faceEdges_card_three_le_of_span_eq_top
          (normals B) normal_cross hspan f
      euler_sphere := by
        exact counted.euler_sphere }

/-- The corresponding blue cellulation used by the discharging modules. -/
noncomputable def blueCellulationOfVertexDegree
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (vertex_degree :
      letI : Nonempty (Line B) := ⟨⟨a, ha⟩⟩
      let hspan := span_normalVec_range_eq_top_of_noncollinear_triple
        B ha hb hc hncol
      ∀ v : Vertex B,
        (concreteVertexEdges hspan v).card =
          2 * lineMultiplicity (OnLine B) v.1) :
    BlueCellulation (Vertex B) (StrictEdge (normals B))
      (StrictFace (normals B)) :=
  (boundaryExtractionOfVertexDegree B ha hb hc hncol vertex_degree).toBlueCellulation
    (normals B) (normals_ne_zero B)

/-- The unconditional literal polar boundary extraction.  Its vertices are
the globally chart-oriented projective intersections, its strict-edge
endpoints are the actual consecutive polar corners, and its face lists are
the genuine cyclic polar boundaries. -/
noncomputable def boundaryExtraction
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    BoundaryExtraction (normals B) (normals_ne_zero B) :=
  boundaryExtractionOfVertexDegree B ha hb hc hncol
    (ConcretePolarVertexDegree.concreteVertexEdges_card_eq B ha hb hc hncol)

/-- The fully concrete blue cellulation of a noncollinear finite projective
line arrangement. -/
noncomputable def blueCellulation
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    BlueCellulation (Vertex B) (StrictEdge (normals B))
      (StrictFace (normals B)) :=
  blueCellulationOfVertexDegree B ha hb hc hncol
    (ConcretePolarVertexDegree.concreteVertexEdges_card_eq B ha hb hc hncol)

end Erdos735.ConcretePolarCellulation
