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

import ErdosProblems.Erdos735.CyclicSkeleton
import ErdosProblems.Erdos735.SignVectorIncidence

/-!
# From cyclic line orders to sign-vector edge endpoints

This file isolates the exact geometric bridge still required between the
strict sign-vector edges of a central arrangement and the cyclic successor
edges on its projective lines.  Given that equivalence, all endpoint and
vertex-degree fields of `SignVector.BoundaryExtraction` are consequences of
the generic cyclic-order lemmas in `CyclicSkeleton`.
-/

open Classical
noncomputable section

namespace Erdos735.SignVector

open ChartOrder

universe u v

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : Type v} [Fintype V] [DecidableEq V]

/-- The geometric certificate that strict sign-vector edges are precisely
the cyclic successor intervals on the labeled projective lines. -/
structure CyclicEdgeRealization
    (n : I → Vec3) (onLine : V → I → Prop) [DecidableRel onLine] where
  vertices : Finset V
  coord : V → ℝ
  all_vertices : vertices = Finset.univ
  coord_injective : Set.InjOn coord (vertices : Set V)
  two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card
  edgeEquiv : StrictEdge n ≃ CyclicSkeletonEdge vertices onLine
  multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v

namespace CyclicEdgeRealization

variable {n : I → Vec3} {onLine : V → I → Prop} [DecidableRel onLine]
variable (X : CyclicEdgeRealization n onLine)

/-- The two projective vertices bounding a strict sign-vector edge. -/
def edgeVertices (e : StrictEdge n) : Finset V :=
  cyclicEdgeVertices X.vertices onLine X.coord (X.edgeEquiv e)

/-- The strict sign-vector edges incident with a projective vertex. -/
def vertexEdges (v : V) : Finset (StrictEdge n) :=
  Finset.univ.filter fun e => v ∈ X.edgeVertices e

theorem vertexEdge_iff (v : V) (e : StrictEdge n) :
    e ∈ X.vertexEdges v ↔ v ∈ X.edgeVertices e := by
  simp [vertexEdges]

theorem edgeVertices_card (e : StrictEdge n) :
    (X.edgeVertices e).card = 2 := by
  exact cyclicEdgeVertices_card X.vertices onLine X.coord X.coord_injective
    X.two_vertices_on_line (X.edgeEquiv e)

/-- Transporting an edge through `edgeEquiv` preserves incidence with a
vertex by definition.  Hence the transported vertex-edge finset has the same
cardinality as the cyclic skeleton's vertex-edge finset. -/
theorem vertexEdges_card_eq_cyclic (v : V) :
    (X.vertexEdges v).card =
      (cyclicVertexEdges X.vertices onLine X.coord v).card := by
  classical
  apply Finset.card_bij (fun e _ => X.edgeEquiv e)
  · intro e he
    rw [mem_cyclicVertexEdges_iff]
    exact (X.vertexEdge_iff v e).mp he
  · intro e he f hf hef
    exact X.edgeEquiv.injective hef
  · intro e he
    refine ⟨X.edgeEquiv.symm e, ?_, X.edgeEquiv.apply_symm_apply e⟩
    apply (X.vertexEdge_iff v (X.edgeEquiv.symm e)).mpr
    change v ∈ cyclicEdgeVertices X.vertices onLine X.coord
      (X.edgeEquiv (X.edgeEquiv.symm e))
    rw [X.edgeEquiv.apply_symm_apply]
    exact (mem_cyclicVertexEdges_iff X.vertices onLine X.coord v e).mp he

theorem vertexEdges_card (v : V) :
    (X.vertexEdges v).card = 2 * lineMultiplicity onLine v := by
  rw [X.vertexEdges_card_eq_cyclic v]
  apply cyclicVertexEdges_card X.vertices onLine X.coord X.coord_injective
    X.two_vertices_on_line v
  rw [X.all_vertices]
  exact Finset.mem_univ v

/-- Adding only genuine cyclic face-boundary lists and Euler's identity to a
cyclic edge realization supplies all of `BoundaryExtraction`.  In particular,
the endpoint and degree fields are not extra assumptions. -/
structure CyclicBoundaryRealization
    (n : I → Vec3) (onLine : V → I → Prop) [DecidableRel onLine]
    extends CyclicEdgeRealization n onLine where
  faceBoundary : StrictFace n → List (StrictEdge n)
  faceBoundary_nodup : ∀ f, (faceBoundary f).Nodup
  faceBoundary_toFinset : ∀ f, (faceBoundary f).toFinset = faceEdges n f
  faceDegree_three_le : ∀ f, 3 ≤ (faceBoundary f).length
  euler_sphere :
    (Fintype.card V : ℤ) - (Fintype.card (StrictEdge n) : ℤ) +
      (Fintype.card (StrictFace n) : ℤ) = 2

namespace CyclicBoundaryRealization

variable {hn : ∀ i, n i ≠ 0}
variable (X : CyclicBoundaryRealization n onLine)

/-- The checked constructor which fills every endpoint/degree field from the
cyclic skeleton and leaves only the explicitly supplied facial cycles. -/
def toBoundaryExtraction : BoundaryExtraction n hn where
  Vertex := V
  instFintypeVertex := inferInstance
  instDecidableEqVertex := inferInstance
  blueMultiplicity := lineMultiplicity onLine
  edgeVertices := X.toCyclicEdgeRealization.edgeVertices
  vertexEdges := X.toCyclicEdgeRealization.vertexEdges
  vertexEdge_iff := X.toCyclicEdgeRealization.vertexEdge_iff
  edgeVertices_card := X.toCyclicEdgeRealization.edgeVertices_card
  vertexEdges_card := X.toCyclicEdgeRealization.vertexEdges_card
  blueMultiplicity_two_le := X.multiplicity_two_le
  faceBoundary := X.faceBoundary
  faceBoundary_nodup := X.faceBoundary_nodup
  faceBoundary_toFinset := X.faceBoundary_toFinset
  faceDegree_three_le := X.faceDegree_three_le
  euler_sphere := X.euler_sphere

/-- The resulting sign-vector cellulation, with its endpoint fields obtained
from cyclic successors and its two-face incidence obtained algebraically from
strict sign vectors. -/
def toBlueCellulation :
    BlueCellulation V (StrictEdge n) (StrictFace n) :=
  (X.toBoundaryExtraction (hn := hn)).toBlueCellulation n hn

end CyclicBoundaryRealization
end CyclicEdgeRealization
end Erdos735.SignVector
