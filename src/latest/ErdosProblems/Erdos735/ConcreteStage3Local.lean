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

import ErdosProblems.Erdos735.Stage3LocalObstruction
import ErdosProblems.Erdos735.ConcretePolarEndpointRestriction
import ErdosProblems.Erdos735.BlueDirectionProjective

/-!
# Concrete local Stage-3 reductions

This file specializes the local bad-neighbour and obstruction interfaces to
the literal polar cellulation.  It also gives the recognition theorem in the
most useful edge-local form: a bad neighbouring quadrangle supplies the two
distinct double vertices automatically, so only the three-vertices-on-owner
cardinality remains to invoke failed-Fano recognition.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage3Local

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open ConcretePolarABKPRData ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev hs : Submodule.span ℝ (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev vd := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

/-- A bad face across a concrete polar boundary edge makes the start
projective endpoint a double blue vertex. -/
theorem badNeighbor_start_lineMultiplicity_eq_two
    (f : StrictFace (normals (B (P := P))))
    (i : Fin ((C (P := P) ha hb hd hncol).faceDegree f))
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle
      ((D hred ha hb hd hncol).across ⟨f, i⟩).1) :
    lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex f i).1 = 2 := by
  have h := (D hred ha hb hd hncol).badNeighbor_start_multiplicity_two f i hbad
  simpa [D, ConcretePolarABKPRData.concreteData,
    ConcretePolarABKPRData.toData, C,
    ConcretePolarCellulation.blueCellulation,
    ConcretePolarCellulation.blueCellulationOfVertexDegree,
    ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
    BoundaryExtraction.toBlueCellulation] using h

/-- The finish endpoint of the same edge is also double. -/
theorem badNeighbor_finish_lineMultiplicity_eq_two
    (f : StrictFace (normals (B (P := P))))
    (i : Fin ((C (P := P) ha hb hd hncol).faceDegree f))
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle
      ((D hred ha hb hd hncol).across ⟨f, i⟩).1) :
    lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex f
        (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i)).1 = 2 := by
  have h := (D hred ha hb hd hncol).badNeighbor_finish_multiplicity_two f i hbad
  simpa [D, ConcretePolarABKPRData.concreteData,
    ConcretePolarABKPRData.toData, C,
    ConcretePolarCellulation.blueCellulation,
    ConcretePolarCellulation.blueCellulationOfVertexDegree,
    ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
    BoundaryExtraction.toBlueCellulation] using h

/-- Two distinct bad-neighbour edges of a concrete polar triangle make all
three projective boundary vertices double. -/
theorem triangle_boundary_lineMultiplicity_eq_two
    (t : StrictFace (normals (B (P := P))))
    (ht : (C (P := P) ha hb hd hncol).faceDegree t = 3)
    (i j : Fin ((C (P := P) ha hb hd hncol).faceDegree t))
    (hij : i ≠ j)
    (hi : i ∈ (D hred ha hb hd hncol).badNeighborIndices t)
    (hj : j ∈ (D hred ha hb hd hncol).badNeighborIndices t)
    (k : Fin ((C (P := P) ha hb hd hncol).faceDegree t)) :
    lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex t k).1 = 2 := by
  have h := (D hred ha hb hd hncol).triangle_all_boundary_multiplicity_two_of_two_bad
    t ht i j hij hi hj k
  simpa [D, ConcretePolarABKPRData.concreteData,
    ConcretePolarABKPRData.toData, C,
    ConcretePolarCellulation.blueCellulation,
    ConcretePolarCellulation.blueCellulationOfVertexDegree,
    ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
    BoundaryExtraction.toBlueCellulation] using h

/-- Concrete specialization of the unconditional donation-edge freeness
lemma. -/
theorem donationEdgeOfGeometry_free
    (f : StrictFace (normals (B (P := P))))
    (t : (D hred ha hb hd hncol).donationRecipients f) :
    (D hred ha hb hd hncol).donationEdgeOfGeometry f t ∈
      (D hred ha hb hd hncol).freeEdgeIndices f := by
  exact (D hred ha hb hd hncol).donationEdgeOfGeometry_free
    (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol) f t

/-- The exact concrete dichotomy before the remaining four local exceptional
patterns are recognized. -/
theorem localObstruction_or_reducedStage3Geometry :
    (D hred ha hb hd hncol).Stage3LocalObstruction ∨
      Nonempty (D hred ha hb hd hncol).ReducedStage3Geometry := by
  exact (D hred ha hb hd hncol).localObstruction_or_reducedStage3Geometry
    (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol)

/-- Final assembly point for the local exceptional analysis: a recognition
proof for each explicit obstruction yields failed Fano or the complete
reduced Stage-3 geometry. -/
theorem failedFano_or_reducedStage3Geometry
    (hrecognize : (D hred ha hb hd hncol).Stage3LocalObstruction →
      IsFailedFano P) :
    IsFailedFano P ∨ Nonempty (D hred ha hb hd hncol).ReducedStage3Geometry := by
  exact (D hred ha hb hd hncol).exceptional_or_reducedStage3Geometry
    (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol) hrecognize

/-- The two oriented endpoints stored on one concrete strict edge have
distinct underlying projective vertices.  Equivalently, projection to the
projective arrangement vertex is injective on that two-element finset. -/
private theorem concreteEdgeVertices_projective_injective
    (e : StrictEdge (normals (B (P := P))))
    {v u : OrientedVertex (B (P := P))}
    (hv : v ∈ concreteEdgeVertices (hs ha hb hd hncol) e)
    (hu : u ∈ concreteEdgeVertices (hs ha hb hd hncol) e)
    (hproj : v.1 = u.1) : v = u := by
  let q := canonicalDart (hs ha hb hd hncol) e
  change v ∈ orientedEdgeVertices (hs ha hb hd hncol) q.1 q.2 at hv
  change u ∈ orientedEdgeVertices (hs ha hb hd hncol) q.1 q.2 at hu
  simp only [orientedEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv hu
  rcases hv with rfl | rfl <;> rcases hu with rfl | rfl
  · rfl
  · exfalso
    exact boundaryVertex_ne_succ (hs ha hb hd hncol) q.1 q.2
      (congrArg (fun z : ProjectiveBoundaryExtraction.Vertex (B (P := P)) ↦ z.1)
        hproj)
  · exfalso
    exact boundaryVertex_ne_succ (hs ha hb hd hncol) q.1 q.2
      (congrArg (fun z : ProjectiveBoundaryExtraction.Vertex (B (P := P)) ↦ z.1)
        hproj.symm)
  · rfl

/-- If the owner of an edge facing a bad quadrangle has exactly three
projective arrangement vertices, failed-Fano recognition applies.  The two
distinct double vertices required by the recognition theorem are the actual
projective endpoints of this edge. -/
theorem isFailedFano_of_owner_three_vertices
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (f : StrictFace (normals (B (P := P))))
    (i : Fin ((C (P := P) ha hb hd hncol).faceDegree f))
    (hstart : lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex f i).1 = 2)
    (hfinish : lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex f
        (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i)).1 = 2)
    (hthree :
      (verticesOn (Finset.univ : Finset
          (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P)))
        ⟨((D hred ha hb hd hncol).boundaryEdge f i).1.1.1,
          ((D hred ha hb hd hncol).boundaryEdge f i).1.1.2⟩).card = 3) :
    IsFailedFano P := by
  let e := (D hred ha hb hd hncol).boundaryEdge f i
  let s : ProjectiveBoundaryExtraction.Line (B (P := P)) :=
    ⟨e.1.1.1, e.1.1.2⟩
  let v₂ : ProjectiveBoundaryExtraction.Vertex (B (P := P)) :=
    ((D hred ha hb hd hncol).boundaryVertex f i).1
  let v₃ : ProjectiveBoundaryExtraction.Vertex (B (P := P)) :=
    ((D hred ha hb hd hncol).boundaryVertex f
      (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i)).1
  have hvne : v₂ ≠ v₃ := by
    intro h
    have horiented : (D hred ha hb hd hncol).boundaryVertex f i =
        (D hred ha hb hd hncol).boundaryVertex f
          (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i) :=
      concreteEdgeVertices_projective_injective ha hb hd hncol e
        (by
          change (D hred ha hb hd hncol).boundaryVertex f i ∈
            (C (P := P) ha hb hd hncol).edgeVertices e
          rw [(D hred ha hb hd hncol).boundaryEdge_vertices f i]
          simp [e])
        (by
          change (D hred ha hb hd hncol).boundaryVertex f
              (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i) ∈
            (C (P := P) ha hb hd hncol).edgeVertices e
          rw [(D hred ha hb hd hncol).boundaryEdge_vertices f i]
          simp [e]) h
    have hisucc : i = ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i :=
      (D hred ha hb hd hncol).boundaryVertex_injective f horiented
    have hcard := (C (P := P) ha hb hd hncol).edgeVertices_card e
    rw [(D hred ha hb hd hncol).boundaryEdge_vertices f i, ← hisucc] at hcard
    simp at hcard
  have hv₂mem : (D hred ha hb hd hncol).boundaryVertex f i ∈
      concreteEdgeVertices (hs ha hb hd hncol) e := by
    change (D hred ha hb hd hncol).boundaryVertex f i ∈
      (C (P := P) ha hb hd hncol).edgeVertices e
    rw [(D hred ha hb hd hncol).boundaryEdge_vertices f i]
    simp [e]
  have hv₃mem : (D hred ha hb hd hncol).boundaryVertex f
        (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i) ∈
      concreteEdgeVertices (hs ha hb hd hncol) e := by
    change (D hred ha hb hd hncol).boundaryVertex f
        (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i) ∈
      (C (P := P) ha hb hd hncol).edgeVertices e
    rw [(D hred ha hb hd hncol).boundaryEdge_vertices f i]
    simp [e]
  have hv₂s : OnLine (B (P := P)) v₂ s := by
    exact concreteEdgeVertex_on_support (hs ha hb hd hncol) e
      ((D hred ha hb hd hncol).boundaryVertex f i) hv₂mem
  have hv₃s : OnLine (B (P := P)) v₃ s := by
    exact concreteEdgeVertex_on_support (hs ha hb hd hncol) e
      ((D hred ha hb hd hncol).boundaryVertex f
        (ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i)) hv₃mem
  apply BlueDirectionProjective.isFailedFano_of_three_projective_vertices_two_double
    hred hAcard s v₂ v₃ hvne hv₂s hv₃s
  · exact hstart
  · exact hfinish
  · simpa [s, e] using hthree

/-- A convenient specialization in which the two double endpoints are
provided by a bad quadrangle across the chosen edge. -/
theorem isFailedFano_of_badNeighbor_owner_three_vertices
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (f : StrictFace (normals (B (P := P))))
    (i : Fin ((C (P := P) ha hb hd hncol).faceDegree f))
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle
      ((D hred ha hb hd hncol).across ⟨f, i⟩).1)
    (hthree :
      (verticesOn (Finset.univ : Finset
          (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P)))
        ⟨((D hred ha hb hd hncol).boundaryEdge f i).1.1.1,
          ((D hred ha hb hd hncol).boundaryEdge f i).1.1.2⟩).card = 3) :
    IsFailedFano P := by
  apply isFailedFano_of_owner_three_vertices hred ha hb hd hncol hAcard f i
  · exact badNeighbor_start_lineMultiplicity_eq_two hred ha hb hd hncol f i hbad
  · exact badNeighbor_finish_lineMultiplicity_eq_two hred ha hb hd hncol f i hbad
  · exact hthree

end Erdos735.ConcreteStage3Local
