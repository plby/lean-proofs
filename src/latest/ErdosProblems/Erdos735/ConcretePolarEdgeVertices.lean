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

import ErdosProblems.Erdos735.ConcretePolarOrientedAcross

open Classical
noncomputable section

namespace Erdos735.ConcretePolarEdgeVertices

open ProjectiveArrangement SignVector
open SignVector.PolarBoundaryAcross
open SignVector.RedChordSector
open ProjectiveBoundaryExtraction
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := {b // b ∈ B}

variable {B : Finset Point} [Nonempty (Line B)]
variable (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)

/-- A deterministic incident-face occurrence of a strict edge. -/
noncomputable def canonicalDart (e : StrictEdge (normals B)) :
    IndexedDart (normals B) :=
  let f := edgeFace (normals B) (normals_ne_zero B) e false
  let he : e ∈ faceEdges (normals B) f := by
    rw [mem_faceEdges_iff]
    exact faceEdgeIncident_edgeFace (normals B) (normals_ne_zero B) e false
  ⟨f, (boundaryEdgeEquiv (normals B) normal_cross hspan f).symm ⟨e, he⟩⟩

@[simp] theorem boundaryEdge_canonicalDart (e : StrictEdge (normals B)) :
    boundaryEdge (normals B) normal_cross hspan (canonicalDart hspan e).1
      (canonicalDart hspan e).2 = e := by
  let f := edgeFace (normals B) (normals_ne_zero B) e false
  let he : e ∈ faceEdges (normals B) f := by
    rw [mem_faceEdges_iff]
    exact faceEdgeIncident_edgeFace (normals B) (normals_ne_zero B) e false
  change boundaryEdge (normals B) normal_cross hspan f
      ((boundaryEdgeEquiv (normals B) normal_cross hspan f).symm ⟨e, he⟩) = e
  have h := (boundaryEdgeEquiv (normals B) normal_cross hspan f).apply_symm_apply ⟨e, he⟩
  exact congrArg Subtype.val h

/-- The literal two globally oriented endpoints of a strict edge. -/
noncomputable def concreteEdgeVertices (e : StrictEdge (normals B)) :
    Finset (OrientedVertex B) :=
  orientedEdgeVertices hspan (canonicalDart hspan e).1 (canonicalDart hspan e).2

@[simp] theorem concreteEdgeVertices_card (e : StrictEdge (normals B)) :
    (concreteEdgeVertices hspan e).card = 2 := by
  exact orientedEdgeVertices_card hspan _ _

/-- On every polar face boundary, the global edge endpoint pair is exactly
the pair of the two consecutive globally oriented face corners. -/
theorem concreteEdgeVertices_boundaryEdge
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    concreteEdgeVertices hspan
        (boundaryEdge (normals B) normal_cross hspan f i) =
      orientedEdgeVertices hspan f i := by
  unfold concreteEdgeVertices
  exact ConcretePolarOrientedVertex.orientedEdgeVertices_eq_of_sameEdge hspan
    (canonicalDart hspan
      (boundaryEdge (normals B) normal_cross hspan f i))
    (⟨f, i⟩ : IndexedDart (normals B)) (by
      rw [boundaryEdge_canonicalDart])

/-- All strict edges incident with a global oriented projective vertex. -/
def concreteVertexEdges (v : OrientedVertex B) :
    Finset (StrictEdge (normals B)) :=
  Finset.univ.filter fun e ↦ v ∈ concreteEdgeVertices hspan e

@[simp] theorem mem_concreteVertexEdges_iff
    (v : OrientedVertex B) (e : StrictEdge (normals B)) :
    e ∈ concreteVertexEdges hspan v ↔ v ∈ concreteEdgeVertices hspan e := by
  simp [concreteVertexEdges]

/-- Every concrete endpoint is incident with its strict edge's supporting
projective line. -/
theorem concreteEdgeVertex_on_support
    (e : StrictEdge (normals B)) (v : OrientedVertex B)
    (hv : v ∈ concreteEdgeVertices hspan e) :
    Incident v.1.1 e.1.1.1 := by
  let d := canonicalDart hspan e
  have hedge : boundaryEdge (normals B) normal_cross hspan d.1 d.2 = e :=
    boundaryEdge_canonicalDart hspan e
  change v ∈ orientedEdgeVertices hspan d.1 d.2 at hv
  simp only [orientedEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · have hp := congrArg (fun z : OrientedVertex B ↦ z.1.1) hv
    rw [boundaryOrientedVertex_projective] at hp
    rw [← hedge, hp]
    exact boundaryVertex_on_edge_start (normals B) normal_cross hspan d.1 d.2
  · have hp := congrArg (fun z : OrientedVertex B ↦ z.1.1) hv
    rw [boundaryOrientedVertex_projective] at hp
    rw [← hedge, hp]
    exact boundaryVertex_on_edge_finish (normals B) normal_cross hspan d.1 d.2

/-- The canonical representative of every actual endpoint weakly realizes
the restricted sign sector of its strict edge. -/
theorem concreteEdgeVertex_weaklyRealizes_restriction
    (e : StrictEdge (normals B)) (v : OrientedVertex B)
    (hv : v ∈ concreteEdgeVertices hspan e) :
    WeaklyRealizes (otherNormals (normals B) e.1.1) e.1.2
      (orientedRep v) := by
  let d := canonicalDart hspan e
  have hdedge : boundaryEdge (normals B) normal_cross hspan d.1 d.2 = e :=
    boundaryEdge_canonicalDart hspan e
  have hmem : v ∈ orientedEdgeVertices hspan d.1 d.2 := by
    exact hv
  have hedgeMem : e ∈ faceEdges (normals B) d.1 := by
    rw [← hdedge]
    exact boundaryEdge_mem (normals B) normal_cross hspan d.1 d.2
  have hinc : FaceEdgeIncident (normals B) d.1 e :=
    (mem_faceEdges_iff (normals B) d.1 e).mp hedgeMem
  simp only [orientedEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · intro j
    have hw := orientedRep_boundaryOrientedVertex_weaklyRealizes hspan d.1 d.2 j.1
    have hsign := hinc ⟨j.1, j.2⟩
    simpa [otherNormals, hsign] using hw
  · intro j
    have hw := orientedRep_boundaryOrientedVertex_weaklyRealizes hspan d.1
      (Erdos957.cyclicSucc d.2) j.1
    have hsign := hinc ⟨j.1, j.2⟩
    simpa [otherNormals, hsign] using hw

end Erdos735.ConcretePolarEdgeVertices
