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

import ErdosProblems.Erdos735.PolarBoundaryOrder
import ErdosProblems.Erdos735.SignVectorPolar

/-!
# Owner-preserving polar boundaries and across-edge pairing

The polar polygon gives a genuine cyclic ordering of the strict edges of
every sign-vector chamber.  This file equips those indexed boundaries with
their consecutive projective vertices and defines the across-edge map purely
algebraically by flipping the sign on the supporting line.  The resulting
dependent across map is an involution, changes the face, and preserves the
strict edge exactly.
-/

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.SignVector.PolarBoundaryAcross

open PolarFace PolarPlaneChart PolarBoundaryOrder

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
variable (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
variable (hspan : Submodule.span ℝ (Set.range n) = ⊤)

abbrev BoundaryIndex (f : StrictFace n) :=
  Fin (Erdos957.hullVertexCount
    (boundaryPolygon n f.1 (faceWitness n f)))

def boundaryEdge (f : StrictFace n) (i : BoundaryIndex n f) : StrictEdge n :=
  PolarBoundaryOrder.boundaryEdge f (faceWitness_realizes n f) hcross hspan i

noncomputable def boundaryEdgeEquiv (f : StrictFace n) :
    BoundaryIndex n f ≃ {e // e ∈ faceEdges n f} :=
  PolarBoundaryOrder.boundaryEdgeEquiv f (faceWitness_realizes n f) hcross hspan

theorem boundaryEdgeEquiv_val (f : StrictFace n) (i : BoundaryIndex n f) :
    (boundaryEdgeEquiv n hcross hspan f i).1 = boundaryEdge n hcross hspan f i := rfl

theorem boundaryEdge_mem (f : StrictFace n) (i : BoundaryIndex n f) :
    boundaryEdge n hcross hspan f i ∈ faceEdges n f :=
  (boundaryEdgeEquiv n hcross hspan f i).2

/-- The projective vertex before boundary edge `i`; thus edge `i` runs
from `boundaryVertex i` to `boundaryVertex (cyclicSucc i)`. -/
noncomputable def boundaryVertex (f : StrictFace n) (i : BoundaryIndex n f) :
    ℙ ℝ Vec3 :=
  PolarBoundaryOrder.boundaryProjectiveVertex f (faceWitness_realizes n f)
    hcross hspan ((finRotate _).symm i)

theorem boundaryVertex_on_edge_start (f : StrictFace n) (i : BoundaryIndex n f) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryEdge n hcross hspan f i).1.1)
      (boundaryVertex n hcross hspan f i) := by
  have h := PolarBoundaryOrder.boundaryProjectiveVertex_on_right f
    (faceWitness_realizes n f) hcross hspan ((finRotate _).symm i)
  have hs : Erdos957.cyclicSucc ((finRotate _).symm i) = i :=
    (finRotate _).apply_symm_apply i
  rw [hs] at h
  simpa [boundaryVertex, boundaryEdge] using h

theorem boundaryVertex_on_edge_finish (f : StrictFace n) (i : BoundaryIndex n f) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryEdge n hcross hspan f i).1.1)
      (boundaryVertex n hcross hspan f (Erdos957.cyclicSucc i)) := by
  have h := PolarBoundaryOrder.boundaryProjectiveVertex_on_left f
    (faceWitness_realizes n f) hcross hspan i
  have hs : (finRotate _).symm (Erdos957.cyclicSucc i) = i :=
    (finRotate _).symm_apply_apply i
  change ProjectiveArrangement.OnProjectiveLine
    (n (boundaryEdge n hcross hspan f i).1.1)
    (PolarBoundaryOrder.boundaryProjectiveVertex f (faceWitness_realizes n f)
      hcross hspan ((finRotate _).symm (Erdos957.cyclicSucc i)))
  rw [hs]
  simpa [boundaryEdge] using h

def faceBoundary (f : StrictFace n) : List (StrictEdge n) :=
  PolarBoundaryOrder.faceBoundary f (faceWitness_realizes n f) hcross hspan

theorem faceBoundary_nodup (f : StrictFace n) :
    (faceBoundary n hcross hspan f).Nodup :=
  PolarBoundaryOrder.faceBoundary_nodup f (faceWitness_realizes n f) hcross hspan

theorem faceBoundary_toFinset (f : StrictFace n) :
    (faceBoundary n hcross hspan f).toFinset = faceEdges n f :=
  PolarBoundaryOrder.faceBoundary_toFinset f (faceWitness_realizes n f) hcross hspan

abbrev FaceEdgeDart := (f : StrictFace n) × {e // e ∈ faceEdges n f}

noncomputable def indexedDartEquiv :
    ((f : StrictFace n) × BoundaryIndex n f) ≃ FaceEdgeDart n :=
  Equiv.sigmaCongrRight fun f ↦ boundaryEdgeEquiv n hcross hspan f

def oppositeFace (f : StrictFace n) (e : StrictEdge n) : StrictFace n :=
  edgeFace n hn e (!(f.1 e.1.1))

theorem oppositeFace_edge_mem (f : StrictFace n) (e : StrictEdge n) :
    e ∈ faceEdges n (oppositeFace n hn f e) := by
  rw [mem_faceEdges_iff]
  exact faceEdgeIncident_edgeFace n hn e _

theorem face_eq_edgeFace_of_mem (f : StrictFace n) (e : StrictEdge n)
    (he : e ∈ faceEdges n f) :
    f = edgeFace n hn e (f.1 e.1.1) :=
  eq_edgeFace_of_incident n hn f e ((mem_faceEdges_iff n f e).mp he)

theorem oppositeFace_ne (f : StrictFace n) (e : StrictEdge n)
    (he : e ∈ faceEdges n f) : oppositeFace n hn f e ≠ f := by
  intro h
  have hf := face_eq_edgeFace_of_mem n hn f e he
  have hfaces : edgeFace n hn e (!(f.1 e.1.1)) =
      edgeFace n hn e (f.1 e.1.1) := h.trans hf
  have hb := edgeFace_injective n hn e hfaces
  cases hval : f.1 e.1.1 <;> simp [hval] at hb

theorem oppositeFace_involutive (f : StrictFace n) (e : StrictEdge n)
    (he : e ∈ faceEdges n f) :
    oppositeFace n hn (oppositeFace n hn f e) e = f := by
  have hf := face_eq_edgeFace_of_mem n hn f e he
  rw [oppositeFace, oppositeFace]
  simp only [edgeFace_sign, extendEdgeSign_support, Bool.not_not]
  exact hf.symm

noncomputable def faceEdgeAcross (d : FaceEdgeDart n) : FaceEdgeDart n :=
  ⟨oppositeFace n hn d.1 d.2.1,
    ⟨d.2.1, oppositeFace_edge_mem n hn d.1 d.2.1⟩⟩

theorem faceEdgeAcross_involutive :
    Function.Involutive (faceEdgeAcross n hn) := by
  rintro ⟨f, e, he⟩
  exact Sigma.subtype_ext (oppositeFace_involutive n hn f e he) rfl

abbrev IndexedDart := (f : StrictFace n) × BoundaryIndex n f

noncomputable def across (d : IndexedDart n) : IndexedDart n :=
  (indexedDartEquiv n hcross hspan).symm
    (faceEdgeAcross n hn (indexedDartEquiv n hcross hspan d))

theorem across_involutive : Function.Involutive (across n hn hcross hspan) := by
  intro d
  apply (indexedDartEquiv n hcross hspan).injective
  simp only [across, Equiv.apply_symm_apply]
  rw [faceEdgeAcross_involutive n hn]

theorem across_otherFace (d : IndexedDart n) :
    (across n hn hcross hspan d).1 ≠ d.1 := by
  have hface : (across n hn hcross hspan d).1 =
      oppositeFace n hn d.1 (boundaryEdge n hcross hspan d.1 d.2) := by
    change ((indexedDartEquiv n hcross hspan).symm
      (faceEdgeAcross n hn (indexedDartEquiv n hcross hspan d))).1 = _
    have h := (indexedDartEquiv n hcross hspan).apply_symm_apply
      (faceEdgeAcross n hn (indexedDartEquiv n hcross hspan d))
    exact congrArg Sigma.fst h
  rw [hface]
  exact oppositeFace_ne n hn d.1 _ (boundaryEdge_mem n hcross hspan d.1 d.2)

theorem across_sameEdge (d : IndexedDart n) :
    boundaryEdge n hcross hspan d.1 d.2 =
      boundaryEdge n hcross hspan (across n hn hcross hspan d).1
        (across n hn hcross hspan d).2 := by
  have h := (indexedDartEquiv n hcross hspan).apply_symm_apply
    (faceEdgeAcross n hn (indexedDartEquiv n hcross hspan d))
  have hedge := congrArg (fun z : FaceEdgeDart n ↦ z.2.1) h
  exact hedge.symm

theorem across_face_eq_edgeFace_flip (d : IndexedDart n) :
    (across n hn hcross hspan d).1 =
      edgeFace n hn (boundaryEdge n hcross hspan d.1 d.2)
        (!(d.1.1 (boundaryEdge n hcross hspan d.1 d.2).1.1)) := by
  change (across n hn hcross hspan d).1 =
    oppositeFace n hn d.1 (boundaryEdge n hcross hspan d.1 d.2)
  have h := (indexedDartEquiv n hcross hspan).apply_symm_apply
    (faceEdgeAcross n hn (indexedDartEquiv n hcross hspan d))
  exact congrArg Sigma.fst h

/-- Replace the unordered face lists of any already-counted spherical
extraction by the genuine owner-preserving polar cycles.  Vertex/edge
incidence and Euler are retained from the counted extraction. -/
noncomputable def toBoundaryExtraction (B : BoundaryExtraction n hn) :
    BoundaryExtraction n hn where
  Vertex := B.Vertex
  instFintypeVertex := B.instFintypeVertex
  instDecidableEqVertex := B.instDecidableEqVertex
  blueMultiplicity := B.blueMultiplicity
  edgeVertices := B.edgeVertices
  vertexEdges := B.vertexEdges
  vertexEdge_iff := B.vertexEdge_iff
  edgeVertices_card := B.edgeVertices_card
  vertexEdges_card := B.vertexEdges_card
  blueMultiplicity_two_le := B.blueMultiplicity_two_le
  faceBoundary := faceBoundary n hcross hspan
  faceBoundary_nodup := faceBoundary_nodup n hcross hspan
  faceBoundary_toFinset := faceBoundary_toFinset n hcross hspan
  faceDegree_three_le := by
    intro f
    rw [← List.toFinset_card_of_nodup (faceBoundary_nodup n hcross hspan f),
      faceBoundary_toFinset n hcross hspan f]
    exact PolarFace.faceEdges_card_three_le_of_span_eq_top n hcross hspan f
  euler_sphere := B.euler_sphere

/-- The counted cellulation equipped with the actual polar face cycles. -/
noncomputable def toBlueCellulation (B : BoundaryExtraction n hn) :
    BlueCellulation B.Vertex (StrictEdge n) (StrictFace n) :=
  (toBoundaryExtraction n hn hcross hspan B).toBlueCellulation n hn

end Erdos735.SignVector.PolarBoundaryAcross
