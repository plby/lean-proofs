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

import ErdosProblems.Erdos735.RedChordExtraction
import ErdosProblems.Erdos735.RedSectorGeometry

/-!
# Endpoint restriction for red chords

This file composes concrete projective red-chord incidence with the sign-vector description of
the two faces across an edge.  It proves the geometric content of ABKPR's endpoint restriction:
if every boundary vertex of the face across an edge is a red endpoint, then neither endpoint of
that edge can be a red endpoint of the original face.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.RedChordExtraction.Geometry

open ProjectiveArrangement SignVector
open SignVector.RotationRealization
open RedBlueDualIncidence

variable {A B : Finset Point}
variable {G : SimpleGraph (BlueVertex B)} [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (X : RotationRealization (G := G) (blueNormals B) (blueNormals_ne_zero B))
variable (H : Geometry (A := A) (B := B) X)

theorem mem_redEndpoints_iff_exists_feasible_incident
    (f : StrictFace (blueNormals B)) (i : Fin (X.strictC.faceDegree f)) :
    i ∈ redEndpoints (A := A) (B := B) X H f ↔
      ∃ a : RedLine A, a ∈ redChordLines (A := A) f ∧
        Incident (X.boundaryVertex f i).1 a.1 := by
  constructor
  · intro hi
    obtain ⟨p, hp, hip⟩ :=
      (mem_redEndpoints_iff (A := A) (B := B) X H f i).mp hi
    obtain ⟨a, rfl⟩ :=
      (mem_redChords_iff (A := A) (B := B) X H f p).mp hp
    refine ⟨a.1, a.2, ?_⟩
    apply (mem_redEndpointIndices_iff (A := A) (B := B) X f a.1 i).mp
    rw [(chordPair_spec (A := A) (B := B) X H f a).2]
    rcases hip with rfl | rfl <;> simp
  · rintro ⟨a, ha, hinc⟩
    let aa : ChordLine (A := A) (B := B) f := ⟨a, ha⟩
    apply (mem_redEndpoints_iff (A := A) (B := B) X H f i).mpr
    refine ⟨chordPair (A := A) (B := B) X H f aa, ?_, ?_⟩
    · apply (mem_redChords_iff (A := A) (B := B) X H f _).mpr
      exact ⟨aa, rfl⟩
    · have hi' : i ∈ redEndpointIndices (A := A) X f a :=
        (mem_redEndpointIndices_iff (A := A) (B := B) X f a i).mpr hinc
      rw [(chordPair_spec (A := A) (B := B) X H f aa).2] at hi'
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi'

include H in
theorem endpoint_not_red_of_across_all_red
    (f : StrictFace (blueNormals B)) (i q : Fin (X.strictC.faceDegree f))
    (hq : q = i ∨ q = X.strictFaceSucc f i)
    (hall : redEndpoints (A := A) (B := B) X H (X.across ⟨f, i⟩).1 = Finset.univ) :
    q ∉ redEndpoints (A := A) (B := B) X H f := by
  intro hqred
  obtain ⟨a, ha, hainc⟩ :=
    (mem_redEndpoints_iff_exists_feasible_incident
      (A := A) (B := B) X H f q).mp hqred
  let d : X.StrictFaceDart := ⟨f, i⟩
  let g : StrictFace (blueNormals B) := (X.across d).1
  let j : Fin (X.strictC.faceDegree g) := (X.across d).2
  have hvmem : X.boundaryVertex f q ∈
      X.strictC.edgeVertices (X.boundaryEdge f i) := by
    rw [X.boundaryEdge_vertices f i]
    rcases hq with rfl | rfl <;> simp
  have hvmem' : X.boundaryVertex f q ∈
      X.strictC.edgeVertices (X.boundaryEdge g j) := by
    rw [← X.across_sameEdge d]
    exact hvmem
  rw [X.boundaryEdge_vertices g j] at hvmem'
  obtain ⟨k, hkv⟩ : ∃ k : Fin (X.strictC.faceDegree g),
      X.boundaryVertex g k = X.boundaryVertex f q := by
    rcases Finset.mem_insert.mp hvmem' with h | h
    · exact ⟨j, h.symm⟩
    · exact ⟨X.strictFaceSucc g j, (Finset.mem_singleton.mp h).symm⟩
  have hallg : redEndpoints (A := A) (B := B) X H g = Finset.univ := hall
  have hkred : k ∈ redEndpoints (A := A) (B := B) X H g := by
    rw [hallg]
    exact Finset.mem_univ k
  obtain ⟨a', ha', ha'inc⟩ :=
    (mem_redEndpoints_iff_exists_feasible_incident
      (A := A) (B := B) X H g k).mp hkred
  have haa' : a = a' := by
    by_contra hne
    apply H.no_two_red_at_blueVertex a a' hne (X.boundaryVertex f q)
    exact ⟨hainc, hkv ▸ ha'inc⟩
  subst a'
  let e : StrictEdge (blueNormals B) := X.boundaryEdge f i
  let b : Bool := f.1 (strictEdgeOwner e)
  have hfe : FaceEdgeIncident (blueNormals B) f e :=
    (mem_faceEdges_iff (blueNormals B) f e).mp (X.boundaryEdge_mem_faceEdges f i)
  have hf : f = edgeFace (blueNormals B) (blueNormals_ne_zero B) e b :=
    eq_edgeFace_of_incident (blueNormals B) (blueNormals_ne_zero B) f e hfe
  have hg : g = edgeFace (blueNormals B) (blueNormals_ne_zero B) e (!b) := by
    exact X.across_face_eq_edgeFace_flip d
  have haEdge : RestrictedRealizable (blueNormals B) (normalVec a.1)
      (edgeFace (blueNormals B) (blueNormals_ne_zero B) e b).1 := by
    rw [← hf]
    exact (mem_redChordLines_iff (A := A) (B := B) f a).mp ha
  have haAcross : RestrictedRealizable (blueNormals B) (normalVec a.1)
      (edgeFace (blueNormals B) (blueNormals_ne_zero B) e (!b)).1 := by
    rw [← hg]
    exact (mem_redChordLines_iff (A := A) (B := B) g a).mp ha'
  have howner : Incident (X.boundaryVertex f q).1 e.1.1.1 := by
    rcases hq with hqi | hqi
    · rw [hqi]
      exact H.boundary_start_on_owner f i
    · rw [hqi]
      exact H.boundary_finish_on_owner f i
  exact not_redChord_both_edgeFaces_at_projective_endpoint B e
    (X.boundaryVertex f q) a.1 b howner hainc haEdge haAcross

include H in
/-- If every vertex of the face across a boundary edge is a red endpoint,
then neither endpoint of the shared edge is a red endpoint of the original
face.  This is the geometric content of ABKPR's endpoint restriction. -/
theorem endpointRestriction_of_across_all_red
    (f : StrictFace (blueNormals B)) (i : Fin (X.strictC.faceDegree f))
    (hall : redEndpoints (A := A) (B := B) X H (X.across ⟨f, i⟩).1 = Finset.univ) :
    i ∉ redEndpoints (A := A) (B := B) X H f ∧
      X.strictFaceSucc f i ∉ redEndpoints (A := A) (B := B) X H f := by
  constructor
  · exact endpoint_not_red_of_across_all_red (A := A) (B := B) X H f i i
      (Or.inl rfl) hall
  · exact endpoint_not_red_of_across_all_red (A := A) (B := B) X H f i
      (X.strictFaceSucc f i) (Or.inr rfl) hall

end Erdos735.RedChordExtraction.Geometry
