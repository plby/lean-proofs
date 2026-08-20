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

import ErdosProblems.Erdos735.SignVectorArrangement
import ErdosProblems.Erdos735.BlueCellulation

/-!
# Finite face--edge incidence from strict sign vectors

For a finite central arrangement, a spherical face is a realizable strict
sign vector.  An open edge on line `i` is a realizable strict sign vector of
all the other normals, restricted to `n i`'s kernel.  This file constructs
these as honest finite types and proves that every such edge is incident with
exactly two faces.  Endpoint and cyclic-boundary extraction are deliberately
not assumed here.
-/

open scoped BigOperators Matrix
open Matrix

namespace Erdos735
namespace SignVector

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite type of realizable strict spherical face signs. -/
abbrev StrictFace (n : I → Vec3) := {s : I → Bool // Realizable n s}

noncomputable instance strictFaceFintype (n : I → Vec3) : Fintype (StrictFace n) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance strictFaceDecidableEq (n : I → Vec3) :
    DecidableEq (StrictFace n) := Classical.decEq _

theorem card_strictFace (n : I → Vec3) :
    Fintype.card (StrictFace n) = faceCount n := by
  classical
  rw [Fintype.card_subtype]
  unfold faceCount facePatterns
  apply congrArg Finset.card
  ext s
  simp

/-- A line label together with signs on all other lines. -/
abbrev EdgeCode (I : Type*) := Σ i : I, ({j : I // j ≠ i} → Bool)

def otherNormals (n : I → Vec3) (i : I) : {j : I // j ≠ i} → Vec3 :=
  fun j ↦ n j.1

def EdgeFeasible (n : I → Vec3) (e : EdgeCode I) : Prop :=
  RestrictedRealizable (otherNormals n e.1) (n e.1) e.2

/-- The finite type of realizable open edge signs. -/
abbrev StrictEdge (n : I → Vec3) := {e : EdgeCode I // EdgeFeasible n e}

noncomputable instance strictEdgeFintype (n : I → Vec3) : Fintype (StrictEdge n) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance strictEdgeDecidableEq (n : I → Vec3) :
    DecidableEq (StrictEdge n) := Classical.decEq _

noncomputable def strictEdgeEquiv (n : I → Vec3) :
    StrictEdge n ≃ Σ i : I,
      {s : {j : I // j ≠ i} → Bool //
        RestrictedRealizable (otherNormals n i) (n i) s} where
  toFun e := ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
  invFun e := ⟨⟨e.1, e.2.1⟩, e.2.2⟩
  left_inv e := rfl
  right_inv e := rfl

/-- The number of spherical open edges is the sum, over supporting lines,
of feasible strict sign patterns in that line's restriction. -/
theorem card_strictEdge (n : I → Vec3) :
    Fintype.card (StrictEdge n) =
      ∑ i : I, restrictedFaceCount (otherNormals n i) (n i) := by
  classical
  rw [Fintype.card_congr (strictEdgeEquiv n), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fintype.card_subtype]
  unfold restrictedFaceCount restrictedFacePatterns
  apply congrArg Finset.card
  ext s
  simp

/-- Extend an edge sign vector to one of the two sides of its supporting line. -/
def extendEdgeSign (e : EdgeCode I) (b : Bool) : I → Bool := fun j ↦
  if h : j = e.1 then b else e.2 ⟨j, h⟩

@[simp] lemma extendEdgeSign_support (e : EdgeCode I) (b : Bool) :
    extendEdgeSign e b e.1 = b := by
  simp [extendEdgeSign]

lemma extendEdgeSign_other (e : EdgeCode I) (b : Bool) {j : I} (hj : j ≠ e.1) :
    extendEdgeSign e b j = e.2 ⟨j, hj⟩ := by
  simp [extendEdgeSign, hj]

/-- Both sign extensions of a feasible restricted edge are realizable faces. -/
lemma edgeExtension_realizable (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) (b : Bool) : Realizable n (extendEdgeSign e.1 b) := by
  rcases e.2 with ⟨x, hx, hxzero⟩
  obtain ⟨c, hc, hplus, hminus⟩ :=
    exists_small_perturbation (otherNormals n e.1.1) e.1.2 hx (n e.1.1)
  have hself := dotProduct_self_pos (hn e.1.1)
  cases b with
  | false =>
      refine ⟨x - c • n e.1.1, ?_⟩
      intro j
      by_cases hj : j = e.1.1
      · subst j
        simp only [extendEdgeSign_support, signed, Bool.false_eq_true, ↓reduceIte,
          dotProduct_sub, dotProduct_smul, smul_eq_mul]
        nlinarith
      · simpa [extendEdgeSign_other e.1 false hj, otherNormals] using hminus ⟨j, hj⟩
  | true =>
      refine ⟨x + c • n e.1.1, ?_⟩
      intro j
      by_cases hj : j = e.1.1
      · subst j
        simp only [extendEdgeSign_support, signed, ↓reduceIte, dotProduct_add,
          dotProduct_smul, smul_eq_mul]
        nlinarith
      · simpa [extendEdgeSign_other e.1 true hj, otherNormals] using hplus ⟨j, hj⟩

/-- The face on side `b` of an open edge. -/
noncomputable def edgeFace (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) (b : Bool) : StrictFace n :=
  ⟨extendEdgeSign e.1 b, edgeExtension_realizable n hn e b⟩

@[simp] lemma edgeFace_sign (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) (b : Bool) : (edgeFace n hn e b).1 = extendEdgeSign e.1 b := rfl

lemma edgeFace_injective (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) : Function.Injective (edgeFace n hn e) := by
  intro b c hbc
  have hsign := congrArg (fun f : StrictFace n ↦ f.1 e.1.1) hbc
  simpa using hsign

/-- The two faces incident with an edge. -/
noncomputable def edgeFaces (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) : Finset (StrictFace n) :=
  Finset.univ.image (edgeFace n hn e)

theorem edgeFaces_card (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) : (edgeFaces n hn e).card = 2 := by
  classical
  rw [edgeFaces, Finset.card_image_of_injective _ (edgeFace_injective n hn e)]
  decide

/-- An edge lies on a face when all signs away from its supporting line agree. -/
def FaceEdgeIncident (n : I → Vec3) (f : StrictFace n) (e : StrictEdge n) : Prop :=
  ∀ j : {j : I // j ≠ e.1.1}, f.1 j.1 = e.1.2 j

lemma faceEdgeIncident_edgeFace (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (e : StrictEdge n) (b : Bool) : FaceEdgeIncident n (edgeFace n hn e b) e := by
  intro j
  exact extendEdgeSign_other e.1 b j.2

lemma eq_edgeFace_of_incident (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (f : StrictFace n) (e : StrictEdge n) (hfe : FaceEdgeIncident n f e) :
    f = edgeFace n hn e (f.1 e.1.1) := by
  apply Subtype.ext
  funext j
  by_cases hj : j = e.1.1
  · subst j
    simp
  · change f.1 j = extendEdgeSign e.1 (f.1 e.1.1) j
    rw [extendEdgeSign_other e.1 _ hj]
    exact hfe ⟨j, hj⟩

theorem mem_edgeFaces_iff (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (f : StrictFace n) (e : StrictEdge n) :
    f ∈ edgeFaces n hn e ↔ FaceEdgeIncident n f e := by
  classical
  constructor
  · intro hf
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hf
    exact faceEdgeIncident_edgeFace n hn e b
  · intro hfe
    refine Finset.mem_image.mpr ⟨f.1 e.1.1, Finset.mem_univ _, ?_⟩
    exact (eq_edgeFace_of_incident n hn f e hfe).symm

/-- The finite set of open edges incident with a strict sign-vector face. -/
noncomputable def faceEdges (n : I → Vec3) (f : StrictFace n) :
    Finset (StrictEdge n) := by
  classical
  exact Finset.univ.filter (FaceEdgeIncident n f)

theorem mem_faceEdges_iff (n : I → Vec3) (f : StrictFace n) (e : StrictEdge n) :
    e ∈ faceEdges n f ↔ FaceEdgeIncident n f e := by
  classical
  simp [faceEdges]

/-- The concrete face--edge incidence relation is symmetric. -/
theorem faceEdge_iff (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
    (f : StrictFace n) (e : StrictEdge n) :
    e ∈ faceEdges n f ↔ f ∈ edgeFaces n hn e := by
  rw [mem_faceEdges_iff, mem_edgeFaces_iff]

/-- Double-counting the completely algebraic face--edge incidence. -/
theorem sum_faceEdges_card (n : I → Vec3) (hn : ∀ i, n i ≠ 0) :
    (∑ f : StrictFace n, (faceEdges n f).card) =
      2 * Fintype.card (StrictEdge n) := by
  classical
  calc
    (∑ f : StrictFace n, (faceEdges n f).card) =
        ∑ f : StrictFace n, ∑ e : StrictEdge n,
          if e ∈ faceEdges n f then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro f hf
            simp
    _ = ∑ e : StrictEdge n, ∑ f : StrictFace n,
          if e ∈ faceEdges n f then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ e : StrictEdge n, ∑ f : StrictFace n,
          if f ∈ edgeFaces n hn e then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            apply Finset.sum_congr rfl
            intro f hf
            simp only [faceEdge_iff n hn f e]
    _ = ∑ e : StrictEdge n, (edgeFaces n hn e).card := by
            apply Finset.sum_congr rfl
            intro e he
            simp
    _ = 2 * Fintype.card (StrictEdge n) := by
            simp [edgeFaces_card, mul_comm]

/-- The remaining data needed to turn the checked sign-vector incidence into a
`BlueCellulation`: endpoint extraction and the genuine cyclic order of every
face boundary.  Stating it separately prevents those geometric facts from
being hidden in the algebraic definitions. -/
structure BoundaryExtraction (n : I → Vec3) (hn : ∀ i, n i ≠ 0) where
  Vertex : Type*
  instFintypeVertex : Fintype Vertex
  instDecidableEqVertex : DecidableEq Vertex
  blueMultiplicity : Vertex → ℕ
  edgeVertices : StrictEdge n → Finset Vertex
  vertexEdges : Vertex → Finset (StrictEdge n)
  vertexEdge_iff : ∀ v e, e ∈ vertexEdges v ↔ v ∈ edgeVertices e
  edgeVertices_card : ∀ e, (edgeVertices e).card = 2
  vertexEdges_card : ∀ v, (vertexEdges v).card = 2 * blueMultiplicity v
  blueMultiplicity_two_le : ∀ v, 2 ≤ blueMultiplicity v
  faceBoundary : StrictFace n → List (StrictEdge n)
  faceBoundary_nodup : ∀ f, (faceBoundary f).Nodup
  faceBoundary_toFinset : ∀ f, (faceBoundary f).toFinset = faceEdges n f
  faceDegree_three_le : ∀ f, 3 ≤ (faceBoundary f).length
  euler_sphere :
    (Fintype.card Vertex : ℤ) - (Fintype.card (StrictEdge n) : ℤ) +
      (Fintype.card (StrictFace n) : ℤ) = 2

attribute [instance] BoundaryExtraction.instFintypeVertex
attribute [instance] BoundaryExtraction.instDecidableEqVertex

/-- Once the explicit endpoint/cyclic-boundary theorem is supplied, the
sign-vector arrangement is literally a `BlueCellulation`; the two-face field
and face--edge incidence are discharged by the algebra above. -/
noncomputable def BoundaryExtraction.toBlueCellulation
    (n : I → Vec3) (hn : ∀ i, n i ≠ 0) (B : BoundaryExtraction n hn) :
    BlueCellulation B.Vertex (StrictEdge n) (StrictFace n) where
  blueMultiplicity := B.blueMultiplicity
  vertexEdges := B.vertexEdges
  edgeVertices := B.edgeVertices
  vertexEdge_iff := B.vertexEdge_iff
  edgeVertices_card := B.edgeVertices_card
  vertexEdges_card := B.vertexEdges_card
  blueMultiplicity_two_le := B.blueMultiplicity_two_le
  faceBoundary := B.faceBoundary
  faceBoundary_nodup := B.faceBoundary_nodup
  edgeFaces := edgeFaces n hn
  faceEdge_iff := by
    intro f e
    rw [← List.mem_toFinset, B.faceBoundary_toFinset]
    exact faceEdge_iff n hn f e
  edgeFaces_card := edgeFaces_card n hn
  faceDegree_three_le := B.faceDegree_three_le
  euler_sphere := B.euler_sphere

end SignVector
end Erdos735
