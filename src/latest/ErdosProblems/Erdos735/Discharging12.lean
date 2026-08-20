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

import ErdosProblems.Erdos735.BlueCellulation

/-!
# The first two ABKPR discharging steps for Erdős Problem 735

This file packages the cyclic boundary, red-chord, and across-edge data used
in Steps 1 and 2 of the Ackerman--Buchin--Knauer--Pinchasi--Rote proof and
formalizes their charge bookkeeping in integer quarter-units.
-/

namespace Erdos735

open scoped BigOperators

universe uV uE uF

namespace ABKPR

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]

/-- The numerical contradiction in the “good two-diagonal quadrangle has
at least two good vertices” argument.  The first three equations are the
alternating bad-corner equations.  The fourth is the normalization equation
at the allegedly unique good corner, where the additional blue circle has
strictly positive weight. -/
theorem uniqueGoodQuadrangle_weightContradiction
    (w₀ w₁ w₂ w₃ w₄ : ℝ) (hw₀ : 0 < w₀)
    (h₁₂ : w₁ + w₂ = 1 / 2)
    (h₂₃ : w₂ + w₃ = 1 / 2)
    (h₃₄ : w₃ + w₄ = 1 / 2)
    (h₄₁ : w₄ + w₁ + w₀ = 1 / 2) : False := by
  linarith

/-- The `k >= 6` estimate in the large-face lemma, with charge scaled by
four.  Both the number `b` of adjacent bad quadrangles and the number `d` of
Step-3 donations are at most the number `k - 2*r` of vertices free of red
diagonal endpoints. -/
theorem largeFaceArithmetic_ge_six
    (k r b d : ℕ) (hk : 6 ≤ k)
    (hb : b + 2 * r ≤ k) (hd : d + 2 * r ≤ k) :
    0 ≤ 4 * ((k : ℤ) - 3 - (r : ℤ)) - (b : ℤ) - (d : ℤ) := by
  omega

/-- The cyclic successor in a nonempty finite cyclic order. -/
def cyclicSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- A boundary dart is a face together with one of its cyclically ordered
boundary edges. -/
abbrev FaceDart (C : BlueCellulation Vertex Edge Face) :=
  (f : Face) × Fin (C.faceDegree f)

variable (C : BlueCellulation Vertex Edge Face)

theorem faceDegree_pos (f : Face) : 0 < C.faceDegree f := by
  have h := C.faceDegree_three_le f
  simp only [BlueCellulation.faceDegree] at h ⊢
  omega

def faceSucc (f : Face) (i : Fin (C.faceDegree f)) : Fin (C.faceDegree f) :=
  cyclicSucc (faceDegree_pos C f) i

/-- Concrete finite data used in ABKPR's first two discharging steps.

`redChords f` consists of pairs of cyclic boundary indices.  Its separate
endpoint finset is included so the geometric facts “two endpoints per
chord” and “different red chords have disjoint endpoints” can be exposed as
the exact cardinal identity used below.  `stage1Corners f` records those red
endpoints at which the crossing is a bad (two-blue-circle) vertex and the
red curve locally enters the face.
-/
structure Data where
  boundaryVertex : ∀ f, Fin (C.faceDegree f) → Vertex
  boundaryVertex_injective : ∀ f, Function.Injective (boundaryVertex f)
  boundaryEdge : ∀ f, Fin (C.faceDegree f) → Edge
  boundaryEdge_injective : ∀ f, Function.Injective (boundaryEdge f)
  boundaryEdge_mem : ∀ f i, boundaryEdge f i ∈ C.faceBoundary f
  boundaryEdge_vertices : ∀ f i,
    C.edgeVertices (boundaryEdge f i) =
      {boundaryVertex f i, boundaryVertex f (faceSucc C f i)}
  across : FaceDart C → FaceDart C
  across_involutive : Function.Involutive across
  across_otherFace : ∀ d, (across d).1 ≠ d.1
  across_sameEdge : ∀ d,
    boundaryEdge d.1 d.2 = boundaryEdge (across d).1 (across d).2
  redChords : ∀ f, Finset (Fin (C.faceDegree f) × Fin (C.faceDegree f))
  redChord_distinct : ∀ f p, p ∈ redChords f → p.1 ≠ p.2
  redChord_nonadjacent : ∀ f p, p ∈ redChords f →
    p.2 ≠ faceSucc C f p.1 ∧ p.1 ≠ faceSucc C f p.2
  redEndpoints : ∀ f, Finset (Fin (C.faceDegree f))
  redEndpoint_iff : ∀ f i, i ∈ redEndpoints f ↔
    ∃ p ∈ redChords f, i = p.1 ∨ i = p.2
  redEndpoints_card : ∀ f,
    (redEndpoints f).card = 2 * (redChords f).card
  stage1Corners : ∀ f, Finset (Fin (C.faceDegree f))
  stage1Corner_iff : ∀ f i, i ∈ stage1Corners f ↔
    i ∈ redEndpoints f ∧ C.blueMultiplicity (boundaryVertex f i) = 2
  badVertex_receiverCount : ∀ v, C.blueMultiplicity v = 2 →
    (Finset.univ.filter fun f =>
      ∃ i ∈ stage1Corners f, boundaryVertex f i = v).card = 2
  triangle_no_redChord : ∀ f, C.faceDegree f = 3 → (redChords f).card = 0
  goodTwoQuadrangle_twoGoodCorners : ∀ f,
    C.faceDegree f = 4 → (redChords f).card = 2 →
    (redEndpoints f \ stage1Corners f).Nonempty →
    2 ≤ (redEndpoints f \ stage1Corners f).card

namespace Data

variable {C : BlueCellulation Vertex Edge Face}
variable (A : Data C)

def recipientVertices (f : Face) : Finset Vertex :=
  (A.stage1Corners f).image (A.boundaryVertex f)

def receiverFaces (v : Vertex) : Finset Face :=
  Finset.univ.filter fun f => v ∈ A.recipientVertices f

def IsTwoDiagonalQuadrangle (f : Face) : Prop :=
  C.faceDegree f = 4 ∧ (A.redChords f).card = 2

def IsGoodTwoQuadrangle (f : Face) : Prop :=
  A.IsTwoDiagonalQuadrangle f ∧
    (A.redEndpoints f \ A.stage1Corners f).Nonempty

def IsBadTwoQuadrangle (f : Face) : Prop :=
  A.IsTwoDiagonalQuadrangle f ∧
    A.redEndpoints f \ A.stage1Corners f = ∅

instance (f : Face) : Decidable (A.IsTwoDiagonalQuadrangle f) := by
  unfold IsTwoDiagonalQuadrangle
  infer_instance

instance (f : Face) : Decidable (A.IsGoodTwoQuadrangle f) := by
  unfold IsGoodTwoQuadrangle
  infer_instance

instance (f : Face) : Decidable (A.IsBadTwoQuadrangle f) := by
  unfold IsBadTwoQuadrangle
  infer_instance

def initialVertexCharge4 (v : Vertex) : ℤ := 4 * C.vertexCharge v

def initialFaceCharge4 (f : Face) : ℤ := 4 * C.faceCharge f

/-- After Step 1, every selected bad corner has transferred two quarter-units
from the face to the bad vertex. -/
def step1VertexCharge4 (v : Vertex) : ℤ :=
  initialVertexCharge4 (C := C) v + 2 * (A.receiverFaces v).card

def step1FaceCharge4 (f : Face) : ℤ :=
  initialFaceCharge4 (C := C) f - 2 * (A.stage1Corners f).card

lemma stage1Corners_subset (f : Face) :
    A.stage1Corners f ⊆ A.redEndpoints f := by
  intro i hi
  exact (A.stage1Corner_iff f i).mp hi |>.1

lemma redChord_count_twice_le_degree (f : Face) :
    2 * (A.redChords f).card ≤ C.faceDegree f := by
  rw [← A.redEndpoints_card f]
  simpa using Finset.card_le_univ (A.redEndpoints f)

lemma stage1Corners_card_le_twice_chords (f : Face) :
    (A.stage1Corners f).card ≤ 2 * (A.redChords f).card := by
  rw [← A.redEndpoints_card f]
  exact Finset.card_le_card (A.stage1Corners_subset f)

lemma recipientVertices_card (f : Face) :
    (A.recipientVertices f).card = (A.stage1Corners f).card := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj hij
  exact A.boundaryVertex_injective f hij

lemma mem_receiverFaces_iff (v : Vertex) (f : Face) :
    f ∈ A.receiverFaces v ↔
      ∃ i ∈ A.stage1Corners f, A.boundaryVertex f i = v := by
  simp [receiverFaces, recipientVertices]

lemma receiverFaces_card_of_bad {v : Vertex} (hv : C.blueMultiplicity v = 2) :
    (A.receiverFaces v).card = 2 := by
  rw [show A.receiverFaces v = Finset.univ.filter (fun f =>
      ∃ i ∈ A.stage1Corners f, A.boundaryVertex f i = v) by
    ext f
    simp only [A.mem_receiverFaces_iff, Finset.mem_filter, Finset.mem_univ, true_and]]
  exact A.badVertex_receiverCount v hv

lemma receiverFaces_eq_empty_of_not_bad {v : Vertex} (hv : C.blueMultiplicity v ≠ 2) :
    A.receiverFaces v = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨f, hf⟩
  rcases (A.mem_receiverFaces_iff v f).mp hf with ⟨i, hi, hiv⟩
  apply hv
  rw [← hiv]
  exact (A.stage1Corner_iff f i).mp hi |>.2

/-- Every vertex has nonnegative charge after Step 1; a bad vertex has
exactly zero charge. -/
theorem step1VertexCharge4_nonnegative (v : Vertex) :
    0 ≤ A.step1VertexCharge4 v := by
  by_cases hv : C.blueMultiplicity v = 2
  · rw [step1VertexCharge4, A.receiverFaces_card_of_bad hv]
    simp [initialVertexCharge4, BlueCellulation.vertexCharge, hv]
  · rw [step1VertexCharge4, A.receiverFaces_eq_empty_of_not_bad hv]
    have htwo := C.blueMultiplicity_two_le v
    have hthree : 3 ≤ C.blueMultiplicity v := by
      omega
    simp [initialVertexCharge4, BlueCellulation.vertexCharge]
    omega

private lemma sum_card_incidence
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (row : α → Finset β) (column : β → Finset α)
    (h : ∀ a b, b ∈ row a ↔ a ∈ column b) :
    (∑ a, (row a).card) = ∑ b, (column b).card := by
  classical
  calc
    (∑ a, (row a).card) = ∑ a, ∑ b, if b ∈ row a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if b ∈ row a then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, if a ∈ column b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      simp only [h a b]
    _ = ∑ b, (column b).card := by
      apply Finset.sum_congr rfl
      intro b _
      simp

lemma sum_receiverFaces_card :
    (∑ v, (A.receiverFaces v).card) =
      ∑ f, (A.stage1Corners f).card := by
  calc
    (∑ v, (A.receiverFaces v).card) =
        ∑ f, (A.recipientVertices f).card := by
      apply sum_card_incidence A.receiverFaces A.recipientVertices
      intro v f
      simp [receiverFaces]
    _ = ∑ f, (A.stage1Corners f).card := by
      apply Finset.sum_congr rfl
      intro f _
      exact A.recipientVertices_card f

/-- Step 1 only redistributes charge, so the total scaled charge stays
`4 * (-6) = -24`. -/
theorem step1_total_charge :
    (∑ v, A.step1VertexCharge4 v) + (∑ f, A.step1FaceCharge4 f) = -24 := by
  have hcountNat := A.sum_receiverFaces_card
  have hcount :
      (∑ v, ((A.receiverFaces v).card : ℤ)) =
        ∑ f, ((A.stage1Corners f).card : ℤ) := by
    exact_mod_cast hcountNat
  have hinitial := C.total_initial_charge
  simp only [step1VertexCharge4, step1FaceCharge4, initialVertexCharge4,
    initialFaceCharge4, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hcount]
  calc
    4 * (∑ v, C.vertexCharge v) +
          2 * (∑ f, ((A.stage1Corners f).card : ℤ)) +
        (4 * (∑ f, C.faceCharge f) -
          2 * (∑ f, ((A.stage1Corners f).card : ℤ))) =
        4 * ((∑ v, C.vertexCharge v) + ∑ f, C.faceCharge f) := by ring
    _ = -24 := by rw [hinitial]; norm_num

/-- The Step-1 face estimate, scaled by four:
`charge(f) >= 4 * (k - 3 - r)`. -/
theorem step1FaceCharge4_lowerBound (f : Face) :
    4 * ((C.faceDegree f : ℤ) - 3 - (A.redChords f).card) ≤
      A.step1FaceCharge4 f := by
  have hc := A.stage1Corners_card_le_twice_chords f
  simp only [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge]
  omega

lemma redEndpoints_eq_stage1Corners_of_badTwo {f : Face}
    (hf : A.IsBadTwoQuadrangle f) :
    A.redEndpoints f = A.stage1Corners f := by
  apply Finset.Subset.antisymm
  · have hd := hf.2
    exact Finset.sdiff_eq_empty_iff_subset.mp hd
  · exact A.stage1Corners_subset f

lemma redEndpoints_eq_univ_of_twoDiagonal {f : Face}
    (hf : A.IsTwoDiagonalQuadrangle f) : A.redEndpoints f = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [A.redEndpoints_card f, hf.2, hf.1]
  simp

lemma step1FaceCharge4_badTwo {f : Face} (hf : A.IsBadTwoQuadrangle f) :
    A.step1FaceCharge4 f = -4 := by
  have he := A.redEndpoints_eq_stage1Corners_of_badTwo hf
  have hc : (A.stage1Corners f).card = 4 := by
    rw [← he, A.redEndpoints_card f, hf.1.2]
  simp [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge,
    hf.1.1, hc]

lemma step1FaceCharge4_goodTwo_nonnegative {f : Face}
    (hf : A.IsGoodTwoQuadrangle f) : 0 ≤ A.step1FaceCharge4 f := by
  have hgood := A.goodTwoQuadrangle_twoGoodCorners f hf.1.1 hf.1.2 hf.2
  have hsub := A.stage1Corners_subset f
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hend := A.redEndpoints_card f
  simp only [hf.1.2] at hend
  simp only [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge, hf.1.1]
  omega

/-- After Step 1 the only negative faces are bad two-diagonal
quadrangles, and each has charge `-4` in quarter-units. -/
theorem step1FaceCharge4_negative_iff_badTwo (f : Face) :
    A.step1FaceCharge4 f < 0 ↔ A.IsBadTwoQuadrangle f := by
  constructor
  · intro hneg
    have hk : 3 ≤ C.faceDegree f := by
      simpa [BlueCellulation.faceDegree] using C.faceDegree_three_le f
    have hr := A.redChord_count_twice_le_degree f
    have hc := A.stage1Corners_card_le_twice_chords f
    have hdeg : C.faceDegree f ≤ 4 := by
      by_contra h
      have : 5 ≤ C.faceDegree f := by omega
      simp only [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge] at hneg
      omega
    have hnot3 : C.faceDegree f ≠ 3 := by
      intro h3
      have hr0 := A.triangle_no_redChord f h3
      simp only [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge,
        h3, hr0] at hneg hc
      omega
    have h4 : C.faceDegree f = 4 := by omega
    have hr2 : (A.redChords f).card = 2 := by
      simp only [step1FaceCharge4, initialFaceCharge4, BlueCellulation.faceCharge, h4] at hneg
      omega
    refine ⟨⟨h4, hr2⟩, ?_⟩
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hgood
    exact (not_lt_of_ge (A.step1FaceCharge4_goodTwo_nonnegative ⟨⟨h4, hr2⟩, hgood⟩)) hneg
  · intro hbad
    rw [A.step1FaceCharge4_badTwo hbad]
    norm_num

/-- An edge occurrence of `f` whose face across the edge is a bad
two-diagonal quadrangle. -/
def badNeighborIndices (f : Face) : Finset (Fin (C.faceDegree f)) :=
  Finset.univ.filter fun i => A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1

def badNeighborCount (f : Face) : ℕ := (A.badNeighborIndices f).card

/-- Crossing a boundary edge is a permutation of the finite set of face
darts (indeed, an involution). -/
def acrossEquiv : FaceDart C ≃ FaceDart C where
  toFun := A.across
  invFun := A.across
  left_inv := A.across_involutive
  right_inv := A.across_involutive

/-- Double-counting Step-2 transfers: outgoing edge occurrences counted at
their donor faces equal the four incoming occurrences counted at every bad
quadrangle. -/
lemma step2_transfer_count :
    (∑ f, A.badNeighborCount f) =
      ∑ f, if A.IsBadTwoQuadrangle f then C.faceDegree f else 0 := by
  calc
    (∑ f, A.badNeighborCount f) =
        ∑ f, ∑ i : Fin (C.faceDegree f),
          if A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      simp [badNeighborCount, badNeighborIndices]
    _ = ∑ d : FaceDart C,
          if A.IsBadTwoQuadrangle (A.across d).1 then 1 else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ d : FaceDart C, if A.IsBadTwoQuadrangle d.1 then 1 else 0 := by
      let e := A.acrossEquiv
      let g := fun d : FaceDart C => if A.IsBadTwoQuadrangle d.1 then (1 : ℕ) else 0
      change (∑ d, g (e d)) = ∑ d, g d
      exact Equiv.sum_comp e g
    _ = ∑ f, ∑ _i : Fin (C.faceDegree f),
          if A.IsBadTwoQuadrangle f then 1 else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ f, if A.IsBadTwoQuadrangle f then C.faceDegree f else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : A.IsBadTwoQuadrangle f <;> simp [hf]

/-- The local fact used in Step 2: if a bad quadrangle lies across a boundary
edge, neither endpoint of that edge can be a red-chord endpoint of the donor
face. -/
def EndpointRestriction : Prop :=
  ∀ f i, A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 →
    i ∉ A.redEndpoints f ∧ faceSucc C f i ∉ A.redEndpoints f

/-- The finite-cycle packing consequence of the endpoint restriction.  The
special one-chord quadrangle clause records that the two unused vertices are
opposite, so they support no common boundary edge. -/
def NeighborPacking : Prop :=
  (∀ f, A.badNeighborCount f + 2 * (A.redChords f).card ≤ C.faceDegree f) ∧
  (∀ f, 0 < (A.redChords f).card →
      2 * (A.redChords f).card < C.faceDegree f →
      A.badNeighborCount f + 2 * (A.redChords f).card + 1 ≤ C.faceDegree f) ∧
  (∀ f, C.faceDegree f = 4 → (A.redChords f).card = 1 →
      A.badNeighborCount f = 0)

/-- Step 2 gives one quarter-unit to each bad quadrangle across each of its
four edges and subtracts one quarter-unit for every adjacent bad
quadrangle. -/
def step2FaceCharge4 (f : Face) : ℤ :=
  A.step1FaceCharge4 f - A.badNeighborCount f +
    if A.IsBadTwoQuadrangle f then C.faceDegree f else 0

/-- Step 2 is also a pure redistribution, so the total scaled charge is
still `-24`. -/
theorem step2_total_charge :
    (∑ v, A.step1VertexCharge4 v) + (∑ f, A.step2FaceCharge4 f) = -24 := by
  have htransferNat := A.step2_transfer_count
  have htransfer :
      (∑ f, (A.badNeighborCount f : ℤ)) =
        ∑ f, ((if A.IsBadTwoQuadrangle f then C.faceDegree f else 0 : ℕ) : ℤ) := by
    exact_mod_cast htransferNat
  have hstep1 := A.step1_total_charge
  simp only [step2FaceCharge4, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [htransfer]
  linarith

lemma badNeighborCount_le_degree (f : Face) :
    A.badNeighborCount f ≤ C.faceDegree f :=
  by simpa [badNeighborCount] using Finset.card_le_univ (A.badNeighborIndices f)

lemma badNeighborCount_eq_zero_of_redEndpoints_univ
    (hrest : A.EndpointRestriction) {f : Face}
    (hend : A.redEndpoints f = Finset.univ) : A.badNeighborCount f = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨i, hi⟩
  have hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1 :=
    (Finset.mem_filter.mp hi).2
  have hfree := (hrest f i hbad).1
  rw [hend] at hfree
  exact hfree (Finset.mem_univ i)

lemma step2FaceCharge4_badTwo
    (hrest : A.EndpointRestriction) {f : Face}
    (hf : A.IsBadTwoQuadrangle f) : A.step2FaceCharge4 f = 0 := by
  have hend := A.redEndpoints_eq_univ_of_twoDiagonal hf.1
  have hn := A.badNeighborCount_eq_zero_of_redEndpoints_univ hrest hend
  simp [step2FaceCharge4, A.step1FaceCharge4_badTwo hf, hn, hf, hf.1.1]

lemma step2FaceCharge4_triangle (f : Face) (hf : C.faceDegree f = 3) :
    A.step2FaceCharge4 f = -(A.badNeighborCount f : ℤ) := by
  have hr := A.triangle_no_redChord f hf
  have hc := A.stage1Corners_card_le_twice_chords f
  have hnotbad : ¬ A.IsBadTwoQuadrangle f := by
    intro h
    have h4 := h.1.1
    omega
  simp only [step2FaceCharge4, step1FaceCharge4, initialFaceCharge4,
    BlueCellulation.faceCharge, hf, hnotbad, if_false]
  omega

lemma step2FaceCharge4_large_nonnegative
    (hpack : A.NeighborPacking) {f : Face} (hf : 5 ≤ C.faceDegree f) :
    0 ≤ A.step2FaceCharge4 f := by
  have hr := A.redChord_count_twice_le_degree f
  have hc := A.stage1Corners_card_le_twice_chords f
  have hnotbad : ¬ A.IsBadTwoQuadrangle f := by
    intro h
    have h4 := h.1.1
    omega
  have ha0 := A.badNeighborCount_le_degree f
  simp only [step2FaceCharge4, step1FaceCharge4, initialFaceCharge4,
    BlueCellulation.faceCharge, hnotbad, if_false]
  by_cases hz : (A.redChords f).card = 0
  · omega
  · have hp := hpack.1 f
    by_cases heq : 2 * (A.redChords f).card = C.faceDegree f
    · omega
    · have hlt : 2 * (A.redChords f).card < C.faceDegree f := by omega
      have hp' := hpack.2.1 f (Nat.pos_of_ne_zero hz) hlt
      omega

lemma step2FaceCharge4_quadrangle_nonnegative
    (hrest : A.EndpointRestriction) (hpack : A.NeighborPacking)
    {f : Face} (hf : C.faceDegree f = 4) :
    0 ≤ A.step2FaceCharge4 f := by
  by_cases hbad : A.IsBadTwoQuadrangle f
  · rw [A.step2FaceCharge4_badTwo hrest hbad]
  · have hr := A.redChord_count_twice_le_degree f
    have hrle : (A.redChords f).card ≤ 2 := by omega
    have hc := A.stage1Corners_card_le_twice_chords f
    have ha0 := A.badNeighborCount_le_degree f
    simp only [step2FaceCharge4, step1FaceCharge4, initialFaceCharge4,
      BlueCellulation.faceCharge, hbad, if_false, hf]
    interval_cases hrn : (A.redChords f).card
    · omega
    · have hn := hpack.2.2 f hf hrn
      omega
    · have htwo : A.IsTwoDiagonalQuadrangle f := ⟨hf, hrn⟩
      have hend := A.redEndpoints_eq_univ_of_twoDiagonal htwo
      have hn := A.badNeighborCount_eq_zero_of_redEndpoints_univ hrest hend
      by_cases hgood : (A.redEndpoints f \ A.stage1Corners f).Nonempty
      · have hg := A.step1FaceCharge4_goodTwo_nonnegative ⟨htwo, hgood⟩
        simp only [step1FaceCharge4, initialFaceCharge4,
          BlueCellulation.faceCharge, hf] at hg
        omega
      · have he : A.redEndpoints f \ A.stage1Corners f = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hgood
        exact False.elim (hbad ⟨htwo, he⟩)

/-- Under the exact local Step-2 hypotheses, a negative face after Step 2
must be triangular. -/
theorem step2_negative_implies_triangle
    (hrest : A.EndpointRestriction) (hpack : A.NeighborPacking)
    {f : Face} (hneg : A.step2FaceCharge4 f < 0) : C.faceDegree f = 3 := by
  have hk : 3 ≤ C.faceDegree f := by
    simpa [BlueCellulation.faceDegree] using C.faceDegree_three_le f
  by_contra h3
  by_cases h4 : C.faceDegree f = 4
  · exact (not_lt_of_ge (A.step2FaceCharge4_quadrangle_nonnegative hrest hpack h4)) hneg
  · have h5 : 5 ≤ C.faceDegree f := by omega
    exact (not_lt_of_ge (A.step2FaceCharge4_large_nonnegative hpack h5)) hneg

end Data

end ABKPR

end Erdos735
