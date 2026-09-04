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

import ErdosProblems.Erdos735.PolarPlaneChart

/-!
# Cyclic polar boundaries with projective vertices

The polar polygon of a strict sign-vector face canonically orders its
supporting arrangement lines.  Consecutive supporting lines meet in a
nonzero cross product, hence determine an actual projective arrangement
vertex.  This file keeps the line labels throughout the cyclic hull order;
no cardinality-only equivalence is used.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.SignVector.PolarBoundaryOrder

noncomputable section

open PolarFace PolarPlaneChart

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Standard first basis vector in the polar coordinate plane. -/
def planeBasisZero : Plane := planePoint 1 0

/-- Standard second basis vector in the polar coordinate plane. -/
def planeBasisOne : Plane := planePoint 0 1

lemma planeFunctional_decompose (l : Plane →L[ℝ] ℝ) (p : Plane) :
    l p = l planeBasisZero * p 0 + l planeBasisOne * p 1 := by
  have hp : p = p 0 • planeBasisZero + p 1 • planeBasisOne := by
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [planeBasisZero, planeBasisOne, planePoint]
  calc
    l p = l (p 0 • planeBasisZero + p 1 • planeBasisOne) := congrArg l hp
    _ = l planeBasisZero * p 0 + l planeBasisOne * p 1 := by
      simp only [map_add, map_smul, smul_eq_mul]
      ring_nf

/-- Insert the two coefficients of a planar functional in the coordinates
retained by `PolarPlaneChart.coord`. -/
def coordDual (x : Vec3) (l : Plane →L[ℝ] ℝ) : Vec3 :=
  if x 2 ≠ 0 then ![l planeBasisZero, l planeBasisOne, 0]
  else if x 1 ≠ 0 then ![l planeBasisZero, 0, l planeBasisOne]
  else ![0, l planeBasisZero, l planeBasisOne]

/-- Dotting with `coordDual` evaluates the planar functional on the chart. -/
lemma dot_coordDual (x p : Vec3) (l : Plane →L[ℝ] ℝ) :
    p ⬝ᵥ coordDual x l = l (coord x p) := by
  rw [planeFunctional_decompose]
  by_cases hx2 : x 2 = 0
  · by_cases hx1 : x 1 = 0
    · simp only [Fin.isValue]
      change p 1 * l planeBasisZero + p 2 * l planeBasisOne =
        l planeBasisZero * p 1 + l planeBasisOne * p 2
      ring
    · simp only [Fin.isValue]
      change p 0 * l planeBasisZero + p 2 * l planeBasisOne =
        l planeBasisZero * p 0 + l planeBasisOne * p 2
      ring
  · simp only [Fin.isValue]
    change p 0 * l planeBasisZero + p 1 * l planeBasisOne =
      l planeBasisZero * p 0 + l planeBasisOne * p 1
    ring

/-- Lift a supporting functional at level `c` to a homogeneous covector. -/
def liftedSupportVector (x : Vec3) (l : Plane →L[ℝ] ℝ) (c : ℝ) : Vec3 :=
  c • x - coordDual x l

/-- Exact affine-to-homogeneous support identity. -/
theorem dot_liftedSupportVector {x p : Vec3} (hp : p ⬝ᵥ x = 1)
    (l : Plane →L[ℝ] ℝ) (c : ℝ) :
    p ⬝ᵥ liftedSupportVector x l c = c - l (coord x p) := by
  rw [liftedSupportVector, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    hp, dot_coordDual]
  ring

/-- The canonical face edge supported by a feasible owner. -/
def edgeOfOwner {n : I → Vec3} {s : I → Bool}
    (i : {i // i ∈ edgeOwners n s}) : StrictEdge n :=
  ⟨faceEdgeCode s i.1, mem_edgeOwners.mp i.2⟩

lemma edgeOfOwner_owner {n : I → Vec3} {s : I → Bool}
    (i : {i // i ∈ edgeOwners n s}) : (edgeOfOwner i).1.1 = i.1 := rfl

/-- On a fixed face, feasible owners and incident strict edges are exactly equivalent. -/
noncomputable def ownerFaceEdgeEquiv {n : I → Vec3} (f : StrictFace n) :
    {i // i ∈ edgeOwners n f.1} ≃ {e // e ∈ faceEdges n f} where
  toFun i := ⟨edgeOfOwner i, by
    rw [mem_faceEdges_iff]
    intro j
    rfl⟩
  invFun e := by
    let i : I := e.1.1.1
    have hinc : FaceEdgeIncident n f e.1 := (mem_faceEdges_iff n f e.1).1 e.2
    have hcode : e.1.1 = faceEdgeCode f.1 i := by
      refine Sigma.ext (x := e.1.1) (y := faceEdgeCode f.1 i) rfl ?_
      exact heq_of_eq <| funext fun j ↦ (hinc j).symm
    refine ⟨i, mem_edgeOwners.mpr ?_⟩
    rw [← hcode]
    exact e.1.2
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    let i : I := e.1.1.1
    have hinc : FaceEdgeIncident n f e.1 := (mem_faceEdges_iff n f e.1).1 e.2
    have hcode : e.1.1 = faceEdgeCode f.1 i := by
      refine Sigma.ext (x := e.1.1) (y := faceEdgeCode f.1 i) rfl ?_
      exact heq_of_eq <| funext fun j ↦ (hinc j).symm
    change faceEdgeCode f.1 i = e.1.1
    exact hcode.symm

/-- Feasible owners and their points on the polar polygon are exactly equivalent. -/
noncomputable def ownerPointEquiv {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    {i // i ∈ edgeOwners n s} ≃ {p // p ∈ boundaryPolygon n s x} :=
  Equiv.ofBijective
    (fun i ↦ ⟨ownerPoint n s x i.1,
      Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)
    ⟨fun i j hij ↦ Subtype.ext
        (ownerPoint_injective hx hcross (congrArg Subtype.val hij)),
      fun p ↦ by
        obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp p.2
        exact ⟨⟨i, hi⟩, Subtype.ext hip⟩⟩

/-- The polar boundary polygon has as many points as the face has edges. -/
theorem boundaryPolygon_card_eq_faceEdges_card {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    (boundaryPolygon n f.1 x).card = (faceEdges n f).card := by
  calc
    (boundaryPolygon n f.1 x).card = (edgeOwners n f.1).card :=
      boundaryPolygon_card hx hcross
    _ = Fintype.card {i // i ∈ edgeOwners n f.1} := (Fintype.card_coe _).symm
    _ = Fintype.card {e // e ∈ faceEdges n f} :=
      Fintype.card_congr (ownerFaceEdgeEquiv f)
    _ = (faceEdges n f).card := Fintype.card_coe _

/-- Full rank gives the polar boundary at least three vertices. -/
theorem three_le_boundaryPolygon_card {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    3 ≤ (boundaryPolygon n f.1 x).card := by
  rw [boundaryPolygon_card_eq_faceEdges_card f hx hcross]
  exact faceEdges_card_three_le_of_span_eq_top n hcross hspan f

/-- The genuine counterclockwise cyclic hull order of a face's polar boundary. -/
noncomputable def boundaryHullOrder {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Erdos957.CyclicHullOrder (boundaryPolygon n f.1 x) :=
  Erdos957.cyclicHullOrderOfThree _ <| by
    rw [hullVertices_boundaryPolygon hx hcross]
    exact three_le_boundaryPolygon_card f hx hcross hspan

/-- A supporting functional for the polar hull edge at `t`. -/
noncomputable def cornerFunctional {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : Plane →L[ℝ] ℝ :=
  Classical.choose ((boundaryHullOrder f hx hcross hspan).edge_support t).2

theorem cornerFunctional_spec {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    cornerFunctional f hx hcross hspan t ≠ 0 ∧
      cornerFunctional f hx hcross hspan t
          ((boundaryHullOrder f hx hcross hspan).vertex t) =
        cornerFunctional f hx hcross hspan t
          ((boundaryHullOrder f hx hcross hspan).vertex (Erdos957.cyclicSucc t)) ∧
      (∀ p ∈ boundaryPolygon n f.1 x,
        cornerFunctional f hx hcross hspan t p ≤
          cornerFunctional f hx hcross hspan t
            ((boundaryHullOrder f hx hcross hspan).vertex t)) ∧
      (∀ p ∈ Erdos957.hullVertices (boundaryPolygon n f.1 x),
        p ≠ (boundaryHullOrder f hx hcross hspan).vertex t →
        p ≠ (boundaryHullOrder f hx hcross hspan).vertex (Erdos957.cyclicSucc t) →
        cornerFunctional f hx hcross hspan t p <
          cornerFunctional f hx hcross hspan t
            ((boundaryHullOrder f hx hcross hspan).vertex t)) :=
  Classical.choose_spec ((boundaryHullOrder f hx hcross hspan).edge_support t).2

/-- Supporting value at the first endpoint of the polar hull edge. -/
def cornerLevel {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : ℝ :=
  cornerFunctional f hx hcross hspan t
    ((boundaryHullOrder f hx hcross hspan).vertex t)

/-- Homogeneous covector of the corner between the boundary edges at `t`
and `cyclicSucc t`. -/
def cornerVector {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : Vec3 :=
  liftedSupportVector x (cornerFunctional f hx hcross hspan t)
    (cornerLevel f hx hcross hspan t)

/-- Evaluation of the homogeneous corner covector on every normalized polar normal. -/
theorem polarPoint_dot_cornerVector {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) (i : I) :
    polarPoint n f.1 x i ⬝ᵥ cornerVector f hx hcross hspan t =
      cornerLevel f hx hcross hspan t -
        cornerFunctional f hx hcross hspan t (ownerPoint n f.1 x i) := by
  exact dot_liftedSupportVector (polarPoint_dot_witness hx i)
    (cornerFunctional f hx hcross hspan t)
    (cornerLevel f hx hcross hspan t)

/-- Every normalized normal lies in the closed homogeneous half-space
selected by the corner covector. -/
theorem polarPoint_dot_cornerVector_nonneg {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) (i : I) :
    0 ≤ polarPoint n f.1 x i ⬝ᵥ cornerVector f hx hcross hspan t := by
  let A := polarPoints n f.1 x
  let H := convexHull ℝ (A : Set Vec3)
  let V := polarVertices n f.1 x
  let y := cornerVector f hx hcross hspan t
  let Half : Set Vec3 := {z | 0 ≤ PolarFace.dotCLM y z}
  have hV : (V : Set Vec3) = H.extremePoints ℝ := by
    ext p
    exact mem_polarVertices
  have hcompact : IsCompact H :=
    Set.Finite.isCompact_convexHull ℝ A.finite_toSet
  have hkrein : closure (convexHull ℝ (V : Set Vec3)) = H := by
    rw [hV]
    exact closure_convexHull_extremePoints hcompact (convex_convexHull ℝ _)
  have hVHalf : (V : Set Vec3) ⊆ Half := by
    intro p hp
    have hpExtreme : p ∈ H.extremePoints ℝ := hV ▸ hp
    have hpA : p ∈ A := extremePoints_convexHull_subset hpExtreme
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hpA
    have hjOwner : j ∈ edgeOwners n f.1 := by
      apply mem_edgeOwners.mpr
      apply (edgeFeasible_faceEdgeCode_iff_extreme hx hcross j).2
      exact hpExtreme
    have hjPolygon : ownerPoint n f.1 x j ∈ boundaryPolygon n f.1 x :=
      Finset.mem_image.mpr ⟨j, hjOwner, rfl⟩
    have hmax := (cornerFunctional_spec f hx hcross hspan t).2.2.1
      (ownerPoint n f.1 x j) hjPolygon
    change 0 ≤ polarPoint n f.1 x j ⬝ᵥ y
    dsimp only [y]
    rw [polarPoint_dot_cornerVector]
    exact sub_nonneg.mpr hmax
  have hconvexHalf : Convex ℝ Half := by
    exact (convex_Ici 0).linear_preimage (PolarFace.dotCLM y).toLinearMap
  have hclosedHalf : IsClosed Half := by
    exact isClosed_Ici.preimage (PolarFace.dotCLM y).continuous
  have hconvexHull : convexHull ℝ (V : Set Vec3) ⊆ Half :=
    convexHull_min hVHalf hconvexHalf
  have hclosure : closure (convexHull ℝ (V : Set Vec3)) ⊆ Half :=
    closure_minimal hconvexHull hclosedHalf
  have hiH : polarPoint n f.1 x i ∈ H :=
    subset_convexHull ℝ (A : Set Vec3) (polarPoint_mem_polarPoints n f.1 x i)
  rw [hkrein] at hclosure
  exact hclosure hiH

/-- A cyclic hull order enumerates its hull-vertex subtype exactly. -/
noncomputable def hullIndexEquiv {A : Finset Erdos957.Point}
    (P : Erdos957.CyclicHullOrder A) :
    Fin (Erdos957.hullVertexCount A) ≃ {p // p ∈ Erdos957.hullVertices A} :=
  Equiv.ofBijective
    (fun i ↦ ⟨P.vertex i, P.vertex_mem_hullVertices i⟩)
    ⟨fun i j hij ↦ P.vertex.injective (congrArg Subtype.val hij),
      fun p ↦ by
        have hp : p.1 ∈ Set.range P.vertex := P.range_vertex.symm ▸ p.2
        obtain ⟨i, hi⟩ := hp
        exact ⟨i, Subtype.ext hi⟩⟩

/-- Identify hull vertices with polygon points when every generator is extreme. -/
def hullPointEquiv {A : Finset Erdos957.Point}
    (hA : Erdos957.hullVertices A = A) :
    {p // p ∈ Erdos957.hullVertices A} ≃ {p // p ∈ A} where
  toFun p := ⟨p.1, by simpa only [hA] using p.2⟩
  invFun p := ⟨p.1, by simpa only [hA] using p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cyclic index is equivalent to the actual supporting-line owner. -/
noncomputable def boundaryOwnerEquiv {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)) ≃
      {i // i ∈ edgeOwners n f.1} :=
  (hullIndexEquiv (boundaryHullOrder f hx hcross hspan)).trans
    ((hullPointEquiv (hullVertices_boundaryPolygon hx hcross)).trans
      (ownerPointEquiv hx hcross).symm)

/-- Supporting-line label at a cyclic boundary index. -/
def boundaryOwner {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : I :=
  (boundaryOwnerEquiv f hx hcross hspan t).1

lemma ownerPoint_boundaryOwner {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ownerPoint n f.1 x (boundaryOwner f hx hcross hspan t) =
      (boundaryHullOrder f hx hcross hspan).vertex t := by
  have h := (ownerPointEquiv hx hcross).apply_symm_apply
    ((hullPointEquiv (hullVertices_boundaryPolygon hx hcross))
      (hullIndexEquiv (boundaryHullOrder f hx hcross hspan) t))
  exact congrArg Subtype.val h

/-- The homogeneous corner covector vanishes on its first endpoint owner. -/
theorem polarPoint_dot_cornerVector_left_eq_zero {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    polarPoint n f.1 x (boundaryOwner f hx hcross hspan t) ⬝ᵥ
      cornerVector f hx hcross hspan t = 0 := by
  rw [polarPoint_dot_cornerVector,
    ownerPoint_boundaryOwner f hx hcross hspan t]
  simp [cornerLevel]

/-- The homogeneous corner covector vanishes on its successor endpoint owner. -/
theorem polarPoint_dot_cornerVector_right_eq_zero {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    polarPoint n f.1 x
        (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)) ⬝ᵥ
      cornerVector f hx hcross hspan t = 0 := by
  rw [polarPoint_dot_cornerVector,
    ownerPoint_boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)]
  change cornerLevel f hx hcross hspan t -
    cornerFunctional f hx hcross hspan t
      ((boundaryHullOrder f hx hcross hspan).vertex (Erdos957.cyclicSucc t)) = 0
  rw [cornerLevel, (cornerFunctional_spec f hx hcross hspan t).2.1]
  ring

/-- Vanishing of a normalized polar normal is equivalent to vanishing of
its underlying unoriented arrangement normal. -/
theorem polarPoint_dot_eq_zero_iff {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) (y : Vec3) :
    polarPoint n s x i ⬝ᵥ y = 0 ↔ n i ⬝ᵥ y = 0 := by
  rw [polarPoint, smul_dotProduct, orientedNormal_dot, smul_eq_mul, mul_eq_zero]
  have hinv : (polarDenom n s x i)⁻¹ ≠ 0 :=
    inv_ne_zero (polarDenom_ne_zero hx i)
  simp only [hinv, false_or]
  cases hsi : s i <;> simp [signed, hsi]

/-- The corner covector has the weak sign vector of the face. -/
theorem cornerVector_weaklyRealizes {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ∀ i, 0 ≤ signed (f.1 i) (n i ⬝ᵥ cornerVector f hx hcross hspan t) := by
  intro i
  have hp := polarPoint_dot_cornerVector_nonneg f hx hcross hspan t i
  rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hp
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr (polarDenom_pos hx i))).1 hp

/-- The first owner normal vanishes at the homogeneous corner. -/
theorem cornerVector_on_left_owner {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    n (boundaryOwner f hx hcross hspan t) ⬝ᵥ
      cornerVector f hx hcross hspan t = 0 :=
  (polarPoint_dot_eq_zero_iff hx _ _).1
    (polarPoint_dot_cornerVector_left_eq_zero f hx hcross hspan t)

/-- The successor owner normal vanishes at the homogeneous corner. -/
theorem cornerVector_on_right_owner {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    n (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)) ⬝ᵥ
      cornerVector f hx hcross hspan t = 0 :=
  (polarPoint_dot_eq_zero_iff hx _ _).1
    (polarPoint_dot_cornerVector_right_eq_zero f hx hcross hspan t)

lemma boundaryHull_third_ne_left {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    (boundaryHullOrder f hx hcross hspan).vertex
        (Erdos957.cyclicSucc (Erdos957.cyclicSucc t)) ≠
      (boundaryHullOrder f hx hcross hspan).vertex t := by
  intro heq
  have hturn := (boundaryHullOrder f hx hcross hspan).strict_turn t
  rw [heq] at hturn
  simp [Erdos957.orientedTurn] at hturn
  nlinarith

lemma boundaryHull_third_ne_right {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    (boundaryHullOrder f hx hcross hspan).vertex
        (Erdos957.cyclicSucc (Erdos957.cyclicSucc t)) ≠
      (boundaryHullOrder f hx hcross hspan).vertex (Erdos957.cyclicSucc t) := by
  intro heq
  have hturn := (boundaryHullOrder f hx hcross hspan).strict_turn t
  rw [heq] at hturn
  simp [Erdos957.orientedTurn] at hturn

/-- A third hull vertex is strictly positive on the lifted homogeneous corner covector. -/
theorem polarPoint_dot_cornerVector_third_pos {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    0 < polarPoint n f.1 x
        (boundaryOwner f hx hcross hspan
          (Erdos957.cyclicSucc (Erdos957.cyclicSucc t))) ⬝ᵥ
      cornerVector f hx hcross hspan t := by
  rw [polarPoint_dot_cornerVector,
    ownerPoint_boundaryOwner f hx hcross hspan
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc t))]
  apply sub_pos.mpr
  exact (cornerFunctional_spec f hx hcross hspan t).2.2.2
    ((boundaryHullOrder f hx hcross hspan).vertex
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc t)))
    ((boundaryHullOrder f hx hcross hspan).vertex_mem_hullVertices _)
    (boundaryHull_third_ne_left f hx hcross hspan t)
    (boundaryHull_third_ne_right f hx hcross hspan t)

/-- The lifted corner covector is nonzero, hence defines a genuine
projective and spherical arrangement vertex. -/
theorem cornerVector_ne_zero {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    cornerVector f hx hcross hspan t ≠ 0 := by
  intro hzero
  have hpos := polarPoint_dot_cornerVector_third_pos f hx hcross hspan t
  rw [hzero, dotProduct_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Unit-sphere normalization of the oriented homogeneous corner covector. -/
def cornerUnitVector {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : Vec3 :=
  (norm3 (cornerVector f hx hcross hspan t))⁻¹ •
    cornerVector f hx hcross hspan t

theorem norm3_cornerUnitVector {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    norm3 (cornerUnitVector f hx hcross hspan t) = 1 := by
  have hnorm : 0 < norm3 (cornerVector f hx hcross hspan t) :=
    norm_pos_iff.mpr (by
      simpa [norm3] using cornerVector_ne_zero f hx hcross hspan t)
  simp only [cornerUnitVector, norm3, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs]
  change |(norm3 (cornerVector f hx hcross hspan t))⁻¹| *
    norm3 (cornerVector f hx hcross hspan t) = 1
  rw [abs_of_pos (inv_pos.mpr hnorm)]
  change (norm3 (cornerVector f hx hcross hspan t))⁻¹ *
    norm3 (cornerVector f hx hcross hspan t) = 1
  exact inv_mul_cancel₀ hnorm.ne'

/-- The unit corner retains the face's weak sign vector. -/
theorem cornerUnitVector_weaklyRealizes {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ∀ i, 0 ≤ signed (f.1 i) (n i ⬝ᵥ cornerUnitVector f hx hcross hspan t) := by
  intro i
  have hnorm : 0 < norm3 (cornerVector f hx hcross hspan t) :=
    norm_pos_iff.mpr (by
      simpa [norm3] using cornerVector_ne_zero f hx hcross hspan t)
  simp only [cornerUnitVector, dotProduct_smul, smul_eq_mul, signed_mul]
  exact mul_nonneg (inv_pos.mpr hnorm).le
    (cornerVector_weaklyRealizes f hx hcross hspan t i)

/-- Oriented vertices of the spherical arrangement. -/
abbrev SphereVertex := {v : Vec3 // norm3 v = 1}

def orientedBoundaryVertex {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : SphereVertex :=
  ⟨cornerUnitVector f hx hcross hspan t,
    norm3_cornerUnitVector f hx hcross hspan t⟩

/-- Oriented projective corner obtained from the supporting polar hull edge. -/
noncomputable def cornerProjectiveVertex {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : ℙ ℝ Vec3 :=
  Projectivization.mk ℝ (cornerVector f hx hcross hspan t)
    (cornerVector_ne_zero f hx hcross hspan t)

theorem cornerProjectiveVertex_on_left {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryOwner f hx hcross hspan t))
      (cornerProjectiveVertex f hx hcross hspan t) := by
  rw [cornerProjectiveVertex, ProjectiveArrangement.onProjectiveLine_mk_iff]
  exact cornerVector_on_left_owner f hx hcross hspan t

theorem cornerProjectiveVertex_on_right {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)))
      (cornerProjectiveVertex f hx hcross hspan t) := by
  rw [cornerProjectiveVertex, ProjectiveArrangement.onProjectiveLine_mk_iff]
  exact cornerVector_on_right_owner f hx hcross hspan t

/-- Consecutive cyclic boundary positions have distinct supporting lines. -/
theorem boundaryOwner_ne_succ {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    boundaryOwner f hx hcross hspan t ≠
      boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t) := by
  intro heq
  apply (boundaryHullOrder f hx hcross hspan).consecutive_ne t
  rw [← ownerPoint_boundaryOwner f hx hcross hspan t,
    ← ownerPoint_boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t), heq]

/-- The projective arrangement vertex between two consecutive face edges. -/
noncomputable def boundaryProjectiveVertex {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ℙ ℝ Vec3 :=
  Projectivization.mk ℝ
    (n (boundaryOwner f hx hcross hspan t) ⨯₃
      n (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)))
    (hcross _ _ (boundaryOwner_ne_succ f hx hcross hspan t))

/-- The consecutive projective vertex lies on its first supporting line. -/
theorem boundaryProjectiveVertex_on_left {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryOwner f hx hcross hspan t))
      (boundaryProjectiveVertex f hx hcross hspan t) := by
  rw [boundaryProjectiveVertex, ProjectiveArrangement.onProjectiveLine_mk_iff]
  exact dot_self_cross _ _

/-- The consecutive projective vertex lies on its successor supporting line. -/
theorem boundaryProjectiveVertex_on_right {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    ProjectiveArrangement.OnProjectiveLine
      (n (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)))
      (boundaryProjectiveVertex f hx hcross hspan t) := by
  rw [boundaryProjectiveVertex, ProjectiveArrangement.onProjectiveLine_mk_iff]
  exact dot_cross_self _ _

/-- The oriented supporting covector represents the same projective point
as the cross product of its two consecutive owner normals. -/
theorem cornerProjectiveVertex_eq_boundaryProjectiveVertex {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    cornerProjectiveVertex f hx hcross hspan t =
      boundaryProjectiveVertex f hx hcross hspan t := by
  rw [cornerProjectiveVertex, boundaryProjectiveVertex,
    Projectivization.mk_eq_mk_iff_crossProduct_eq_zero]
  rw [cross_cross_eq_smul_sub_smul']
  have hright : cornerVector f hx hcross hspan t ⬝ᵥ
      n (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)) = 0 := by
    rw [dotProduct_comm]
    exact cornerVector_on_right_owner f hx hcross hspan t
  rw [hright, cornerVector_on_left_owner f hx hcross hspan t]
  simp

/-- Among extreme owner points, the only normals vanishing on a corner are
the two endpoints of its supporting hull edge. -/
theorem owner_eq_endpoint_of_dot_cornerVector_eq_zero {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)))
    (i : I) (hi : i ∈ edgeOwners n f.1)
    (hzero : n i ⬝ᵥ cornerVector f hx hcross hspan t = 0) :
    i = boundaryOwner f hx hcross hspan t ∨
      i = boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t) := by
  by_cases hil : i = boundaryOwner f hx hcross hspan t
  · exact Or.inl hil
  by_cases hir : i = boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)
  · exact Or.inr hir
  exfalso
  have hpzero : polarPoint n f.1 x i ⬝ᵥ cornerVector f hx hcross hspan t = 0 :=
    (polarPoint_dot_eq_zero_iff hx i _).2 hzero
  have hpi : ownerPoint n f.1 x i ∈
      Erdos957.hullVertices (boundaryPolygon n f.1 x) := by
    rw [hullVertices_boundaryPolygon hx hcross]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hneLeft : ownerPoint n f.1 x i ≠
      (boundaryHullOrder f hx hcross hspan).vertex t := by
    rw [← ownerPoint_boundaryOwner f hx hcross hspan t]
    exact (ownerPoint_injective hx hcross).ne hil
  have hneRight : ownerPoint n f.1 x i ≠
      (boundaryHullOrder f hx hcross hspan).vertex (Erdos957.cyclicSucc t) := by
    rw [← ownerPoint_boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)]
    exact (ownerPoint_injective hx hcross).ne hir
  have hlt := (cornerFunctional_spec f hx hcross hspan t).2.2.2
    (ownerPoint n f.1 x i) hpi hneLeft hneRight
  rw [polarPoint_dot_cornerVector] at hpzero
  simp only [cornerLevel] at hpzero
  linarith

/-- The left owner of one corner is strictly inside the next corner's
selected half-space. -/
theorem polarPoint_dot_next_cornerVector_pos {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    0 < polarPoint n f.1 x (boundaryOwner f hx hcross hspan t) ⬝ᵥ
      cornerVector f hx hcross hspan (Erdos957.cyclicSucc t) := by
  rw [polarPoint_dot_cornerVector,
    ownerPoint_boundaryOwner f hx hcross hspan t]
  apply sub_pos.mpr
  exact (cornerFunctional_spec f hx hcross hspan (Erdos957.cyclicSucc t)).2.2.2
    ((boundaryHullOrder f hx hcross hspan).vertex t)
    ((boundaryHullOrder f hx hcross hspan).vertex_mem_hullVertices t)
    ((boundaryHullOrder f hx hcross hspan).consecutive_ne t)
    (boundaryHull_third_ne_left f hx hcross hspan t).symm

theorem left_owner_dot_next_cornerVector_ne_zero {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    n (boundaryOwner f hx hcross hspan t) ⬝ᵥ
      cornerVector f hx hcross hspan (Erdos957.cyclicSucc t) ≠ 0 := by
  have hp := polarPoint_dot_next_cornerVector_pos f hx hcross hspan t
  rw [polarPoint, smul_dotProduct, orientedNormal_dot, smul_eq_mul] at hp
  have hsigned : 0 < signed (f.1 (boundaryOwner f hx hcross hspan t))
      (n (boundaryOwner f hx hcross hspan t) ⬝ᵥ
        cornerVector f hx hcross hspan (Erdos957.cyclicSucc t)) :=
    (mul_pos_iff_of_pos_left
      (inv_pos.mpr (polarDenom_pos hx (boundaryOwner f hx hcross hspan t)))).1 hp
  intro hzero
  rw [hzero] at hsigned
  cases f.1 (boundaryOwner f hx hcross hspan t) <;> simp [signed] at hsigned

/-- Consecutive projective corner vertices are distinct. -/
theorem cornerProjectiveVertex_ne_succ {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    cornerProjectiveVertex f hx hcross hspan t ≠
      cornerProjectiveVertex f hx hcross hspan (Erdos957.cyclicSucc t) := by
  intro heq
  rw [cornerProjectiveVertex, cornerProjectiveVertex,
    Projectivization.mk_eq_mk_iff'] at heq
  obtain ⟨a, ha⟩ := heq
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at ha
    exact cornerVector_ne_zero f hx hcross hspan t ha.symm
  have hdot := congrArg
    (fun z : Vec3 ↦ n (boundaryOwner f hx hcross hspan t) ⬝ᵥ z) ha
  rw [dotProduct_smul, smul_eq_mul,
    cornerVector_on_left_owner f hx hcross hspan t] at hdot
  exact mul_ne_zero ha0
    (left_owner_dot_next_cornerVector_ne_zero f hx hcross hspan t) hdot

theorem boundaryProjectiveVertex_ne_succ {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    boundaryProjectiveVertex f hx hcross hspan t ≠
      boundaryProjectiveVertex f hx hcross hspan (Erdos957.cyclicSucc t) := by
  rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex f hx hcross hspan t,
    ← cornerProjectiveVertex_eq_boundaryProjectiveVertex f hx hcross hspan
      (Erdos957.cyclicSucc t)]
  exact cornerProjectiveVertex_ne_succ f hx hcross hspan t

/-- Distinct cyclic corners give distinct projective arrangement vertices. -/
theorem boundaryProjectiveVertex_injective {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Function.Injective (boundaryProjectiveVertex f hx hcross hspan) := by
  intro t u htu
  have hcorner : cornerProjectiveVertex f hx hcross hspan t =
      cornerProjectiveVertex f hx hcross hspan u := by
    rw [cornerProjectiveVertex_eq_boundaryProjectiveVertex,
      cornerProjectiveVertex_eq_boundaryProjectiveVertex]
    exact htu
  rw [cornerProjectiveVertex, cornerProjectiveVertex,
    Projectivization.mk_eq_mk_iff'] at hcorner
  obtain ⟨a, ha⟩ := hcorner
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at ha
    exact cornerVector_ne_zero f hx hcross hspan t ha.symm
  have transferZero (i : I)
      (hi : n i ⬝ᵥ cornerVector f hx hcross hspan t = 0) :
      n i ⬝ᵥ cornerVector f hx hcross hspan u = 0 := by
    have hdot := congrArg (fun z : Vec3 ↦ n i ⬝ᵥ z) ha
    rw [dotProduct_smul, smul_eq_mul, hi] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left ha0
  have htOwner := owner_eq_endpoint_of_dot_cornerVector_eq_zero f hx hcross hspan u
    (boundaryOwner f hx hcross hspan t)
    (boundaryOwnerEquiv f hx hcross hspan t).2
    (transferZero _ (cornerVector_on_left_owner f hx hcross hspan t))
  have hsOwner := owner_eq_endpoint_of_dot_cornerVector_eq_zero f hx hcross hspan u
    (boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t))
    (boundaryOwnerEquiv f hx hcross hspan (Erdos957.cyclicSucc t)).2
    (transferZero _ (cornerVector_on_right_owner f hx hcross hspan t))
  have index_eq_of_owner_eq {v w}
      (hvw : boundaryOwner f hx hcross hspan v =
        boundaryOwner f hx hcross hspan w) : v = w := by
    apply (boundaryOwnerEquiv f hx hcross hspan).injective
    exact Subtype.ext hvw
  rcases htOwner with htLeft | htRight
  · rcases hsOwner with hsLeft | hsRight
    · exact False.elim <| (boundaryOwner_ne_succ f hx hcross hspan t)
        (htLeft.trans hsLeft.symm)
    · exact index_eq_of_owner_eq htLeft
  · rcases hsOwner with hsLeft | hsRight
    · have htu' : t = Erdos957.cyclicSucc u := index_eq_of_owner_eq htRight
      have hstu : Erdos957.cyclicSucc t = u := index_eq_of_owner_eq hsLeft
      have hcycle : Erdos957.cyclicSucc (Erdos957.cyclicSucc u) = u := by
        calc
          Erdos957.cyclicSucc (Erdos957.cyclicSucc u) =
              Erdos957.cyclicSucc t := congrArg Erdos957.cyclicSucc htu'.symm
          _ = u := hstu
      exfalso
      apply boundaryHull_third_ne_left f hx hcross hspan u
      exact congrArg (boundaryHullOrder f hx hcross hspan).vertex hcycle
    · exact False.elim <| (boundaryOwner_ne_succ f hx hcross hspan t)
        (htRight.trans hsRight.symm)

/-- The strict edge at a cyclic boundary index, with its owner preserved. -/
def boundaryEdge {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) : StrictEdge n :=
  edgeOfOwner (boundaryOwnerEquiv f hx hcross hspan t)

@[simp] theorem boundaryEdge_owner {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    (boundaryEdge f hx hcross hspan t).1.1 =
      boundaryOwner f hx hcross hspan t := rfl

theorem boundaryEdge_mem_faceEdges {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    boundaryEdge f hx hcross hspan t ∈ faceEdges n f := by
  rw [mem_faceEdges_iff]
  intro j
  rfl

/-- The cyclic boundary index is exactly equivalent to the incident strict edge. -/
noncomputable def boundaryEdgeEquiv {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)) ≃
      {e // e ∈ faceEdges n f} :=
  (boundaryOwnerEquiv f hx hcross hspan).trans (ownerFaceEdgeEquiv f)

@[simp] theorem boundaryEdgeEquiv_val {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x))) :
    (boundaryEdgeEquiv f hx hcross hspan t).1 =
      boundaryEdge f hx hcross hspan t := rfl

/-- The owner-preserving cyclic list of all strict edges around the face. -/
noncomputable def faceBoundary {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) : List (StrictEdge n) :=
  List.ofFn fun t ↦ boundaryEdge f hx hcross hspan t

theorem faceBoundary_nodup {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    (faceBoundary f hx hcross hspan).Nodup := by
  rw [faceBoundary, List.nodup_ofFn]
  intro i j hij
  apply (boundaryEdgeEquiv f hx hcross hspan).injective
  apply Subtype.ext
  simpa using hij

theorem faceBoundary_toFinset {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    (faceBoundary f hx hcross hspan).toFinset = faceEdges n f := by
  ext e
  rw [List.mem_toFinset, faceBoundary, List.mem_ofFn']
  constructor
  · rintro ⟨t, rfl⟩
    exact boundaryEdge_mem_faceEdges f hx hcross hspan t
  · intro he
    obtain ⟨t, ht⟩ := (boundaryEdgeEquiv f hx hcross hspan).surjective ⟨e, he⟩
    exact ⟨t, congrArg Subtype.val ht⟩

@[simp] theorem faceBoundary_length {n : I → Vec3}
    (f : StrictFace n) {x : Vec3} (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    (faceBoundary f hx hcross hspan).length =
      Erdos957.hullVertexCount (boundaryPolygon n f.1 x) := by
  simp [faceBoundary]

end

end Erdos735.SignVector.PolarBoundaryOrder
