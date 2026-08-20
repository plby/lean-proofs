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

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The blue cellulation used in Erdős Problem 735

This file packages the finite incidence data needed for the initial-charge
identity in the Ackerman--Buchin--Knauer--Pinchasi--Rote discharging proof.
-/

namespace Erdos735

open scoped BigOperators

universe uV uE uF

/-- A finite blue cellulation of the sphere, retaining exactly the finite
incidence information used by the initial-charge argument. A vertex where
`k` blue great circles meet has `2 * k` incident graph edges. A face boundary
is stored as a cyclic list; its choice of starting edge is immaterial here. -/
structure BlueCellulation
    (Vertex : Type uV) (Edge : Type uE) (Face : Type uF)
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face] where
  blueMultiplicity : Vertex → ℕ
  vertexEdges : Vertex → Finset Edge
  edgeVertices : Edge → Finset Vertex
  vertexEdge_iff : ∀ v e, e ∈ vertexEdges v ↔ v ∈ edgeVertices e
  edgeVertices_card : ∀ e, (edgeVertices e).card = 2
  vertexEdges_card : ∀ v, (vertexEdges v).card = 2 * blueMultiplicity v
  blueMultiplicity_two_le : ∀ v, 2 ≤ blueMultiplicity v
  faceBoundary : Face → List Edge
  faceBoundary_nodup : ∀ f, (faceBoundary f).Nodup
  edgeFaces : Edge → Finset Face
  faceEdge_iff : ∀ f e, e ∈ faceBoundary f ↔ f ∈ edgeFaces e
  edgeFaces_card : ∀ e, (edgeFaces e).card = 2
  faceDegree_three_le : ∀ f, 3 ≤ (faceBoundary f).length
  euler_sphere :
    (Fintype.card Vertex : ℤ) - (Fintype.card Edge : ℤ) +
        (Fintype.card Face : ℤ) = 2

namespace BlueCellulation

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]

variable (C : BlueCellulation Vertex Edge Face)

/-- The number of edges of a polygonal face. -/
def faceDegree (f : Face) : ℕ := (C.faceBoundary f).length

/-- The number `t_k` of blue vertices at which exactly `k` circles meet. -/
def vertexMultiplicityCount (k : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Vertex => C.blueMultiplicity v = k).card

/-- The number `f_k` of blue polygonal faces of degree `k`. -/
def faceDegreeCount (k : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Face => C.faceDegree f = k).card

/-- The finite set of multiplicities which actually occur. -/
def occurringVertexMultiplicities : Finset ℕ :=
  Finset.univ.image C.blueMultiplicity

/-- The finite set of face degrees which actually occur. -/
def occurringFaceDegrees : Finset ℕ :=
  Finset.univ.image C.faceDegree

theorem two_le_of_mem_occurringVertexMultiplicities {k : ℕ}
    (hk : k ∈ C.occurringVertexMultiplicities) : 2 ≤ k := by
  rcases Finset.mem_image.mp hk with ⟨v, -, rfl⟩
  exact C.blueMultiplicity_two_le v

theorem three_le_of_mem_occurringFaceDegrees {k : ℕ}
    (hk : k ∈ C.occurringFaceDegrees) : 3 ≤ k := by
  rcases Finset.mem_image.mp hk with ⟨f, -, rfl⟩
  exact C.faceDegree_three_le f

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
    _ = ∑ b, ∑ a, if b ∈ row a then 1 else 0 := by
      rw [Finset.sum_comm]
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

/-- Counting vertex-edge incidences first by vertices and then by edges. -/
theorem sum_vertexEdge_card :
    (∑ v, (C.vertexEdges v).card) = 2 * Fintype.card Edge := by
  rw [sum_card_incidence C.vertexEdges C.edgeVertices C.vertexEdge_iff]
  simp [C.edgeVertices_card, mul_comm]

/-- Counting face-edge incidences first by faces and then by edges. -/
theorem sum_faceDegree :
    (∑ f, C.faceDegree f) = 2 * Fintype.card Edge := by
  calc
    (∑ f, C.faceDegree f) = ∑ f, (C.faceBoundary f).toFinset.card := by
      apply Finset.sum_congr rfl
      intro f _
      simpa [faceDegree] using (List.toFinset_card_of_nodup (C.faceBoundary_nodup f)).symm
    _ = ∑ e, (C.edgeFaces e).card := by
      apply sum_card_incidence
      intro f e
      simpa using C.faceEdge_iff f e
    _ = 2 * Fintype.card Edge := by
      simp [C.edgeFaces_card, mul_comm]

/-- Since the graph degree at a `k`-fold crossing is `2 * k`, incidence
double-counting gives `sum k * t_k = E` in the object-indexed form. -/
theorem sum_blueMultiplicity :
    (∑ v, C.blueMultiplicity v) = Fintype.card Edge := by
  have h := C.sum_vertexEdge_card
  simp_rw [C.vertexEdges_card] at h
  have h' : 2 * (∑ v, C.blueMultiplicity v) = 2 * Fintype.card Edge := by
    rw [Finset.mul_sum]
    simpa [mul_comm] using h
  omega

/-- Initial charge on a crossing vertex. -/
def vertexCharge (v : Vertex) : ℤ := (C.blueMultiplicity v : ℤ) - 3

/-- Initial charge on a face. -/
def faceCharge (f : Face) : ℤ := (C.faceDegree f : ℤ) - 3

/-- Grouping vertices according to their blue multiplicity turns the
object-indexed charge sum into `sum (k - 3) * t_k`. -/
theorem sum_vertexCharge_eq_counted :
    (∑ v, C.vertexCharge v) =
      ∑ k ∈ C.occurringVertexMultiplicities,
        ((k : ℤ) - 3) * (C.vertexMultiplicityCount k : ℤ) := by
  calc
    (∑ v, C.vertexCharge v) =
        ∑ k ∈ C.occurringVertexMultiplicities,
          ∑ v ∈ Finset.univ with C.blueMultiplicity v = k, C.vertexCharge v := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro v hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    _ = ∑ k ∈ C.occurringVertexMultiplicities,
          ((k : ℤ) - 3) * (C.vertexMultiplicityCount k : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ v with C.blueMultiplicity v = k, C.vertexCharge v) =
            ∑ v ∈ (Finset.univ.filter fun v : Vertex =>
              C.blueMultiplicity v = k), ((k : ℤ) - 3) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hvk : C.blueMultiplicity v = k := (Finset.mem_filter.mp hv).2
          simp [vertexCharge, hvk]
        _ = ((k : ℤ) - 3) * (C.vertexMultiplicityCount k : ℤ) := by
          simp [vertexMultiplicityCount, mul_comm]
          ring

/-- Grouping polygonal faces according to their degree turns the
object-indexed charge sum into `sum (k - 3) * f_k`. -/
theorem sum_faceCharge_eq_counted :
    (∑ f, C.faceCharge f) =
      ∑ k ∈ C.occurringFaceDegrees,
        ((k : ℤ) - 3) * (C.faceDegreeCount k : ℤ) := by
  calc
    (∑ f, C.faceCharge f) =
        ∑ k ∈ C.occurringFaceDegrees,
          ∑ f ∈ Finset.univ with C.faceDegree f = k, C.faceCharge f := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro f hf
      exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    _ = ∑ k ∈ C.occurringFaceDegrees,
          ((k : ℤ) - 3) * (C.faceDegreeCount k : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ f with C.faceDegree f = k, C.faceCharge f) =
            ∑ f ∈ (Finset.univ.filter fun f : Face => C.faceDegree f = k),
              ((k : ℤ) - 3) := by
          apply Finset.sum_congr rfl
          intro f hf
          have hfk : C.faceDegree f = k := (Finset.mem_filter.mp hf).2
          simp [faceCharge, hfk]
        _ = ((k : ℤ) - 3) * (C.faceDegreeCount k : ℤ) := by
          simp [faceDegreeCount, mul_comm]
          ring

/-- Euler and the two incidence counts give total initial charge `-6`. -/
theorem total_initial_charge :
    (∑ v, C.vertexCharge v) + (∑ f, C.faceCharge f) = -6 := by
  have hmultNat := C.sum_blueMultiplicity
  have hfaceNat := C.sum_faceDegree
  have hmult : (∑ v, (C.blueMultiplicity v : ℤ)) = (Fintype.card Edge : ℤ) := by
    exact_mod_cast hmultNat
  have hface : (∑ f, (C.faceDegree f : ℤ)) = 2 * (Fintype.card Edge : ℤ) := by
    exact_mod_cast hfaceNat
  simp only [vertexCharge, faceCharge, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  rw [hmult, hface]
  linarith [C.euler_sphere]

/-- The ABKPR charge equation in its customary histogram notation:
`t_k` counts `k`-fold blue vertices and `f_k` counts blue `k`-gons.
Only occurring degrees are summed, so these are genuine finite sums. -/
theorem charge_identity :
    (∑ k ∈ C.occurringVertexMultiplicities,
        ((k : ℤ) - 3) * (C.vertexMultiplicityCount k : ℤ)) +
      (∑ k ∈ C.occurringFaceDegrees,
        ((k : ℤ) - 3) * (C.faceDegreeCount k : ℤ)) = -6 := by
  rw [← C.sum_vertexCharge_eq_counted, ← C.sum_faceCharge_eq_counted]
  exact C.total_initial_charge

end BlueCellulation

end Erdos735
