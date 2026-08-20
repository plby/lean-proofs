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

import Mathlib

/-!
# Finite great-circle arrangements

This file supplies the stable finite and topological foundations for the spherical
arrangement used in the proof of Erdős Problem 735.  A great circle is represented by a
nonzero normal vector in `Fin 3 → ℝ`; intersections are normalized cross products.

The vertices are an explicit finite set.  Open arcs and faces are defined intrinsically as
connected components of a punctured great circle and of the arrangement complement.  The
file also proves the line--vertex incidence double count and the Euler invariance of the
local count changes made when a further great circle is inserted.  Turning the topological
components into a complete finite cellulation requires additional geometric arguments.
-/

open scoped BigOperators Matrix RealInnerProductSpace
open Set Topology Matrix

namespace Erdos735

abbrev Vec3 := Fin 3 → ℝ

noncomputable def norm3 (v : Vec3) : ℝ := ‖WithLp.toLp 2 v‖

noncomputable def normalizedCross (n m : Vec3) : Vec3 :=
  (norm3 (n ⨯₃ m))⁻¹ • (n ⨯₃ m)

noncomputable def vertices (N : Finset Vec3) : Finset Vec3 :=
  N.offDiag.image fun nm ↦ normalizedCross nm.1 nm.2

def onCircle (n p : Vec3) : Prop := n ⬝ᵥ p = 0

lemma normalizedCross_onCircle_left (n m : Vec3) :
    onCircle n (normalizedCross n m) := by
  simp [onCircle, normalizedCross]

lemma normalizedCross_onCircle_right (n m : Vec3) :
    onCircle m (normalizedCross n m) := by
  simp [onCircle, normalizedCross]

lemma norm3_normalizedCross {n m : Vec3} (hcross : n ⨯₃ m ≠ 0) :
    norm3 (normalizedCross n m) = 1 := by
  simp only [norm3, normalizedCross, WithLp.toLp_smul]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (by simpa using hcross)

lemma normalizedCross_swap (n m : Vec3) :
    normalizedCross m n = -normalizedCross n m := by
  have hcross : m ⨯₃ n = -(n ⨯₃ m) := (cross_anticomm n m).symm
  have hnorm : norm3 (m ⨯₃ n) = norm3 (n ⨯₃ m) := by
    simp only [norm3, hcross, WithLp.toLp_neg, norm_neg]
  unfold normalizedCross
  rw [hnorm, hcross]
  exact smul_neg _ _

lemma mem_vertices_iff {N : Finset Vec3} {p : Vec3} :
    p ∈ vertices N ↔
      ∃ n ∈ N, ∃ m ∈ N, n ≠ m ∧ p = normalizedCross n m := by
  classical
  simp only [vertices, Finset.mem_image, Finset.mem_offDiag, Prod.exists]
  aesop

lemma neg_mem_vertices_iff {N : Finset Vec3} {p : Vec3} :
    -p ∈ vertices N ↔ p ∈ vertices N := by
  constructor
  · intro hp
    obtain ⟨n, hn, m, hm, hne, hneg⟩ := mem_vertices_iff.mp hp
    have h := congrArg Neg.neg hneg
    simp only [neg_neg] at h
    rw [← normalizedCross_swap n m] at h
    exact mem_vertices_iff.mpr ⟨m, hm, n, hn, hne.symm, h⟩
  · intro hp
    obtain ⟨n, hn, m, hm, hne, rfl⟩ := mem_vertices_iff.mp hp
    exact mem_vertices_iff.mpr
      ⟨m, hm, n, hn, hne.symm, (normalizedCross_swap n m).symm⟩

def PairwiseIndependent (N : Finset Vec3) : Prop :=
  ∀ n ∈ N, ∀ m ∈ N, n ≠ m → n ⨯₃ m ≠ 0

lemma norm3_eq_one_of_mem_vertices {N : Finset Vec3}
    (hN : PairwiseIndependent N) {p : Vec3} (hp : p ∈ vertices N) :
    norm3 p = 1 := by
  obtain ⟨n, hn, m, hm, hne, rfl⟩ := mem_vertices_iff.mp hp
  exact norm3_normalizedCross (hN n hn m hm hne)

lemma exists_two_incident_circles_of_mem_vertices {N : Finset Vec3}
    {p : Vec3} (hp : p ∈ vertices N) :
    ∃ n ∈ N, ∃ m ∈ N, n ≠ m ∧ onCircle n p ∧ onCircle m p := by
  obtain ⟨n, hn, m, hm, hne, rfl⟩ := mem_vertices_iff.mp hp
  exact ⟨n, hn, m, hm, hne, normalizedCross_onCircle_left n m,
    normalizedCross_onCircle_right n m⟩

abbrev UnitPoint := {p : Vec3 // norm3 p = 1}

def vertexUnitPoints (N : Finset Vec3) : Set UnitPoint :=
  {p | p.1 ∈ vertices N}

def openCircleCarrier (N : Finset Vec3) (n : Vec3) : Set UnitPoint :=
  {p | onCircle n p.1 ∧ p.1 ∉ vertices N}

abbrev OpenArc (N : Finset Vec3) (n : Vec3) :=
  ConnectedComponents (openCircleCarrier N n)

def faceCarrier (N : Finset Vec3) : Set UnitPoint :=
  {p | ∀ n ∈ N, ¬ onCircle n p.1}

abbrev Face (N : Finset Vec3) := ConnectedComponents (faceCarrier N)

noncomputable def multiplicity (N : Finset Vec3) (p : Vec3) : ℕ :=
  by classical exact (N.filter fun n ↦ onCircle n p).card

noncomputable def circleVertexCount (N : Finset Vec3) (n : Vec3) : ℕ :=
  by classical exact ((vertices N).filter fun p ↦ onCircle n p).card

theorem two_le_multiplicity_of_mem_vertices {N : Finset Vec3} {p : Vec3}
    (hp : p ∈ vertices N) : 2 ≤ multiplicity N p := by
  classical
  obtain ⟨n, hn, m, hm, hne, hnp, hmp⟩ :=
    exists_two_incident_circles_of_mem_vertices hp
  have hsubset : {n, m} ⊆ N.filter fun q ↦ onCircle q p := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hn, hnp⟩
    · exact Finset.mem_filter.mpr ⟨hm, hmp⟩
  have hcard := Finset.card_le_card hsubset
  simpa [multiplicity, hne] using hcard

theorem incidence_double_count (N : Finset Vec3) :
    ∑ p ∈ vertices N, multiplicity N p =
      ∑ n ∈ N, circleVertexCount N n := by
  classical
  simp only [multiplicity, circleVertexCount, Finset.card_filter]
  exact Finset.sum_comm

/-- Count changes made by successively inserting great circles into a spherical arrangement. -/
inductive CellCountConstruction : (vertices edges faces : ℕ) → Prop
  | twoCircles : CellCountConstruction 2 4 4
  | insert {v e f u k : ℕ} :
      CellCountConstruction v e f →
      CellCountConstruction (v + u) (e + u + k) (f + k)

namespace CellCountConstruction

/-- Euler's formula is invariant under the exact local count changes made by inserting a
further great circle. -/
theorem euler {v e f : ℕ} (h : CellCountConstruction v e f) :
    v + f = e + 2 := by
  induction h with
  | twoCircles => decide
  | insert h ih => omega

end CellCountConstruction

/-- The edge count predicted by punctured-circle components. -/
noncomputable def predictedEdgeCount (N : Finset Vec3) : ℕ :=
  ∑ n ∈ N, circleVertexCount N n

theorem predictedEdgeCount_eq_sum_multiplicity (N : Finset Vec3) :
    predictedEdgeCount N = ∑ p ∈ vertices N, multiplicity N p := by
  exact (incidence_double_count N).symm

end Erdos735
