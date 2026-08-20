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

import ErdosProblems.Erdos735.ConcretePolarEndpointRestriction
import ErdosProblems.Erdos735.ConcretePolarLocalSector
import ErdosProblems.Erdos735.Discharging4Concrete
import Mathlib.Tactic.FinCases

/-!
# Existence of a non-triangular Stage-4 flank

This file proves the local part of flank existence which does not involve
the failed-Fano exception.  Every cyclic flank of an evil triangle is
either a triangle or a zero-diagonal quadrangle.  Degree at least five
would make it a Stage-3 donor, while in degree four endpoint restriction
rules out every red chord.
-/

open Classical
noncomputable section

namespace Erdos735
namespace ABKPR

private theorem fin_four_chord_hits_edge
    (i a b : Fin 4) (hab : a ≠ b)
    (hba : b ≠ cyclicSucc (by decide) a)
    (hab' : a ≠ cyclicSucc (by decide) b) :
    a = i ∨ a = cyclicSucc (by decide) i ∨
      b = i ∨ b = cyclicSucc (by decide) i := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [cyclicSucc] at hab hba hab' ⊢

namespace Data

universe uV uEd uF

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}

/-- In a quadrangle, an edge whose opposite face is bad leaves no room for
a nonadjacent red chord: endpoint restriction frees the two endpoints of
that edge, and the other two vertices are adjacent. -/
theorem zeroDiagonal_of_degree_four_of_bad_across
    (hrest : A.EndpointRestriction) {f : Face}
    (hfour : C.faceDegree f = 4)
    (i : Fin (C.faceDegree f))
    (hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1) :
    A.IsZeroDiagonalQuadrangle f := by
  refine ⟨hfour, Finset.card_eq_zero.mpr ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hdistinct := A.redChord_distinct f p hp
  have hnon := A.redChord_nonadjacent f p hp
  have hfree := hrest f i hbad
  have hp₁ : p.1 ∈ A.redEndpoints f :=
    (A.redEndpoint_iff f p.1).mpr ⟨p, hp, Or.inl rfl⟩
  have hp₂ : p.2 ∈ A.redEndpoints f :=
    (A.redEndpoint_iff f p.2).mpr ⟨p, hp, Or.inr rfl⟩
  let cast : Fin (C.faceDegree f) → Fin 4 := Fin.cast hfour
  have hcast_inj : Function.Injective cast := Fin.cast_injective hfour
  have hsucc (x : Fin (C.faceDegree f)) :
      cast (faceSucc C f x) = cyclicSucc (by decide) (cast x) := by
    apply Fin.ext
    simp [cast, faceSucc, cyclicSucc, hfour]
  have hhit := fin_four_chord_hits_edge (cast i) (cast p.1) (cast p.2)
    (fun h ↦ hdistinct (hcast_inj h))
    (fun h ↦ hnon.1 (hcast_inj (h.trans (hsucc p.1).symm)))
    (fun h ↦ hnon.2 (hcast_inj (h.trans (hsucc p.2).symm)))
  rcases hhit with h | h | h | h
  · exact hfree.1 (hcast_inj h.symm ▸ hp₁)
  · exact hfree.2 (hcast_inj ((hsucc i).trans h.symm) ▸ hp₁)
  · exact hfree.1 (hcast_inj h.symm ▸ hp₂)
  · exact hfree.2 (hcast_inj ((hsucc i).trans h.symm) ▸ hp₂)

/-- Adjacent edges of a face retain their common boundary vertex on the
two opposite faces. -/
theorem exists_common_boundaryVertex_across_of_cyclicAdjacent
    (q : Face) (i j : Fin (C.faceDegree q))
    (hadj : CyclicAdjacentIndex (C := C) i j) :
    ∃ pi : Fin (C.faceDegree (A.across ⟨q, i⟩).1),
      ∃ pj : Fin (C.faceDegree (A.across ⟨q, j⟩).1),
        A.boundaryVertex (A.across ⟨q, i⟩).1 pi =
          A.boundaryVertex (A.across ⟨q, j⟩).1 pj := by
  let v : Vertex := if faceSucc C q i = j then
      A.boundaryVertex q j else A.boundaryVertex q i
  have hvi : v ∈ C.edgeVertices (A.boundaryEdge q i) := by
    rw [A.boundaryEdge_vertices q i]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : faceSucc C q i = j
    · right
      simp [v, h]
    · left
      simp [v, h]
  have hvj : v ∈ C.edgeVertices (A.boundaryEdge q j) := by
    rw [A.boundaryEdge_vertices q j]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : faceSucc C q i = j
    · left
      simp [v, h]
    · right
      have hji : faceSucc C q j = i := hadj.resolve_left h
      simp [v, h, hji]
  have hvi' : v ∈ C.edgeVertices
      (A.boundaryEdge (A.across ⟨q, i⟩).1 (A.across ⟨q, i⟩).2) := by
    rw [← A.across_sameEdge ⟨q, i⟩]
    exact hvi
  have hvj' : v ∈ C.edgeVertices
      (A.boundaryEdge (A.across ⟨q, j⟩).1 (A.across ⟨q, j⟩).2) := by
    rw [← A.across_sameEdge ⟨q, j⟩]
    exact hvj
  rw [A.boundaryEdge_vertices] at hvi' hvj'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvi' hvj'
  rcases hvi' with hi | hi <;> rcases hvj' with hj | hj
  · exact ⟨_, _, hi.symm.trans hj⟩
  · exact ⟨_, _, hi.symm.trans hj⟩
  · exact ⟨_, _, hi.symm.trans hj⟩
  · exact ⟨_, _, hi.symm.trans hj⟩

/-- A flank of degree at least five would have donated to its evil
triangle in Stage 3. -/
theorem donationGeometry_flank_of_degree_five
    (e : A.EvilFace)
    (j : Fin (C.faceDegree (A.across (A.evilDart e)).1))
    (hadj : CyclicAdjacentIndex (C := C) (A.across (A.evilDart e)).2 j)
    (hfive : 5 ≤ C.faceDegree
      (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1) :
    A.DonationGeometry
      (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1 e.1 := by
  let bad := A.across (A.evilDart e)
  let flankDart := A.across ⟨bad.1, j⟩
  have hit : A.evilIndex e ∈ A.badNeighborIndices e.1 := by
    rw [A.badNeighborIndices_eq_singleton e]
    simp
  refine ⟨e.2.1, hfive, A.evilIndex e, hit, ?_, ?_⟩
  · refine ⟨flankDart.2, j, ?_⟩
    exact (A.across_sameEdge ⟨bad.1, j⟩).symm
  · let v : Vertex := if faceSucc C bad.1 bad.2 = j then
        A.boundaryVertex bad.1 j else A.boundaryVertex bad.1 bad.2
    have hvbad : v ∈ C.edgeVertices (A.boundaryEdge bad.1 bad.2) := by
      rw [A.boundaryEdge_vertices bad.1 bad.2]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : faceSucc C bad.1 bad.2 = j
      · right
        simp [v, h]
      · left
        simp [v, h]
    have hvflankEdge : v ∈ C.edgeVertices (A.boundaryEdge bad.1 j) := by
      rw [A.boundaryEdge_vertices bad.1 j]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : faceSucc C bad.1 bad.2 = j
      · left
        simp [v, h]
      · right
        have hji : faceSucc C bad.1 j = bad.2 := hadj.resolve_left h
        simp [v, h, hji]
    have hve : v ∈ C.edgeVertices
        (A.boundaryEdge e.1 (A.evilIndex e)) := by
      change v ∈ C.edgeVertices
        (A.boundaryEdge (A.evilDart e).1 (A.evilDart e).2)
      rw [A.across_sameEdge (A.evilDart e)]
      simpa only [bad] using hvbad
    have hvf : v ∈ C.edgeVertices
        (A.boundaryEdge flankDart.1 flankDart.2) := by
      dsimp only [flankDart]
      rw [← A.across_sameEdge ⟨bad.1, j⟩]
      exact hvflankEdge
    rw [A.boundaryEdge_vertices] at hve hvf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve hvf
    rcases hvf with hf | hf <;> rcases hve with he | he
    · exact ⟨_, _, hf.symm.trans he⟩
    · exact ⟨_, _, hf.symm.trans he⟩
    · exact ⟨_, _, hf.symm.trans he⟩
    · exact ⟨_, _, hf.symm.trans he⟩

/-- Every literal cyclic flank of an evil triangle is either triangular or
a zero-diagonal quadrangle. -/
theorem flank_triangle_or_zeroDiagonal
    (hrest : A.EndpointRestriction)
    (e : A.EvilFace)
    (j : Fin (C.faceDegree (A.across (A.evilDart e)).1))
    (hadj : CyclicAdjacentIndex (C := C) (A.across (A.evilDart e)).2 j) :
    C.faceDegree (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1 = 3 ∨
      A.IsZeroDiagonalQuadrangle
        (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1 := by
  let bad := A.across (A.evilDart e)
  let flank := A.across ⟨bad.1, j⟩
  have hthree : 3 ≤ C.faceDegree flank.1 := by
    simpa only [BlueCellulation.faceDegree] using C.faceDegree_three_le flank.1
  by_cases h3 : C.faceDegree flank.1 = 3
  · exact Or.inl h3
  by_cases h4 : C.faceDegree flank.1 = 4
  · right
    apply A.zeroDiagonal_of_degree_four_of_bad_across hrest h4 flank.2
    have hinv : A.across flank = ⟨bad.1, j⟩ :=
      A.across_involutive ⟨bad.1, j⟩
    rw [hinv]
    exact A.evilDart_across_bad e
  · have hfive : 5 ≤ C.faceDegree flank.1 := by omega
    have hdon : flank.1 ∈ A.donationDonors e.1 := by
      apply (A.mem_donationDonors_iff e.1 flank.1).mpr
      exact A.donationGeometry_flank_of_degree_five e j hadj hfive
    rw [e.2.2] at hdon
    simp at hdon

end Data
end ABKPR
end Erdos735
