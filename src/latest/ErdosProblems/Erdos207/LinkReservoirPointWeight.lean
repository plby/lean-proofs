/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReservoirSampling

/-!
# Point-weight bookkeeping for a sweep of link reservoirs

A reservoir used at center `o` is supported only on triples containing that
center.  Since every ambient triple has three vertices, the sum of these
support weights over an injectively indexed center family is at most three
times the sampling density, independently of the number of centers.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Sum of the sampling densities belonging to centers contained in `T`. -/
def centerIndexedTriangleWeight
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (center : O → V) (S : Finset O) (sigma : ℝ≥0)
    (T : TripleOn V) : ℝ≥0 :=
  ∑ o ∈ S, if center o ∈ T.1 then sigma else 0

@[simp]
lemma centerIndexedTriangleWeight_empty
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (center : O → V) (sigma : ℝ≥0) (T : TripleOn V) :
    centerIndexedTriangleWeight center ∅ sigma T = 0 := by
  simp [centerIndexedTriangleWeight]

lemma centerIndexedTriangleWeight_insert
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (center : O → V) {S : Finset O} {o : O} (ho : o ∉ S)
    (sigma : ℝ≥0) (T : TripleOn V) :
    centerIndexedTriangleWeight center (insert o S) sigma T =
      (if center o ∈ T.1 then sigma else 0) +
        centerIndexedTriangleWeight center S sigma T := by
  simp [centerIndexedTriangleWeight, ho]

lemma centerIndexedTriangleWeight_mono
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (center : O → V) {S R : Finset O} (hSR : S ⊆ R)
    (sigma : ℝ≥0) (T : TripleOn V) :
    centerIndexedTriangleWeight center S sigma T ≤
      centerIndexedTriangleWeight center R sigma T := by
  unfold centerIndexedTriangleWeight
  exact sum_le_sum_of_subset_of_nonneg hSR fun _ _ _ ↦ zero_le

lemma mem_linkReservoirTriangles_univ_center
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    {T : TripleOn V}
    (hT : T ∈ linkReservoirTriangles center left right hcenterLeft
      hcenterRight hleftRight (univ : Finset (A × B))) :
    center ∈ T.1 := by
  classical
  rw [linkReservoirTriangles_eq_map] at hT
  obtain ⟨ab, _hab, rfl⟩ := mem_map.mp hT
  change center ∈
    (linkMatchingTriple center left right hcenterLeft hcenterRight
      hleftRight ab.1 ab.2).1
  rw [mem_linkMatchingTriple_iff]
  exact Or.inl rfl

/-- The exact reservoir point weight is bounded by the indicator weight of
its center. -/
lemma linkReservoirPointWeight_le_center
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (T : TripleOn V) :
    linkReservoirPointWeight center left right hcenterLeft
      hcenterRight hleftRight sigma T ≤
        if center ∈ T.1 then sigma else 0 := by
  classical
  by_cases hfull : T ∈ linkReservoirTriangles center left right hcenterLeft
      hcenterRight hleftRight (univ : Finset (A × B))
  · have hc := mem_linkReservoirTriangles_univ_center center left right
      hcenterLeft hcenterRight hleftRight hfull
    simp [linkReservoirPointWeight, hfull, hc]
  · simp [linkReservoirPointWeight, hfull]

/-- The link point weight at one center is bounded by any indexed center
weight containing that center. -/
lemma linkReservoirPointWeight_le_centerIndexed
    {O A B V : Type*} [DecidableEq O] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : O → V) (S : Finset O) {o : O} (ho : o ∈ S)
    (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center o ≠ left a)
    (hcenterRight : ∀ b, center o ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (T : TripleOn V) :
    linkReservoirPointWeight (center o) left right hcenterLeft
      hcenterRight hleftRight sigma T ≤
        centerIndexedTriangleWeight center S sigma T := by
  calc
    linkReservoirPointWeight (center o) left right hcenterLeft
        hcenterRight hleftRight sigma T ≤
      if center o ∈ T.1 then sigma else 0 :=
        linkReservoirPointWeight_le_center (center o) left right
          hcenterLeft hcenterRight hleftRight sigma T
    _ ≤ centerIndexedTriangleWeight center S sigma T := by
      unfold centerIndexedTriangleWeight
      let f : O → ℝ≥0 := fun j ↦
        if center j ∈ T.1 then sigma else 0
      change f o ≤ ∑ j ∈ S, f j
      exact single_le_sum (fun _j _hj ↦ zero_le) ho

/-- Removing the current center from the remaining-center weight pays for
the exact support-sensitive weight of its Bernoulli link reservoir. -/
lemma linkReservoirPointWeight_add_remaining_le
    {O A B V : Type*} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : O → V) (S : Finset O) (o : O) (ho : o ∉ S)
    (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center o ≠ left a)
    (hcenterRight : ∀ b, center o ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sigma : ℝ≥0) (baseWeight : TripleOn V → ℝ≥0) (T : TripleOn V) :
    linkReservoirPointWeight (center o) left right hcenterLeft
        hcenterRight hleftRight sigma T +
      (centerIndexedTriangleWeight center (univ \ insert o S) sigma T +
        baseWeight T) ≤
      centerIndexedTriangleWeight center (univ \ S) sigma T +
        baseWeight T := by
  classical
  have hremaining : univ \ S = insert o (univ \ insert o S) := by
    ext j
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_or]
    constructor
    · intro hj
      by_cases hjo : j = o
      · exact Or.inl hjo
      · exact Or.inr ⟨hjo, hj⟩
    · rintro (rfl | ⟨_hjo, hj⟩)
      · exact ho
      · exact hj
  rw [hremaining, centerIndexedTriangleWeight_insert center (by simp)
    sigma T]
  have hlink := linkReservoirPointWeight_le_center (center o) left right
    hcenterLeft hcenterRight hleftRight sigma T
  calc
    linkReservoirPointWeight (center o) left right hcenterLeft
          hcenterRight hleftRight sigma T +
        (centerIndexedTriangleWeight center (univ \ insert o S) sigma T +
          baseWeight T) =
        (linkReservoirPointWeight (center o) left right hcenterLeft
            hcenterRight hleftRight sigma T +
          centerIndexedTriangleWeight center (univ \ insert o S) sigma T) +
            baseWeight T := by ac_rfl
    _ ≤ ((if center o ∈ T.1 then sigma else 0) +
          centerIndexedTriangleWeight center (univ \ insert o S) sigma T) +
            baseWeight T := by gcongr

/-- A triple contains at most three injectively indexed centers. -/
lemma centerIndexedTriangleWeight_le_three
    {O V : Type*} [Fintype O] [DecidableEq O] [DecidableEq V]
    (center : O → V) (hinj : Function.Injective center)
    (S : Finset O) (sigma : ℝ≥0) (T : TripleOn V) :
    centerIndexedTriangleWeight center S sigma T ≤ 3 * sigma := by
  classical
  let C := S.filter fun o ↦ center o ∈ T.1
  let e : ↥C ↪ ↥T.1 :=
    { toFun := fun o ↦ ⟨center o.1, (mem_filter.mp o.2).2⟩
      inj' := by
        intro o o' h
        apply Subtype.ext
        exact hinj (congrArg Subtype.val h) }
  have hcard : C.card ≤ 3 := by
    calc
      C.card = Fintype.card ↥C := by simp
      _ ≤ Fintype.card ↥T.1 := Fintype.card_le_of_embedding e
      _ = T.1.card := Fintype.card_coe _
      _ = 3 := T.2
  calc
    centerIndexedTriangleWeight center S sigma T = C.card * sigma := by
      rw [centerIndexedTriangleWeight]
      change (∑ o ∈ S, if center o ∈ T.1 then sigma else 0) = _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, C]
    _ ≤ 3 * sigma :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le

end

end Erdos207
