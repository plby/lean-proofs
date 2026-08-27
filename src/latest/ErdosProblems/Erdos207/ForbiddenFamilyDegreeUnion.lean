/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformSupersetCounts

/-! # Degree budgets for unions of earlier forbidden orders -/

namespace Erdos207

open Finset

noncomputable section

theorem finiteHypergraphDegree_union_le
    {I : Type*} [DecidableEq I] (F G : Finset (Finset I)) (v : I) :
    finiteHypergraphDegree (F ∪ G) v ≤ finiteHypergraphDegree F v + finiteHypergraphDegree G v := by
  unfold finiteHypergraphDegree
  rw [filter_union]
  exact card_union_le _ _

theorem finiteHypergraphMaxDegree_union_le
    {I : Type*} [Fintype I] [DecidableEq I] (F G : Finset (Finset I)) :
    finiteHypergraphMaxDegree (F ∪ G) ≤ finiteHypergraphMaxDegree F + finiteHypergraphMaxDegree G := by
  apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
  intro v
  exact (finiteHypergraphDegree_union_le F G v).trans
    (Nat.add_le_add (finiteHypergraphDegree_le_max F v) (finiteHypergraphDegree_le_max G v))

theorem finiteHypergraphMaxDegree_biUnion_le
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (S : Finset K) (F : K → Finset (Finset I)) :
    finiteHypergraphMaxDegree (S.biUnion F) ≤ ∑ i ∈ S, finiteHypergraphMaxDegree (F i) := by
  apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
  intro v
  have hfilter : ((S.biUnion F).filter (fun E ↦ v ∈ E)) =
      S.biUnion (fun i ↦ (F i).filter (fun E ↦ v ∈ E)) := by
    ext E
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨⟨i, hi, hE⟩, hv⟩
      exact ⟨i, hi, hE, hv⟩
    · rintro ⟨i, hi, hE, hv⟩
      exact ⟨⟨i, hi, hE⟩, hv⟩
  unfold finiteHypergraphDegree
  rw [hfilter]
  exact card_biUnion_le.trans (sum_le_sum (fun i _ ↦ finiteHypergraphDegree_le_max (F i) v))

theorem uniformSupersets_biUnion
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (S : Finset K) (F : K → Finset (Finset I)) (k : ℕ) :
    uniformSupersets k (S.biUnion F) = S.biUnion (fun i ↦ uniformSupersets k (F i)) := by
  ext E
  simp only [mem_uniformSupersets_iff, mem_biUnion]
  constructor
  · rintro ⟨hcard, C, ⟨i, hi, hC⟩, hCE⟩
    exact ⟨i, hi, hcard, C, hC, hCE⟩
  · rintro ⟨i, hi, hcard, C, hC, hCE⟩
    exact ⟨hcard, C, ⟨i, hi, hC⟩, hCE⟩

theorem uniformSupersets_biUnion_max_degree_le
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (S : Finset K) (F : K → Finset (Finset I)) (size : K → ℕ) (k : ℕ)
    (hsize : ∀ i ∈ S, 1 ≤ size i ∧ size i ≤ k)
    (huniform : ∀ i ∈ S, ∀ E ∈ F i, E.card = size i) :
    finiteHypergraphMaxDegree (uniformSupersets k (S.biUnion F)) ≤
      ∑ i ∈ S, 2 * finiteHypergraphMaxDegree (F i) * (Fintype.card I) ^ (k - size i) := by
  rw [uniformSupersets_biUnion]
  apply (finiteHypergraphMaxDegree_biUnion_le S (fun i ↦ uniformSupersets k (F i))).trans
  apply sum_le_sum
  intro i hi
  exact uniformSupersets_max_degree_le_of_le k (size i) (F i) (hsize i hi).1 (hsize i hi).2 (huniform i hi)

end

end Erdos207
