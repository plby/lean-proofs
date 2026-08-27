/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationForbiddenDegree

/-! # A uniform vertex-power bound for the actual forbidden family -/

namespace Erdos207

open Finset

theorem earlier_superset_degree_term_le
    (n m D k s : ℕ) (hn : 1 ≤ n) (hm : m ≤ n ^ 3) (hs : 2 ≤ s) (hsk : s ≤ k)
    (hD : D ≤ n ^ (s - 1)) :
    2 * D * m ^ (k - s) ≤ 2 * n ^ (3 * k - 5) := by
  calc
    _ ≤ 2 * n ^ (s - 1) * (n ^ 3) ^ (k - s) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hD) (Nat.pow_le_pow_left hm _)
    _ = 2 * n ^ ((s - 1) + 3 * (k - s)) := by rw [← pow_mul, mul_assoc, ← pow_add]
    _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hn (by omega))

theorem earlier_superset_degree_sum_le
    {K : Type*} [DecidableEq K] (orders : Finset K) (D size : K → ℕ) (n m k : ℕ)
    (hn : 1 ≤ n) (hm : m ≤ n ^ 3) (hk : 2 ≤ k) (horders : orders.card ≤ n)
    (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ k)
    (hD : ∀ i ∈ orders, D i ≤ n ^ (size i - 1)) :
    (∑ i ∈ orders, 2 * D i * m ^ (k - size i)) ≤ 2 * n ^ (3 * k - 4) := by
  calc
    _ ≤ ∑ _i ∈ orders, 2 * n ^ (3 * k - 5) := sum_le_sum (fun i hi ↦
      earlier_superset_degree_term_le n m (D i) k (size i) hn hm (hsize i hi).1 (hsize i hi).2 (hD i hi))
    _ = orders.card * (2 * n ^ (3 * k - 5)) := by simp
    _ ≤ n * (2 * n ^ (3 * k - 5)) := Nat.mul_le_mul_right _ horders
    _ = 2 * n ^ (3 * k - 4) := by
      have he : 3 * k - 4 = (3 * k - 5) + 1 := by omega
      rw [he, pow_succ]
      ring

theorem regularizationForbiddenFamily_max_degree_le_nine_power
    {V I K : Type*} [DecidableEq V] [Fintype I] [DecidableEq I] [DecidableEq K]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U)
    (hn : 1 ≤ U.card) (k : ℕ) (hk : 2 ≤ k) (G : Finset (Finset I))
    (orders : Finset K) (earlier : K → Finset (Finset I)) (size : K → ℕ)
    (horders : orders.card ≤ U.card) (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ k)
    (huniform : ∀ i ∈ orders, ∀ E ∈ earlier i, E.card = size i)
    (hearlier : ∀ i ∈ orders, finiteHypergraphMaxDegree (earlier i) ≤ U.card ^ (size i - 1))
    (hG : finiteHypergraphMaxDegree G ≤ U.card ^ (k - 1)) :
    finiteHypergraphMaxDegree (regularizationForbiddenFamily e k G (orders.biUnion earlier)) ≤
      9 * U.card ^ (3 * k - 4) := by
  have hm := card_auxiliary_triangles_le e U hsupport
  have hsup := uniformSupersets_biUnion_max_degree_le orders earlier size k
    (fun i hi ↦ ⟨by have := (hsize i hi).1; omega, (hsize i hi).2⟩) huniform
  have hsum := earlier_superset_degree_sum_le orders (fun i ↦ finiteHypergraphMaxDegree (earlier i))
    size U.card (Fintype.card I) k hn hm hk horders hsize hearlier
  have hG' : finiteHypergraphMaxDegree G ≤ U.card ^ (3 * k - 4) :=
    hG.trans (Nat.pow_le_pow_right hn (by omega))
  unfold regularizationForbiddenFamily
  have htotal := (finiteHypergraphMaxDegree_union_le
    (auxiliaryNonDisjointFamily e k ∪ uniformSupersets k (orders.biUnion earlier)) G).trans
    (Nat.add_le_add (finiteHypergraphMaxDegree_union_le _ _) le_rfl)
  apply htotal.trans
  have hbound := Nat.add_le_add
    (Nat.add_le_add (auxiliaryNonDisjointFamily_max_degree_le_vertex_power e U hsupport k hk)
      (hsup.trans hsum)) hG'
  exact hbound.trans_eq (by ring)

end Erdos207
