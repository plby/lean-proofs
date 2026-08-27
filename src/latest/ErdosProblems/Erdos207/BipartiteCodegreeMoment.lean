/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BipartiteSecondMomentMixing

/-!
# Codegrees give the bipartite second-moment bound

The squared right `S`-degrees count ordered pairs of left endpoints with a
common right neighbor.  Splitting the diagonal and off-diagonal terms turns
maximum degree and maximum codegree into the second-moment hypothesis used
by the finite mixing lemma.
-/

namespace Erdos207

open Finset

/-- Common right neighbors of two left vertices. -/
def relationCommonNeighbors
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (a a' : A) : Finset B :=
  univ.filter fun b ↦ r a b ∧ r a' b

@[simp]
lemma mem_relationCommonNeighbors_iff
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    {a a' : A} {b : B} :
    b ∈ relationCommonNeighbors r a a' ↔ r a b ∧ r a' b := by
  simp [relationCommonNeighbors]

lemma relationCommonNeighbors_self
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (a : A) :
    relationCommonNeighbors r a a = relationNeighborsIn r univ a := by
  ext b
  simp

/-- Exact ordered-pair double count for the right-degree second moment. -/
theorem sum_sq_relationPreneighbors_eq_sum_commonNeighbors
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (S : Finset A) :
    (∑ b : B, (relationPreneighborsIn r S b).card ^ 2) =
      ∑ a ∈ S, ∑ a' ∈ S, (relationCommonNeighbors r a a').card := by
  classical
  simp only [relationPreneighborsIn, relationCommonNeighbors,
    card_eq_sum_ones, sum_filter, pow_two]
  simp_rw [Finset.sum_mul_sum]
  simp only [ite_mul, one_mul, zero_mul, ite_eq_right_iff]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_comm]
  apply sum_congr rfl
  intro a' ha'
  apply sum_congr rfl
  intro b hb
  by_cases hab : r a b <;> by_cases ha'b : r a' b <;> simp [hab, ha'b]

/-- Maximum degree and off-diagonal codegree imply the standard second
moment estimate. -/
theorem hasBipartiteDegreeSecondMomentBounds_of_degree_codegree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (d D codegree : ℕ)
    (hdegree : ∀ a,
      d ≤ (relationNeighborsIn r univ a).card ∧
        (relationNeighborsIn r univ a).card ≤ D)
    (hcodegree : ∀ a a', a ≠ a' →
      (relationCommonNeighbors r a a').card ≤ codegree) :
    HasBipartiteDegreeSecondMomentBounds r d D codegree := by
  refine ⟨hdegree, ?_⟩
  intro S
  rw [sum_sq_relationPreneighbors_eq_sum_commonNeighbors]
  calc
    (∑ a ∈ S, ∑ a' ∈ S,
        (relationCommonNeighbors r a a').card) ≤
      ∑ _a ∈ S, (D + codegree * (S.card - 1)) := by
        apply sum_le_sum
        intro a ha
        rw [← add_sum_erase S
          (fun a' ↦ (relationCommonNeighbors r a a').card) ha]
        apply Nat.add_le_add
        · rw [relationCommonNeighbors_self]
          exact (hdegree a).2
        · calc
            (∑ a' ∈ S.erase a,
                (relationCommonNeighbors r a a').card) ≤
              ∑ _a' ∈ S.erase a, codegree := by
                apply sum_le_sum
                intro a' ha'
                exact hcodegree a a' (Ne.symm (ne_of_mem_erase ha'))
            _ = codegree * (S.card - 1) := by
              rw [sum_const_nat (m := codegree)
                (f := fun _ : A ↦ codegree) (fun _ _ ↦ rfl),
                card_erase_of_mem ha]
              ring
    _ = D * S.card + codegree * S.card * (S.card - 1) := by
      rw [sum_const_nat
        (m := D + codegree * (S.card - 1))
        (f := fun _ : A ↦ D + codegree * (S.card - 1))
        (fun _ _ ↦ rfl)]
      ring

end Erdos207
