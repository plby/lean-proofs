/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomRobustMatching

/-!
# Exact counting for bipartite Hall obstructions

This file records the elementary double-counting identities used in the
robust matching lemma.  In particular, minimum degree on either side gives
an exact lower bound for the number of relation-pairs escaping a prospective
Hall obstruction.  These are the two extreme-size regimes in the KSSS
matching argument; the intermediate regime is supplied by the typical-graph
mixing estimate.
-/

namespace Erdos207

open Finset

/-- Right vertices in `U` related to a fixed left vertex. -/
def relationNeighborsIn
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (U : Finset B) (a : A) : Finset B :=
  U.filter (r a)

@[simp]
lemma mem_relationNeighborsIn_iff
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    {U : Finset B} {a : A} {b : B} :
    b ∈ relationNeighborsIn r U a ↔ b ∈ U ∧ r a b := by
  simp [relationNeighborsIn]

/-- Left vertices in `S` related to a fixed right vertex. -/
def relationPreneighborsIn
    {A B : Type*} [Fintype A] [DecidableEq A]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (b : B) : Finset A :=
  S.filter fun a ↦ r a b

@[simp]
lemma mem_relationPreneighborsIn_iff
    {A B : Type*} [Fintype A] [DecidableEq A]
    (r : A → B → Prop) [DecidableRel r]
    {S : Finset A} {a : A} {b : B} :
    a ∈ relationPreneighborsIn r S b ↔ a ∈ S ∧ r a b := by
  simp [relationPreneighborsIn]

/-- Relation-pairs with their two coordinates in prescribed finite sets. -/
def relationPairsBetween
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) : Finset (A × B) :=
  (S.product U).filter fun ab ↦ r ab.1 ab.2

@[simp]
lemma mem_relationPairsBetween_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    {S : Finset A} {U : Finset B} {a : A} {b : B} :
    (a, b) ∈ relationPairsBetween r S U ↔ a ∈ S ∧ b ∈ U ∧ r a b := by
  simp [relationPairsBetween, and_assoc]

/-- Counting relation-pairs by their left endpoint. -/
lemma card_relationPairsBetween_eq_sum_left
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    (relationPairsBetween r S U).card =
      ∑ a ∈ S, (relationNeighborsIn r U a).card := by
  classical
  simp only [relationPairsBetween, relationNeighborsIn, card_eq_sum_ones,
    sum_filter]
  exact Finset.sum_product' S U
    (fun a b ↦ if r a b then (1 : ℕ) else 0)

/-- Counting relation-pairs by their right endpoint. -/
lemma card_relationPairsBetween_eq_sum_right
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    (relationPairsBetween r S U).card =
      ∑ b ∈ U, (relationPreneighborsIn r S b).card := by
  classical
  rw [card_relationPairsBetween_eq_sum_left]
  simp only [relationNeighborsIn, relationPreneighborsIn,
    card_eq_sum_ones, sum_filter]
  rw [sum_comm]

/-- Escaping a Hall set `T` means going to its complement. -/
lemma relationPairsLeaving_eq_between_sdiff
    {A B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (T : Finset B) :
    relationPairsLeaving r S T =
      relationPairsBetween r S (Finset.univ \ T) := by
  ext ab
  rcases ab with ⟨a, b⟩
  simp only [mem_relationPairsLeaving_iff, mem_relationPairsBetween_iff,
    mem_sdiff, mem_univ, true_and]

/-- A lower bound on every left degree gives the first Hall-obstruction
count: each left vertex has at most `|T|` neighbors inside `T`. -/
theorem card_relationPairsLeaving_ge_of_left_degree
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (d : ℕ) (hdegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (S : Finset A) (T : Finset B) :
    S.card * (d - T.card) ≤ (relationPairsLeaving r S T).card := by
  classical
  rw [relationPairsLeaving_eq_between_sdiff,
    card_relationPairsBetween_eq_sum_left]
  calc
    S.card * (d - T.card) = ∑ _a ∈ S, (d - T.card) := by simp
    _ ≤ ∑ a ∈ S, (relationNeighborsIn r (univ \ T) a).card := by
      apply sum_le_sum
      intro a ha
      have hsplit : relationNeighborsIn r univ a ⊆
          relationNeighborsIn r (univ \ T) a ∪ T := by
        intro b hb
        by_cases hbT : b ∈ T
        · exact mem_union_right _ hbT
        · exact mem_union_left _ <| mem_relationNeighborsIn_iff r |>.2
            ⟨mem_sdiff.mpr ⟨mem_univ _, hbT⟩,
              (mem_relationNeighborsIn_iff r |>.1 hb).2⟩
      have hcard := card_le_card hsplit
      have hunion := card_union_le
        (relationNeighborsIn r (univ \ T) a) T
      apply Nat.sub_le_iff_le_add.mpr
      exact (hdegree a).trans (hcard.trans hunion)

/-- A lower bound on every right degree gives the symmetric large-set
Hall-obstruction count. -/
theorem card_relationPairsLeaving_ge_of_right_degree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (d : ℕ) (hdegree : ∀ b, d ≤ (relationPreneighborsIn r univ b).card)
    (S : Finset A) (T : Finset B) :
    (Fintype.card B - T.card) * (d - (Fintype.card A - S.card)) ≤
      (relationPairsLeaving r S T).card := by
  classical
  rw [relationPairsLeaving_eq_between_sdiff,
    card_relationPairsBetween_eq_sum_right]
  have hcardT : T.card ≤ Fintype.card B := by
    simpa using T.card_le_univ
  calc
    (Fintype.card B - T.card) * (d - (Fintype.card A - S.card)) =
        ∑ _b ∈ (univ \ T : Finset B),
          (d - (Fintype.card A - S.card)) := by
      simp [card_sdiff_of_subset (subset_univ T), hcardT]
    _ ≤ ∑ b ∈ (univ \ T : Finset B),
        (relationPreneighborsIn r S b).card := by
      apply sum_le_sum
      intro b hb
      have hsplit : relationPreneighborsIn r univ b ⊆
          relationPreneighborsIn r S b ∪ (univ \ S) := by
        intro a ha
        by_cases haS : a ∈ S
        · exact mem_union_left _ <| mem_relationPreneighborsIn_iff r |>.2
            ⟨haS, (mem_relationPreneighborsIn_iff r |>.1 ha).2⟩
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _, haS⟩)
      have hcard := card_le_card hsplit
      have hunion := card_union_le
        (relationPreneighborsIn r S b) (univ \ S)
      have hcardS : S.card ≤ Fintype.card A := by
        simpa using S.card_le_univ
      rw [card_sdiff_of_subset (subset_univ S)] at hunion
      apply Nat.sub_le_iff_le_add.mpr
      exact (hdegree b).trans (hcard.trans hunion)

/-- A relation has `c` escaping pairs per left vertex at every Hall
obstruction.  This is the exact deterministic expansion delivered by the
degree/codegree mixing part of the KSSS robust matching lemma. -/
def HasRobustHallPairExpansion
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (c : ℕ) : Prop :=
  ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
    c * S.card ≤ (relationPairsLeaving r S T).card

/-- Uniform robust pair expansion implies the candidate-group inequality
used by the finite random sparsification theorem. -/
theorem candidate_bound_of_robustHallPairExpansion
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize c : ℕ)
    (hexpand : HasRobustHallPairExpansion r c)
    (hscalar : Delta * groupSize + groupSize ≤ c) :
    ∀ o : HallObstruction A B,
      (Delta * o.1.1.card + 1) * groupSize ≤
        (relationPairsLeaving r o.1.1 o.1.2).card := by
  intro o
  have hnonempty : 1 ≤ o.1.1.card := by omega
  refine le_trans ?_ (hexpand o.1.1 o.1.2 o.2)
  calc
    (Delta * o.1.1.card + 1) * groupSize =
        Delta * groupSize * o.1.1.card + groupSize := by ring
    _ ≤ (Delta * groupSize + groupSize) * o.1.1.card := by
      nlinarith
    _ ≤ c * o.1.1.card := Nat.mul_le_mul_right _ hscalar

end Erdos207
