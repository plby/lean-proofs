/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ChosenMasterCrossingCoverStage
import ErdosProblems.Erdos207.FiniteProbability

/-!
# Uniform balanced bisections of a finite vertex set

The robust matching lemma begins by randomly bisecting an even link-vertex
set.  This file isolates the exact finite sample space.  Every outcome gives
a `BipartiteLink` whose two sides partition the prescribed set and have the
same cardinality.  A strict finite union bound then selects a bisection
avoiding any stated family of bad events.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A choice of one half of an even finite set.  Its complementary half is
defined below, so disjointness and coverage do not need to be stored. -/
structure BalancedBisection
    (V : Type*) [DecidableEq V] (W : Finset V) where
  left : Finset V
  left_subset : left ⊆ W
  twice_card : 2 * left.card = W.card

instance BalancedBisection.instFintype
    {V : Type*} [Fintype V] [DecidableEq V] (W : Finset V) :
    Fintype (BalancedBisection V W) :=
  Fintype.ofInjective BalancedBisection.left (by
    intro B C h
    cases B
    cases C
    cases h
    rfl)

namespace BalancedBisection

/-- The complementary half of a bisection. -/
def right
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : Finset V :=
  W \ B.left

lemma disjoint_left_right
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : Disjoint B.left B.right := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  exact (mem_sdiff.mp hxR).2 hxL

lemma union_left_right
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : B.left ∪ B.right = W := by
  rw [right, union_comm, Finset.sdiff_union_of_subset B.left_subset]

lemma card_right
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : B.right.card = B.left.card := by
  rw [right, card_sdiff_of_subset B.left_subset]
  rw [← B.twice_card]
  omega

/-- A balanced bisection, together with a center outside the bisected set,
is the concrete bipartite-link structure consumed by the matching layer. -/
def toBipartiteLink
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    BipartiteLink V where
  center := center
  left := B.left
  right := B.right
  center_not_left := fun h ↦ hcenter (B.left_subset h)
  center_not_right := fun h ↦ hcenter (mem_sdiff.mp h).1
  disjoint_sides := B.disjoint_left_right

@[simp]
lemma toBipartiteLink_center
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    (B.toBipartiteLink center hcenter).center = center := rfl

@[simp]
lemma toBipartiteLink_left
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    (B.toBipartiteLink center hcenter).left = B.left := rfl

@[simp]
lemma toBipartiteLink_right
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    (B.toBipartiteLink center hcenter).right = B.right := rfl

lemma toBipartiteLink_union
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    (B.toBipartiteLink center hcenter).left ∪
      (B.toBipartiteLink center hcenter).right = W :=
  B.union_left_right

lemma toBipartiteLink_balanced
    {V : Type*} [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (center : V) (hcenter : center ∉ W) :
    (B.toBipartiteLink center hcenter).left.card =
      (B.toBipartiteLink center hcenter).right.card := by
  exact B.card_right.symm

/-- An even finite set has at least one balanced bisection. -/
theorem nonempty_of_even
    {V : Type*} [DecidableEq V] (W : Finset V) (heven : Even W.card) :
    Nonempty (BalancedBisection V W) := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp heven
  have hmle : m ≤ W.card := by omega
  obtain ⟨L, hLW, hLcard⟩ := Finset.exists_subset_card_eq hmle
  exact ⟨⟨L, hLW, by omega⟩⟩

/-- The uniform law on all balanced bisections of an even set. -/
def uniformLaw
    {V : Type*} [Fintype V] [DecidableEq V] (W : Finset V)
    (heven : Even W.card) : FiniteLaw (BalancedBisection V W) := by
  letI : Nonempty (BalancedBisection V W) := nonempty_of_even W heven
  exact FiniteLaw.uniform

/-- A strict union bound over the uniform balanced-bisection law supplies
one bisection avoiding every bad event. -/
theorem exists_avoiding_of_sum_probability_lt_one
    {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V]
    (W : Finset V) (heven : Even W.card)
    (bad : I → BalancedBisection V W → Prop)
    (hsmall :
      ∑ i : I, (uniformLaw W heven).probability (bad i) < 1) :
    ∃ B : BalancedBisection V W, ∀ i, ¬ bad i B := by
  obtain ⟨B, hB⟩ :=
    (uniformLaw W heven).exists_avoiding_of_sum_probability_lt_one
      (univ : Finset I) bad (by simpa using hsmall)
  exact ⟨B, fun i ↦ hB i (mem_univ i)⟩

/-- The preceding extraction stated directly as a chosen bipartite link. -/
theorem exists_bipartiteLink_avoiding
    {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V]
    (center : V) (W : Finset V) (hcenter : center ∉ W)
    (heven : Even W.card)
    (bad : I → BalancedBisection V W → Prop)
    (hsmall :
      ∑ i : I, (uniformLaw W heven).probability (bad i) < 1) :
    ∃ B : BalancedBisection V W,
      let K := B.toBipartiteLink center hcenter
      K.center = center ∧ K.left ∪ K.right = W ∧
        K.left.card = K.right.card ∧ ∀ i, ¬ bad i B := by
  obtain ⟨B, hB⟩ := exists_avoiding_of_sum_probability_lt_one
    W heven bad hsmall
  exact ⟨B, rfl, B.toBipartiteLink_union center hcenter,
    B.toBipartiteLink_balanced center hcenter, hB⟩

end BalancedBisection

end

end Erdos207
