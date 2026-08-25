/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.EquivFin
import ErdosProblems.Erdos207.Basic

/-!
# Deterministic robust Hall lemmas for Erdős Problem 207

This file isolates the deterministic conclusion used by the final crossing
edge step of KSSS.  Random sparsification is used only to establish the
`SurvivesEveryHallObstruction` hypothesis below; Hall's theorem then returns
the required matching without any probability-theoretic side conditions.
-/

namespace Erdos207

open Finset

/-- The vertices on the right met from at least one member of `S`. -/
def relationNeighbors {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (S : Finset A) : Finset B :=
  Finset.univ.filter fun b ↦ ∃ a ∈ S, r a b

@[simp]
lemma mem_relationNeighbors_iff {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] {S : Finset A} {b : B} :
    b ∈ relationNeighbors r S ↔ ∃ a ∈ S, r a b := by
  simp [relationNeighbors]

/-- Hall's cardinality condition for a finite relation. -/
def HasHallExpansion {A B : Type*} [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] : Prop :=
  ∀ S : Finset A, S.card ≤ (relationNeighbors r S).card

/-- The relation survives every potential Hall obstruction: whenever the
right-hand set `T` is smaller than the left-hand set `S`, a surviving edge
leaves `T`. -/
def SurvivesEveryHallObstruction {A B : Type*}
    (r deleted : A → B → Prop) : Prop :=
  ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
    ∃ a ∈ S, ∃ b ∉ T, r a b ∧ ¬ deleted a b

/-- Right neighbors deleted at one left vertex. -/
def deletedNeighbors {A B : Type*} [Fintype B]
    (deleted : A → B → Prop) [DecidableRel deleted] (a : A) : Finset B :=
  Finset.univ.filter (deleted a)

@[simp]
lemma mem_deletedNeighbors_iff {A B : Type*} [Fintype B]
    (deleted : A → B → Prop) [DecidableRel deleted] {a : A} {b : B} :
    b ∈ deletedNeighbors deleted a ↔ deleted a b := by
  simp [deletedNeighbors]

/-- Candidate relation-pairs which leave a proposed right-hand Hall
obstruction. -/
def relationPairsLeaving {A B : Type*} [DecidableEq A] [Fintype B]
    [DecidableEq B] (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (T : Finset B) : Finset (A × B) :=
  (S.product Finset.univ).filter fun ab ↦ ab.2 ∉ T ∧ r ab.1 ab.2

@[simp]
lemma mem_relationPairsLeaving_iff
    {A B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    {S : Finset A} {T : Finset B} {a : A} {b : B} :
    (a, b) ∈ relationPairsLeaving r S T ↔
      a ∈ S ∧ b ∉ T ∧ r a b := by
  simp [relationPairsLeaving]

/-- If each left vertex loses at most `Δ` pairs, then more than
`Δ * |S|` candidate pairs leave every smaller right set, so at least one
candidate survives.  This is the deterministic counting step immediately
before robust Hall is invoked in KSSS. -/
theorem survivesEveryHallObstruction_of_many_pairs
    {A B : Type*} [DecidableEq A] [Fintype B] [DecidableEq B]
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (Δ : ℕ)
    (hdeleted : ∀ a, (deletedNeighbors deleted a).card ≤ Δ)
    (hmany : ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
      Δ * S.card < (relationPairsLeaving r S T).card) :
    SurvivesEveryHallObstruction r deleted := by
  intro S T hTS
  by_contra hnone
  push Not at hnone
  have hsubset : relationPairsLeaving r S T ⊆
      S.biUnion fun a ↦
        (deletedNeighbors deleted a).image fun b ↦ (a, b) := by
    intro ab hab
    obtain ⟨haS, hbT, hrab⟩ :=
      mem_relationPairsLeaving_iff r |>.mp hab
    have hdab : deleted ab.1 ab.2 := by
      by_contra hnot
      exact hnot (hnone ab.1 haS ab.2 hbT hrab)
    apply mem_biUnion.mpr
    refine ⟨ab.1, haS, mem_image.mpr ⟨ab.2, ?_, rfl⟩⟩
    exact mem_deletedNeighbors_iff deleted |>.mpr hdab
  have hcardUnion :
      (S.biUnion fun a ↦
        (deletedNeighbors deleted a).image fun b ↦ (a, b)).card ≤
        Δ * S.card := by
    calc
      (S.biUnion fun a ↦
          (deletedNeighbors deleted a).image fun b ↦ (a, b)).card ≤
          ∑ a ∈ S, ((deletedNeighbors deleted a).image fun b ↦ (a, b)).card :=
        card_biUnion_le
      _ ≤ ∑ _a ∈ S, Δ := by
        apply sum_le_sum
        intro a ha
        exact card_image_le.trans (hdeleted a)
      _ = Δ * S.card := by
        simp [mul_comm]
  have hcandidates := (card_le_card hsubset).trans hcardUnion
  exact (not_lt_of_ge hcandidates) (hmany S T hTS)

/-- The obstruction formulation directly implies Hall expansion after all
deleted pairs are removed. -/
theorem hallExpansion_after_deletion
    {A B : Type*} [Fintype B] [DecidableEq B]
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (hrobust : SurvivesEveryHallObstruction r deleted) :
    HasHallExpansion (fun a b ↦ r a b ∧ ¬ deleted a b) := by
  intro S
  by_contra hcard
  have hlt :
      (relationNeighbors (fun a b ↦ r a b ∧ ¬ deleted a b) S).card < S.card := by
    omega
  obtain ⟨a, haS, b, hbN, hab⟩ := hrobust S
    (relationNeighbors (fun a b ↦ r a b ∧ ¬ deleted a b) S) hlt
  exact hbN (mem_relationNeighbors_iff _ |>.2 ⟨a, haS, hab⟩)

/-- Robust Hall expansion supplies a system of distinct representatives in
the surviving relation. -/
theorem exists_injective_matching_after_deletion
    {A B : Type*} [Finite A] [Fintype B] [DecidableEq B]
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (hrobust : SurvivesEveryHallObstruction r deleted) :
    ∃ f : A → B, Function.Injective f ∧
      ∀ a, r a (f a) ∧ ¬ deleted a (f a) := by
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun a b ↦ r a b ∧ ¬ deleted a b)).mp
  intro S
  exact hallExpansion_after_deletion r deleted hrobust S

/-- When the two sides have the same finite cardinality, the robust Hall
matching is a bijection. -/
theorem exists_bijective_matching_after_deletion
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (hcard : Fintype.card A = Fintype.card B)
    (hrobust : SurvivesEveryHallObstruction r deleted) :
    ∃ f : A → B, Function.Bijective f ∧
      ∀ a, r a (f a) ∧ ¬ deleted a (f a) := by
  obtain ⟨f, hinj, hf⟩ :=
    exists_injective_matching_after_deletion r deleted hrobust
  exact ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, hcard⟩, hf⟩

end Erdos207
