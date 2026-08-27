/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairedBisectionSampling
import ErdosProblems.Erdos207.FairBitLiteralConcentration
import ErdosProblems.Erdos207.AmbientLinkRelation

/-!
# Degree concentration for paired balanced bisections

For a fixed vertex, every pair of the base bisection contains zero, one, or
two ambient neighbors.  A two-neighbor pair contributes deterministically
one neighbor across the sampled cut.  A one-neighbor pair contributes when
its independent fair bit matches one prescribed literal.  This file proves
that exact deterministic decomposition and the resulting finite lower-tail
bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace BalancedBisection

/-- The paired coordinates, excluding the unique pair containing `x`.  The
caller supplies its index; later applications choose the canonical index. -/
def pairIndicesExcept
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (owner : ↥B.left) : Finset ↥B.left :=
  univ.erase owner

/-- Pairs, other than the owner pair, both of whose endpoints are related to
`x`. -/
def doubleNeighborPairs
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) : Finset ↥B.left :=
  (B.pairIndicesExcept owner).filter fun a ↦
    r x a.1 ∧ r x (B.pairEquiv a).1

/-- Pairs, other than the owner pair, with exactly one endpoint related to
`x`. -/
def singleNeighborPairs
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) : Finset ↥B.left :=
  (B.pairIndicesExcept owner).filter fun a ↦
    (r x a.1 ∧ ¬ r x (B.pairEquiv a).1) ∨
      (¬ r x a.1 ∧ r x (B.pairEquiv a).1)

lemma disjoint_double_single
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) :
    Disjoint (B.doubleNeighborPairs r x owner)
      (B.singleNeighborPairs r x owner) := by
  rw [Finset.disjoint_left]
  intro a haD haS
  have hd := (mem_filter.mp haD).2
  have hs := (mem_filter.mp haS).2
  tauto

/-- Literal which makes the unique neighbor of a one-neighbor pair land on
the sampled right side. -/
def rightCrossingLiteral
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (a : ↥B.left) : Bool :=
  decide (r x (B.pairEquiv a).1)

/-- Literal which makes the unique neighbor land on the sampled left side. -/
def leftCrossingLiteral
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (a : ↥B.left) : Bool :=
  decide (r x a.1)

lemma relation_pairedRightVertex_of_double
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner a : ↥B.left) (ω : ↥B.left → Bool)
    (ha : a ∈ B.doubleNeighborPairs r x owner) :
    r x (B.pairedRightVertex ω a) := by
  have hd := (mem_filter.mp ha).2
  by_cases hω : ω a = true
  · simpa [pairedRightVertex, hω] using hd.2
  · have hω' : ω a = false := Bool.eq_false_of_not_eq_true hω
    simpa [pairedRightVertex, hω'] using hd.1

lemma relation_pairedLeftVertex_of_double
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner a : ↥B.left) (ω : ↥B.left → Bool)
    (ha : a ∈ B.doubleNeighborPairs r x owner) :
    r x (B.pairedLeftVertex ω a) := by
  have hd := (mem_filter.mp ha).2
  by_cases hω : ω a = true
  · simpa [pairedLeftVertex, hω] using hd.1
  · have hω' : ω a = false := Bool.eq_false_of_not_eq_true hω
    simpa [pairedLeftVertex, hω'] using hd.2

lemma relation_pairedRightVertex_of_single_matched
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner a : ↥B.left) (ω : ↥B.left → Bool)
    (ha : a ∈ B.singleNeighborPairs r x owner)
    (hmatch : ω a = B.rightCrossingLiteral r x a) :
    r x (B.pairedRightVertex ω a) := by
  have hs := (mem_filter.mp ha).2
  rcases hs with ⟨haL, haR⟩ | ⟨haL, haR⟩
  · have hlit : B.rightCrossingLiteral r x a = false := by
      simp [rightCrossingLiteral, haR]
    have hω : ω a = false := hmatch.trans hlit
    simpa [pairedRightVertex, hω] using haL
  · have hlit : B.rightCrossingLiteral r x a = true := by
      simp [rightCrossingLiteral, haR]
    have hω : ω a = true := hmatch.trans hlit
    simpa [pairedRightVertex, hω] using haR

lemma relation_pairedLeftVertex_of_single_matched
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner a : ↥B.left) (ω : ↥B.left → Bool)
    (ha : a ∈ B.singleNeighborPairs r x owner)
    (hmatch : ω a = B.leftCrossingLiteral r x a) :
    r x (B.pairedLeftVertex ω a) := by
  have hs := (mem_filter.mp ha).2
  rcases hs with ⟨haL, haR⟩ | ⟨haL, haR⟩
  · have hlit : B.leftCrossingLiteral r x a = true := by
      simp [leftCrossingLiteral, haL]
    have hω : ω a = true := hmatch.trans hlit
    simpa [pairedLeftVertex, hω] using haL
  · have hlit : B.leftCrossingLiteral r x a = false := by
      simp [leftCrossingLiteral, haL]
    have hω : ω a = false := hmatch.trans hlit
    simpa [pairedLeftVertex, hω] using haR

/-- Neighbors of `x` on the sampled right side. -/
def pairedRightNeighbors
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (ω : ↥B.left → Bool) (x : V) : Finset V :=
  (B.pairedRight ω).filter (r x)

/-- Neighbors of `x` on the sampled left side. -/
def pairedLeftNeighbors
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (ω : ↥B.left → Bool) (x : V) : Finset V :=
  (B.pairedLeft ω).filter (r x)

lemma double_add_matched_le_pairedRightNeighbors
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) (ω : ↥B.left → Bool) :
    (B.doubleNeighborPairs r x owner).card +
        (matchedBits (B.rightCrossingLiteral r x) ω
          (B.singleNeighborPairs r x owner)).card ≤
      (B.pairedRightNeighbors r ω x).card := by
  classical
  let D := B.doubleNeighborPairs r x owner
  let S := matchedBits (B.rightCrossingLiteral r x) ω
    (B.singleNeighborPairs r x owner)
  let I := D ∪ S
  have hDS : Disjoint D S := by
    apply (B.disjoint_double_single r x owner).mono_right
    intro a ha
    exact (mem_matchedBits_iff.mp ha).1
  have hIcard : I.card = D.card + S.card := by
    exact card_union_of_disjoint hDS
  have hinj : Function.Injective (B.pairedRightVertex ω) :=
    B.pairedRightVertex_injective ω
  have himage : I.image (B.pairedRightVertex ω) ⊆
      B.pairedRightNeighbors r ω x := by
    intro y hy
    obtain ⟨a, haI, rfl⟩ := mem_image.mp hy
    apply mem_filter.mpr
    refine ⟨mem_pairedRight_iff.mpr ⟨a, rfl⟩, ?_⟩
    rcases mem_union.mp haI with haD | haS
    · exact B.relation_pairedRightVertex_of_double r x owner a ω haD
    · have haS' := mem_matchedBits_iff.mp haS
      exact B.relation_pairedRightVertex_of_single_matched r x owner a ω
        haS'.1 haS'.2
  calc
    D.card + S.card = I.card := hIcard.symm
    _ = (I.image (B.pairedRightVertex ω)).card := by
      rw [card_image_of_injective _ hinj]
    _ ≤ (B.pairedRightNeighbors r ω x).card := card_le_card himage

lemma double_add_matched_le_pairedLeftNeighbors
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) (ω : ↥B.left → Bool) :
    (B.doubleNeighborPairs r x owner).card +
        (matchedBits (B.leftCrossingLiteral r x) ω
          (B.singleNeighborPairs r x owner)).card ≤
      (B.pairedLeftNeighbors r ω x).card := by
  classical
  let D := B.doubleNeighborPairs r x owner
  let S := matchedBits (B.leftCrossingLiteral r x) ω
    (B.singleNeighborPairs r x owner)
  let I := D ∪ S
  have hDS : Disjoint D S := by
    apply (B.disjoint_double_single r x owner).mono_right
    intro a ha
    exact (mem_matchedBits_iff.mp ha).1
  have hIcard : I.card = D.card + S.card := card_union_of_disjoint hDS
  have hinj : Function.Injective (B.pairedLeftVertex ω) :=
    B.pairedLeftVertex_injective ω
  have himage : I.image (B.pairedLeftVertex ω) ⊆
      B.pairedLeftNeighbors r ω x := by
    intro y hy
    obtain ⟨a, haI, rfl⟩ := mem_image.mp hy
    apply mem_filter.mpr
    refine ⟨mem_pairedLeft_iff.mpr ⟨a, rfl⟩, ?_⟩
    rcases mem_union.mp haI with haD | haS
    · exact B.relation_pairedLeftVertex_of_double r x owner a ω haD
    · have haS' := mem_matchedBits_iff.mp haS
      exact B.relation_pairedLeftVertex_of_single_matched r x owner a ω
        haS'.1 haS'.2
  calc
    D.card + S.card = I.card := hIcard.symm
    _ = (I.image (B.pairedLeftVertex ω)).card := by
      rw [card_image_of_injective _ hinj]
    _ ≤ (B.pairedLeftNeighbors r ω x).card := card_le_card himage

/-- The actual number of related vertices across the paired cut. -/
def pairedCrossDegree
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (ω : ↥B.left → Bool) (x : V) : ℕ :=
  if x ∈ B.pairedLeft ω then
    (B.pairedRightNeighbors r ω x).card
  else
    (B.pairedLeftNeighbors r ω x).card

/-- Exact paired-sampling lower tail for one vertex and a supplied owner
pair.  The factor two is the union over the two possible sampled sides of
the vertex. -/
theorem pairedLaw_probability_crossDegree_lt_le
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) (d : ℕ) :
    (B.pairedLaw).probability (fun ω ↦ B.pairedCrossDegree r ω x < d) ≤
      2 * ((2 : ℝ≥0) ^
        (d - (B.doubleNeighborPairs r x owner).card) *
          (3 / 4 : ℝ≥0) ^
            (B.singleNeighborPairs r x owner).card) := by
  classical
  let D := (B.doubleNeighborPairs r x owner).card
  let S := B.singleNeighborPairs r x owner
  let k := d - D
  let BadR : (↥B.left → Bool) → Prop := fun ω ↦
    (matchedBits (B.rightCrossingLiteral r x) ω S).card ≤ k
  let BadL : (↥B.left → Bool) → Prop := fun ω ↦
    (matchedBits (B.leftCrossingLiteral r x) ω S).card ≤ k
  have hsub : ∀ ω, B.pairedCrossDegree r ω x < d → BadR ω ∨ BadL ω := by
    intro ω hbad
    by_cases hxL : x ∈ B.pairedLeft ω
    · apply Or.inl
      have hlower := B.double_add_matched_le_pairedRightNeighbors
        r x owner ω
      simp only [pairedCrossDegree, hxL, if_true] at hbad
      dsimp only [BadR, k, D, S]
      omega
    · apply Or.inr
      have hlower := B.double_add_matched_le_pairedLeftNeighbors
        r x owner ω
      simp only [pairedCrossDegree, hxL, if_false] at hbad
      dsimp only [BadL, k, D, S]
      omega
  calc
    (B.pairedLaw).probability (fun ω ↦ B.pairedCrossDegree r ω x < d) ≤
        (B.pairedLaw).probability (fun ω ↦ BadR ω ∨ BadL ω) :=
      (B.pairedLaw).probability_mono hsub
    _ ≤ (B.pairedLaw).probability BadR +
        (B.pairedLaw).probability BadL :=
      (B.pairedLaw).probability_or_le BadR BadL
    _ ≤ ((2 : ℝ≥0) ^ k * (3 / 4 : ℝ≥0) ^ S.card) +
        ((2 : ℝ≥0) ^ k * (3 / 4 : ℝ≥0) ^ S.card) := by
      apply add_le_add
      · exact fairBits_probability_matchedBits_card_le_le_generating
          (B.rightCrossingLiteral r x) S k
      · exact fairBits_probability_matchedBits_card_le_le_generating
          (B.leftCrossingLiteral r x) S k
    _ = 2 * ((2 : ℝ≥0) ^
        (d - (B.doubleNeighborPairs r x owner).card) *
          (3 / 4 : ℝ≥0) ^
            (B.singleNeighborPairs r x owner).card) := by
      simp only [k, D, S]
      ring

/-- The unique base-pair coordinate containing a vertex of `W`. -/
def pairOwner
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (x : V) (hx : x ∈ W) : ↥B.left := by
  by_cases hxL : x ∈ B.left
  · exact ⟨x, hxL⟩
  · exact B.pairEquiv.symm ⟨x, mem_sdiff.mpr ⟨hx, hxL⟩⟩

/-- A strict sum of the explicit one-vertex paired lower-tail bounds yields
one balanced bisection with the requested minimum cross degree at every
vertex of `W`. -/
theorem exists_pairedBisection_minCrossDegree
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (d : ℕ)
    (hsmall :
      ∑ x : ↥W,
        2 * ((2 : ℝ≥0) ^
          (d - (B.doubleNeighborPairs r x.1 (B.pairOwner x.1 x.2)).card) *
            (3 / 4 : ℝ≥0) ^
              (B.singleNeighborPairs r x.1 (B.pairOwner x.1 x.2)).card) < 1) :
    ∃ ω : ↥B.left → Bool,
      ∀ x ∈ W, d ≤ B.pairedCrossDegree r ω x := by
  classical
  let Bad : ↥W → (↥B.left → Bool) → Prop :=
    fun x ω ↦ B.pairedCrossDegree r ω x.1 < d
  have hprob :
      ∑ x : ↥W, (B.pairedLaw).probability (Bad x) ≤
        ∑ x : ↥W,
          2 * ((2 : ℝ≥0) ^
            (d - (B.doubleNeighborPairs r x.1 (B.pairOwner x.1 x.2)).card) *
              (3 / 4 : ℝ≥0) ^
                (B.singleNeighborPairs r x.1 (B.pairOwner x.1 x.2)).card) := by
    apply Finset.sum_le_sum
    intro x _hx
    exact B.pairedLaw_probability_crossDegree_lt_le r x.1
      (B.pairOwner x.1 x.2) d
  obtain ⟨ω, hω⟩ :=
    (B.pairedLaw).exists_avoiding_of_sum_probability_lt_one
      (univ : Finset ↥W) Bad (by simpa using hprob.trans_lt hsmall)
  exact ⟨ω, fun x hx ↦ Nat.le_of_not_gt (hω ⟨x, hx⟩ (mem_univ _))⟩

end BalancedBisection

end

end Erdos207
