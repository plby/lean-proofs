/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairedBisectionDegree
import ErdosProblems.Erdos207.BalancedLinkTypicality

/-!
# Producing a typical bipartite link by paired sampling

This file connects paired-cut degrees to the concrete subtype relation used
by the matching theorem.  Upper degree and codegree bounds are inherited
deterministically from the full ambient link graph; only the minimum degree
requires concentration.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace BalancedBisection

lemma pairedCrossDegree_eq_left_linkDegree
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool)
    (center : V) (hcenter : center ∉ W)
    (available : TripleSystemOn V)
    (a : ↥((B.pairedBisection ω).toBipartiteLink center hcenter).left) :
    B.pairedCrossDegree (ambientLinkRelation center available) ω a.1 =
      (relationNeighborsIn
        (linkAvailableRelation
          ((B.pairedBisection ω).toBipartiteLink center hcenter) available)
        univ a).card := by
  let K := (B.pairedBisection ω).toBipartiteLink center hcenter
  have haL : a.1 ∈ B.pairedLeft ω := by
    exact a.2
  rw [card_relationNeighborsIn_linkAvailable_eq_ambient]
  simp only [pairedCrossDegree, haL, if_true]
  congr 1
  ext x
  simp [pairedRightNeighbors, ambientLinkNeighborsIn, K]

lemma pairedCrossDegree_eq_right_linkDegree
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool)
    (center : V) (hcenter : center ∉ W)
    (available : TripleSystemOn V)
    (b : ↥((B.pairedBisection ω).toBipartiteLink center hcenter).right) :
    B.pairedCrossDegree (ambientLinkRelation center available) ω b.1 =
      (relationNeighborsIn
        (transposeRelation (linkAvailableRelation
          ((B.pairedBisection ω).toBipartiteLink center hcenter) available))
        univ b).card := by
  let K := (B.pairedBisection ω).toBipartiteLink center hcenter
  have hbR : b.1 ∈ B.pairedRight ω := by
    simpa only [K, toBipartiteLink_right, pairedBisection_right] using b.2
  have hbNotL : b.1 ∉ B.pairedLeft ω := by
    intro hbL
    exact Finset.disjoint_left.mp (B.disjoint_paired ω) hbL hbR
  rw [card_relationNeighborsIn_transpose_linkAvailable_eq_ambient]
  simp only [pairedCrossDegree, hbNotL, if_false]
  congr 1

lemma ambientLinkNeighborsIn_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {available : TripleSystemOn V}
    {S T : Finset V} (hST : S ⊆ T) (x : V) :
    ambientLinkNeighborsIn center available S x ⊆
      ambientLinkNeighborsIn center available T x := by
  intro y hy
  exact mem_ambientLinkNeighborsIn_iff.mpr
    ⟨hST (mem_ambientLinkNeighborsIn_iff.mp hy).1,
      (mem_ambientLinkNeighborsIn_iff.mp hy).2⟩

lemma ambientLinkCommonNeighborsIn_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {available : TripleSystemOn V}
    {S T : Finset V} (hST : S ⊆ T) (x y : V) :
    ambientLinkCommonNeighborsIn center available S x y ⊆
      ambientLinkCommonNeighborsIn center available T x y := by
  intro z hz
  have hz' := mem_ambientLinkCommonNeighborsIn_iff.mp hz
  exact mem_ambientLinkCommonNeighborsIn_iff.mpr
    ⟨hST hz'.1, hz'.2.1, hz'.2.2⟩

/-- Paired minimum-degree concentration, together with full-link upper
bounds, produces the exact two-oriented degree/codegree package used by the
robust Hall estimate. -/
theorem exists_paired_goodLinkBisection
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W)
    (center : V) (hcenter : center ∉ W)
    (available : TripleSystemOn V) (d D codegree : ℕ)
    (hdegreeUpper : ∀ x ∈ W,
      (ambientLinkNeighborsIn center available W x).card ≤ D)
    (hcodegreeUpper : ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      (ambientLinkCommonNeighborsIn center available W x y).card ≤ codegree)
    (hsmall :
      ∑ x : ↥W,
        2 * ((2 : ℝ≥0) ^
          (d - (B.doubleNeighborPairs
            (ambientLinkRelation center available) x.1
              (B.pairOwner x.1 x.2)).card) *
            (3 / 4 : ℝ≥0) ^
              (B.singleNeighborPairs
                (ambientLinkRelation center available) x.1
                  (B.pairOwner x.1 x.2)).card) < 1) :
    ∃ K : BipartiteLink V,
      K.center = center ∧ K.left ∪ K.right = W ∧
      K.left.card = K.right.card ∧
      HasLinkDegreeCodegreeBounds available K d D codegree := by
  obtain ⟨ω, hmin⟩ := B.exists_pairedBisection_minCrossDegree
    (ambientLinkRelation center available) d hsmall
  let B' := B.pairedBisection ω
  let K := B'.toBipartiteLink center hcenter
  have hpart := B.pairedBisection_isResidualPartition ω center hcenter
  refine ⟨K, hpart.1, hpart.2.1, hpart.2.2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rw [← B.pairedCrossDegree_eq_left_linkDegree ω center hcenter
        available a]
      exact hmin a.1 (by
        have : a.1 ∈ K.left := a.2
        simpa [K, B'] using B'.left_subset this)
    · rw [card_relationNeighborsIn_linkAvailable_eq_ambient]
      have hKR : K.right ⊆ W := by
        intro x hx
        rw [← hpart.2.1]
        exact mem_union_right K.left hx
      exact (card_le_card (ambientLinkNeighborsIn_mono hKR a.1)).trans
        (by
          simpa [K, B'] using hdegreeUpper a.1 (by
            rw [← hpart.2.1]
            exact mem_union_left K.right a.2))
  · intro b
    constructor
    · rw [← B.pairedCrossDegree_eq_right_linkDegree ω center hcenter
        available b]
      exact hmin b.1 (by
        have hbW := B'.left_subset
        have : b.1 ∈ K.right := b.2
        rw [← hpart.2.1]
        exact mem_union_right K.left this)
    · rw [card_relationNeighborsIn_transpose_linkAvailable_eq_ambient]
      have hKL : K.left ⊆ W := by
        intro x hx
        rw [← hpart.2.1]
        exact mem_union_left K.right hx
      exact (card_le_card (ambientLinkNeighborsIn_mono hKL b.1)).trans
        (by
          simpa [K, B'] using hdegreeUpper b.1 (by
            rw [← hpart.2.1]
            exact mem_union_right K.left b.2))
  · intro a a' haa'
    rw [card_relationCommonNeighbors_linkAvailable_eq_ambient]
    have hKR : K.right ⊆ W := by
      intro x hx
      rw [← hpart.2.1]
      exact mem_union_right K.left hx
    exact (card_le_card (ambientLinkCommonNeighborsIn_mono hKR a.1 a'.1)).trans
      (hcodegreeUpper a.1 (by
          rw [← hpart.2.1]
          exact mem_union_left K.right a.2)
        a'.1 (by
          rw [← hpart.2.1]
          exact mem_union_left K.right a'.2)
        (fun h ↦ haa' (Subtype.ext h)))
  · intro b b' hbb'
    rw [card_relationCommonNeighbors_transpose_linkAvailable_eq_ambient]
    have hKL : K.left ⊆ W := by
      intro x hx
      rw [← hpart.2.1]
      exact mem_union_left K.right hx
    exact (card_le_card (ambientLinkCommonNeighborsIn_mono hKL b.1 b'.1)).trans
      (hcodegreeUpper b.1 (by
          rw [← hpart.2.1]
          exact mem_union_right K.left b.2)
        b'.1 (by
          rw [← hpart.2.1]
          exact mem_union_right K.left b'.2)
        (fun h ↦ hbb' (Subtype.ext h)))

end BalancedBisection

end

end Erdos207
