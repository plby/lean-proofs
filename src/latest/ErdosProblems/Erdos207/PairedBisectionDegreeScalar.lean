/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairedLinkBisection

/-!
# Scalar degree concentration for paired bisections

The exact paired-sampling estimate records, for every vertex, the numbers of
base pairs containing two and one ambient neighbors.  This file eliminates
those auxiliary counts.  Apart from the pair containing the vertex itself,
every ambient neighbor belongs to either a two-neighbor pair or the unique
neighbor endpoint of a one-neighbor pair.  Consequently

`degree ≤ 2 * doublePairs + singlePairs + 2`.

If the full ambient degree is at least `m` and `doublePairs < d`, this forces
at least `m - 2*d` one-neighbor pairs.  The exact one-vertex estimate then has
the uniform upper bound

`2 * 2^d * (3/4)^(m - 2*d)`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace BalancedBisection

/-- The base pair selected by `pairOwner` really contains the supplied
vertex. -/
lemma pairOwner_endpoint
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (x : V) (hx : x ∈ W) :
    x = (B.pairOwner x hx).1 ∨
      x = (B.pairEquiv (B.pairOwner x hx)).1 := by
  by_cases hxL : x ∈ B.left
  · left
    simp [pairOwner, hxL]
  · right
    let b : ↥B.right := ⟨x, mem_sdiff.mpr ⟨hx, hxL⟩⟩
    have h := congrArg Subtype.val (B.pairEquiv.apply_symm_apply b)
    simpa [pairOwner, hxL, b] using h.symm

/-- The related endpoint of a pair having exactly one neighbor of `x`. -/
def singleNeighborVertex
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (a : ↥B.left) : V :=
  if r x a.1 then a.1 else (B.pairEquiv a).1

lemma relation_singleNeighborVertex
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner a : ↥B.left)
    (ha : a ∈ B.singleNeighborPairs r x owner) :
    r x (B.singleNeighborVertex r x a) := by
  have hs := (mem_filter.mp ha).2
  rcases hs with ⟨haL, _haR⟩ | ⟨haL, haR⟩
  · simpa [singleNeighborVertex, haL] using haL
  · simpa [singleNeighborVertex, haL] using haR

/-- A finite cover of all related vertices in `W`, sorted by their base-pair
type, with the owner pair kept as a two-element error term. -/
def categorizedNeighborCover
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) : Finset V :=
  (B.doubleNeighborPairs r x owner).image Subtype.val ∪
    (B.doubleNeighborPairs r x owner).image
      (fun a ↦ (B.pairEquiv a).1) ∪
    (B.singleNeighborPairs r x owner).image
      (B.singleNeighborVertex r x) ∪
    {owner.1, (B.pairEquiv owner).1}

lemma ambientNeighbors_subset_categorizedNeighborCover
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) :
    W.filter (r x) ⊆ B.categorizedNeighborCover r x owner := by
  intro y hy
  have hyW : y ∈ W := (mem_filter.mp hy).1
  have hry : r x y := (mem_filter.mp hy).2
  let a := B.pairOwner y hyW
  have hay : y = a.1 ∨ y = (B.pairEquiv a).1 := by
    simpa [a] using B.pairOwner_endpoint y hyW
  by_cases hao : a = owner
  · rw [hao] at hay
    rcases hay with hay | hay
    · rw [hay]
      exact mem_union_right _ (by simp)
    · rw [hay]
      exact mem_union_right _ (by simp)
  · have haExcept : a ∈ B.pairIndicesExcept owner := by
      exact mem_erase.mpr ⟨hao, mem_univ a⟩
    rcases hay with hay | hay
    · have hra : r x a.1 := by rwa [hay] at hry
      by_cases hrb : r x (B.pairEquiv a).1
      · have haD : a ∈ B.doubleNeighborPairs r x owner := by
          exact mem_filter.mpr ⟨haExcept, hra, hrb⟩
        rw [hay]
        exact mem_union_left _ (mem_union_left _
          (mem_union_left _ (mem_image.mpr ⟨a, haD, rfl⟩)))
      · have haS : a ∈ B.singleNeighborPairs r x owner := by
          exact mem_filter.mpr ⟨haExcept, Or.inl ⟨hra, hrb⟩⟩
        rw [hay]
        exact mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨a, haS, by simp [singleNeighborVertex, hra]⟩))
    · have hrb : r x (B.pairEquiv a).1 := by rwa [hay] at hry
      by_cases hra : r x a.1
      · have haD : a ∈ B.doubleNeighborPairs r x owner := by
          exact mem_filter.mpr ⟨haExcept, hra, hrb⟩
        rw [hay]
        exact mem_union_left _ (mem_union_left _
          (mem_union_right _ (mem_image.mpr ⟨a, haD, rfl⟩)))
      · have haS : a ∈ B.singleNeighborPairs r x owner := by
          exact mem_filter.mpr ⟨haExcept, Or.inr ⟨hra, hrb⟩⟩
        rw [hay]
        exact mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨a, haS, by simp [singleNeighborVertex, hra]⟩))

/-- Pair classification bounds the full degree by twice the number of
two-neighbor pairs, plus the number of one-neighbor pairs, plus the two
endpoints of the owner pair. -/
lemma card_filter_relation_le_double_single
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) :
    (W.filter (r x)).card ≤
      2 * (B.doubleNeighborPairs r x owner).card +
        (B.singleNeighborPairs r x owner).card + 2 := by
  let D := B.doubleNeighborPairs r x owner
  let S := B.singleNeighborPairs r x owner
  let DL : Finset V := D.image Subtype.val
  let DR : Finset V := D.image (fun a ↦ (B.pairEquiv a).1)
  let SN : Finset V := S.image (B.singleNeighborVertex r x)
  let O : Finset V := {owner.1, (B.pairEquiv owner).1}
  have hsub : W.filter (r x) ⊆ DL ∪ DR ∪ SN ∪ O := by
    simpa [categorizedNeighborCover, D, S, DL, DR, SN, O] using
      B.ambientNeighbors_subset_categorizedNeighborCover r x owner
  have hDL : DL.card ≤ D.card := by
    exact card_image_le
  have hDR : DR.card ≤ D.card := by
    exact card_image_le
  have hSN : SN.card ≤ S.card := by
    exact card_image_le
  have hO : O.card ≤ 2 := by
    simpa [O] using card_insert_le owner.1 {(B.pairEquiv owner).1}
  calc
    (W.filter (r x)).card ≤ (DL ∪ DR ∪ SN ∪ O).card := card_le_card hsub
    _ ≤ (DL ∪ DR ∪ SN).card + O.card :=
      card_union_le (DL ∪ DR ∪ SN) O
    _ ≤ ((DL ∪ DR).card + SN.card) + O.card := by
      exact Nat.add_le_add_right (card_union_le (DL ∪ DR) SN) O.card
    _ ≤ ((DL.card + DR.card) + SN.card) + O.card := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (card_union_le DL DR) SN.card) O.card
    _ ≤ 2 * D.card + S.card + 2 := by omega

/-- The deterministic contribution of the two-neighbor pairs is always a
lower bound for the sampled cross degree. -/
lemma doubleNeighborPairs_card_le_pairedCrossDegree
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (owner : ↥B.left) (ω : ↥B.left → Bool) :
    (B.doubleNeighborPairs r x owner).card ≤
      B.pairedCrossDegree r ω x := by
  by_cases hxL : x ∈ B.pairedLeft ω
  · have h := B.double_add_matched_le_pairedRightNeighbors r x owner ω
    simp only [pairedCrossDegree, hxL, if_true]
    omega
  · have h := B.double_add_matched_le_pairedLeftNeighbors r x owner ω
    simp only [pairedCrossDegree, hxL, if_false]
    omega

/-- A full-degree lower bound turns the exact pair statistics into a uniform
one-vertex lower-tail estimate. -/
theorem pairedLaw_probability_crossDegree_lt_le_scalar
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (hx : x ∈ W) (m d : ℕ)
    (hdegree : m ≤ (W.filter (r x)).card) :
    (B.pairedLaw).probability (fun ω ↦ B.pairedCrossDegree r ω x < d) ≤
      2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d) := by
  let owner := B.pairOwner x hx
  let D := (B.doubleNeighborPairs r x owner).card
  let S := (B.singleNeighborPairs r x owner).card
  by_cases hdD : d ≤ D
  · have hempty : ∀ ω, ¬ B.pairedCrossDegree r ω x < d := by
      intro ω hbad
      exact (not_lt_of_ge (hdD.trans
        (B.doubleNeighborPairs_card_le_pairedCrossDegree r x owner ω))) hbad
    calc
      (B.pairedLaw).probability
          (fun ω ↦ B.pairedCrossDegree r ω x < d) = 0 := by
        apply le_antisymm
        · rw [← B.pairedLaw.probability_false]
          exact B.pairedLaw.probability_mono (fun ω h ↦ (hempty ω h).elim)
        · exact zero_le
      _ ≤ 2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d) := zero_le
  · have hDd : D < d := Nat.lt_of_not_ge hdD
    have hcount := B.card_filter_relation_le_double_single r x owner
    have hS : m - 2 * d ≤ S := by
      omega
    have hpowTwo : (2 : ℝ≥0) ^ (d - D) ≤ (2 : ℝ≥0) ^ d := by
      exact pow_le_pow_right' (by norm_num) (Nat.sub_le d D)
    have hpowThree : (3 / 4 : ℝ≥0) ^ S ≤
        (3 / 4 : ℝ≥0) ^ (m - 2 * d) := by
      exact pow_le_pow_right_of_le_one'
        ((div_le_one (by norm_num : (0 : ℝ≥0) < 4)).2
          (by norm_num : (3 : ℝ≥0) ≤ 4)) hS
    calc
      (B.pairedLaw).probability
          (fun ω ↦ B.pairedCrossDegree r ω x < d) ≤
          2 * ((2 : ℝ≥0) ^ (d - D) * (3 / 4 : ℝ≥0) ^ S) := by
        simpa [D, S, owner] using
          B.pairedLaw_probability_crossDegree_lt_le r x owner d
      _ ≤ 2 * ((2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hpowTwo hpowThree zero_le zero_le) zero_le
      _ = 2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d) := by
        ring

/-- A single scalar inequality gives one paired balanced bisection whose
cross degree is at least `d` at every vertex. -/
theorem exists_pairedBisection_minCrossDegree_of_scalar
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (m d : ℕ)
    (hdegree : ∀ x ∈ W, m ≤ (W.filter (r x)).card)
    (hsmall : (W.card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ ω : ↥B.left → Bool,
      ∀ x ∈ W, d ≤ B.pairedCrossDegree r ω x := by
  classical
  let Bad : ↥W → (↥B.left → Bool) → Prop :=
    fun x ω ↦ B.pairedCrossDegree r ω x.1 < d
  let q : ℝ≥0 :=
    2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)
  have hprob : ∑ x : ↥W, (B.pairedLaw).probability (Bad x) ≤
      (W.card : ℝ≥0) * q := by
    calc
      ∑ x : ↥W, (B.pairedLaw).probability (Bad x) ≤
          ∑ _x : ↥W, q := by
        apply Finset.sum_le_sum
        intro x _hx
        exact B.pairedLaw_probability_crossDegree_lt_le_scalar r x.1 x.2
          m d (hdegree x.1 x.2)
      _ = (W.card : ℝ≥0) * q := by
        rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  obtain ⟨ω, hω⟩ :=
    (B.pairedLaw).exists_avoiding_of_sum_probability_lt_one
      (univ : Finset ↥W) Bad (by
        apply hprob.trans_lt
        simpa [q] using hsmall)
  exact ⟨ω, fun x hx ↦ Nat.le_of_not_gt (hω ⟨x, hx⟩ (mem_univ _))⟩

/-- Scalar paired concentration plus full-link upper degree and codegree
bounds produces the exact typical-link package used by robust Hall. -/
theorem exists_paired_goodLinkBisection_of_scalar
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W)
    (center : V) (hcenter : center ∉ W)
    (available : TripleSystemOn V) (m d D codegree : ℕ)
    (hdegreeLower : ∀ x ∈ W,
      m ≤ (ambientLinkNeighborsIn center available W x).card)
    (hdegreeUpper : ∀ x ∈ W,
      (ambientLinkNeighborsIn center available W x).card ≤ D)
    (hcodegreeUpper : ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      (ambientLinkCommonNeighborsIn center available W x y).card ≤ codegree)
    (hsmall : (W.card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ K : BipartiteLink V,
      K.center = center ∧ K.left ∪ K.right = W ∧
      K.left.card = K.right.card ∧
      HasLinkDegreeCodegreeBounds available K d D codegree := by
  have hfilter : ∀ x ∈ W, m ≤
      (W.filter (ambientLinkRelation center available x)).card := by
    intro x hx
    simpa [ambientLinkNeighborsIn] using hdegreeLower x hx
  obtain ⟨ω, hmin⟩ := B.exists_pairedBisection_minCrossDegree_of_scalar
    (ambientLinkRelation center available) m d hfilter hsmall
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
        rw [← hpart.2.1]
        exact mem_union_left K.right a.2)
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
        rw [← hpart.2.1]
        exact mem_union_right K.left b.2)
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
