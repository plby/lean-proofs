/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.BipartiteRelationCounting

/-!
# Two-sided robust Hall for balanced bipartite relations

For a balanced bipartite graph it is enough to rule out Hall obstructions of
size at most `ceil(m / 2)` on both sides.  This is the exact deterministic
form used by KSSS: small left obstructions and small right obstructions are
handled by the same sparsified undirected link graph.  The distinction is
essential for sparse relations, where a large one-sided obstruction need not
have a number of escaping pairs proportional to its left size.
-/

namespace Erdos207

open Finset

/-- Every Hall obstruction whose left set has size at most the rounded-up
half of its ambient side has a surviving escaping relation-pair. -/
def SurvivesSmallHallObstructions
    {A B : Type*} [Fintype A]
    (r deleted : A → B → Prop) : Prop :=
  ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
    2 * S.card ≤ Fintype.card A + 1 →
    ∃ a ∈ S, ∃ b ∉ T, r a b ∧ ¬ deleted a b

/-- The transposed relation and deletion predicate. -/
def transposeRelation
    {A B : Type*} (r : A → B → Prop) : B → A → Prop :=
  fun b a ↦ r a b

noncomputable instance transposeRelation.instDecidableRel
    {A B : Type*} (r : A → B → Prop) [DecidableRel r] :
    DecidableRel (transposeRelation r) := by
  intro b a
  exact Classical.propDecidable _

@[simp]
lemma transposeRelation_apply
    {A B : Type*} (r : A → B → Prop) (b : B) (a : A) :
    transposeRelation r b a ↔ r a b := Iff.rfl

/-- Two-sided small-obstruction survival implies the full one-sided robust
Hall condition. -/
theorem survivesEveryHallObstruction_of_twoSided_small
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r deleted : A → B → Prop)
    (hcard : Fintype.card A = Fintype.card B)
    (hleft : SurvivesSmallHallObstructions r deleted)
    (hright : SurvivesSmallHallObstructions
      (transposeRelation r) (transposeRelation deleted)) :
    SurvivesEveryHallObstruction r deleted := by
  intro S T hTS
  classical
  by_cases hsmall : 2 * (T.card + 1) ≤ Fintype.card A + 1
  · have hsize : T.card + 1 ≤ S.card := by omega
    obtain ⟨S₀, hS₀S, hS₀card⟩ :=
      Finset.exists_subset_card_eq hsize
    obtain ⟨a, haS₀, b, hbT, hr, hdel⟩ :=
      hleft S₀ T (by omega) (by simpa only [hS₀card] using hsmall)
    exact ⟨a, hS₀S haS₀, b, hbT, hr, hdel⟩
  · let U : Finset B := univ \ T
    let X : Finset A := univ \ S
    have hTcard : T.card ≤ Fintype.card B := by
      simpa using T.card_le_univ
    have hScard : S.card ≤ Fintype.card A := by
      simpa using S.card_le_univ
    have hUcard : U.card = Fintype.card B - T.card := by
      simp [U, card_sdiff_of_subset (subset_univ T)]
    have hXcard : X.card = Fintype.card A - S.card := by
      simp [X, card_sdiff_of_subset (subset_univ S)]
    have hUX : X.card < U.card := by
      rw [hUcard, hXcard, ← hcard]
      omega
    have hUsmall : 2 * U.card ≤ Fintype.card B + 1 := by
      rw [hUcard, ← hcard]
      omega
    obtain ⟨b, hbU, a, haX, hr, hdel⟩ :=
      hright U X hUX hUsmall
    have hbT : b ∉ T := (mem_sdiff.mp hbU).2
    have haS : a ∈ S := by
      by_contra ha
      exact haX (mem_sdiff.mpr ⟨mem_univ _, ha⟩)
    exact ⟨a, haS, b, hbT, hr, hdel⟩

/-- The two-sided small-obstruction criterion supplies a perfect matching
after deletion. -/
theorem exists_bijective_matching_of_twoSided_small
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r deleted : A → B → Prop)
    [DecidableRel r] [DecidableRel deleted]
    (hcard : Fintype.card A = Fintype.card B)
    (hleft : SurvivesSmallHallObstructions r deleted)
    (hright : SurvivesSmallHallObstructions
      (transposeRelation r) (transposeRelation deleted)) :
    ∃ f : A → B, Function.Bijective f ∧
      ∀ a, r a (f a) ∧ ¬ deleted a (f a) := by
  exact exists_bijective_matching_after_deletion r deleted hcard
    (survivesEveryHallObstruction_of_twoSided_small r deleted hcard
      hleft hright)

/-- Candidate pairs leaving a small Hall obstruction. -/
def SmallHallCandidateBound
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize : ℕ) : Prop :=
  ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
    2 * S.card ≤ Fintype.card A + 1 →
    (Delta * S.card + 1) * groupSize ≤
      (relationPairsLeaving r S T).card

/-- More than `Delta * |S|` escaping pairs at every small obstruction
survive any deletion relation of maximum left degree `Delta`. -/
theorem survivesSmallHallObstructions_of_many_pairs
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r deleted : A → B → Prop) [DecidableRel r] [DecidableRel deleted]
    (Delta : ℕ)
    (hdeleted : ∀ a, (deletedNeighbors deleted a).card ≤ Delta)
    (hmany : ∀ S : Finset A, ∀ T : Finset B,
      T.card < S.card → 2 * S.card ≤ Fintype.card A + 1 →
      Delta * S.card < (relationPairsLeaving r S T).card) :
    SurvivesSmallHallObstructions r deleted := by
  intro S T hTS hsmall
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
        Delta * S.card := by
    calc
      (S.biUnion fun a ↦
          (deletedNeighbors deleted a).image fun b ↦ (a, b)).card ≤
          ∑ a ∈ S,
            ((deletedNeighbors deleted a).image fun b ↦ (a, b)).card :=
        card_biUnion_le
      _ ≤ ∑ _a ∈ S, Delta := by
        apply sum_le_sum
        intro a ha
        exact card_image_le.trans (hdeleted a)
      _ = Delta * S.card := by simp [mul_comm]
  exact (not_lt_of_ge ((card_le_card hsubset).trans hcardUnion))
    (hmany S T hTS hsmall)

/-- Two-sided small candidate counts and two-sided maximum deletion degree
give a bijective surviving matching. -/
theorem exists_bijective_matching_of_twoSided_many_pairs
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r deleted : A → B → Prop)
    [DecidableRel r] [DecidableRel deleted]
    (Delta : ℕ) (hcard : Fintype.card A = Fintype.card B)
    (hleftDegree : ∀ a, (deletedNeighbors deleted a).card ≤ Delta)
    (hrightDegree : ∀ b,
      (deletedNeighbors (transposeRelation deleted) b).card ≤ Delta)
    (hleftPairs : ∀ S : Finset A, ∀ T : Finset B,
      T.card < S.card → 2 * S.card ≤ Fintype.card A + 1 →
      Delta * S.card < (relationPairsLeaving r S T).card)
    (hrightPairs : ∀ S : Finset B, ∀ T : Finset A,
      T.card < S.card → 2 * S.card ≤ Fintype.card B + 1 →
      Delta * S.card <
        (relationPairsLeaving (transposeRelation r) S T).card) :
    ∃ f : A → B, Function.Bijective f ∧
      ∀ a, r a (f a) ∧ ¬ deleted a (f a) := by
  apply exists_bijective_matching_of_twoSided_small r deleted hcard
  · exact survivesSmallHallObstructions_of_many_pairs r deleted Delta
      hleftDegree hleftPairs
  · exact survivesSmallHallObstructions_of_many_pairs
      (transposeRelation r) (transposeRelation deleted) Delta
      hrightDegree hrightPairs

/-- A minimum left degree handles the genuinely small regime.  The scalar
hypothesis says that after excluding every vertex of `T`, enough candidates
remain to form all robust-sampling groups. -/
theorem smallHallCandidateBound_of_left_degree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize d cutoff : ℕ)
    (hdegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hscalar : Delta * groupSize + groupSize ≤ d - cutoff) :
    ∀ S : Finset A, ∀ T : Finset B,
      T.card < S.card → S.card ≤ cutoff →
      (Delta * S.card + 1) * groupSize ≤
        (relationPairsLeaving r S T).card := by
  intro S T hTS hScut
  have hnonempty : 1 ≤ S.card := by omega
  apply le_trans _ (card_relationPairsLeaving_ge_of_left_degree
    r d hdegree S T)
  calc
    (Delta * S.card + 1) * groupSize =
        Delta * groupSize * S.card + groupSize := by ring
    _ ≤ (Delta * groupSize + groupSize) * S.card := by nlinarith
    _ ≤ (d - cutoff) * S.card :=
      Nat.mul_le_mul_right _ hscalar
    _ ≤ S.card * (d - T.card) := by
      rw [mul_comm (d - cutoff) S.card]
      apply Nat.mul_le_mul_left
      exact Nat.sub_le_sub_left (by omega) d

end Erdos207
