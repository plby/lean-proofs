/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.SimultaneousLinkReservoirSampling
import ErdosProblems.Erdos551.External.Erdos207.TwoSidedRandomRobustMatching

/-!
# Simultaneous robust-Hall sampling

All link reservoirs are represented by one dependent sum of Bernoulli
coordinates.  This file takes a union bound over every center and every
two-sided Hall witness group, proving that all sampled link graphs are
simultaneously robust against bounded left and right deletions.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Embed the pair coordinates of one center into the global dependent-sum
coordinate type. -/
def simultaneousLinkPairAtEmbedding
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V) (o : O) :
    (↥(K o).left × ↥(K o).right) ↪ SimultaneousLinkPair O V K where
  toFun ab := ⟨o, ab⟩
  inj' := by
    intro x y hxy
    cases hxy
    rfl

/-- The local sampled pair set obtained by restricting the global bit vector
to one center. -/
def simultaneousLinkSelectedPairs
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (ω : SimultaneousLinkPair O V K → Bool) (o : O) :
    Finset (↥(K o).left × ↥(K o).right) :=
  Finset.univ.filter fun ab ↦ ω ⟨o, ab⟩ = true

@[simp]
lemma mem_simultaneousLinkSelectedPairs_iff
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    {K : O → BipartiteLink V}
    {ω : SimultaneousLinkPair O V K → Bool} {o : O}
    {ab : ↥(K o).left × ↥(K o).right} :
    ab ∈ simultaneousLinkSelectedPairs K ω o ↔ ω ⟨o, ab⟩ = true := by
  simp [simultaneousLinkSelectedPairs]

/-- A sampled bipartite relation remains perfectly matchable after every
two-sided deletion relation of maximum degree `Delta`. -/
def IsTwoSidedRobustMatchingSample
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta : ℕ) (R : Finset (A × B)) : Prop :=
  ∀ (deleted : A → B → Prop) [DecidableRel deleted],
    (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
    (∀ b, (deletedNeighbors (transposeRelation deleted) b).card ≤ Delta) →
    ∃ f : A → B, Function.Bijective f ∧
      ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a)

/-- Meeting every oriented witness group gives a two-sided robust sample. -/
theorem isTwoSidedRobustMatchingSample_of_meets_groups
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta : ℕ)
    (groups : (o : OrientedSmallHallObstruction A B) →
      OrientedSmallHallGroupIndex Delta o → Finset (A × B))
    (hgroups : ∀ o i, groups o i ⊆ orientedSmallHallCandidates r o)
    (hdisjoint : ∀ o i j, i ≠ j → Disjoint (groups o i) (groups o j))
    (hcard : Fintype.card A = Fintype.card B)
    (R : Finset (A × B))
    (hmeets : ∀ o i, ¬ Disjoint (groups o i) R) :
    IsTwoSidedRobustMatchingSample r Delta R := by
  classical
  intro deleted _ hleftDegree hrightDegree
  have hmany := many_sampled_orientedSmallHallCandidates_of_groups
    r Delta groups hgroups hdisjoint R hmeets
  let sampled : A → B → Prop := fun a b ↦ r a b ∧ (a, b) ∈ R
  obtain ⟨f, hfbij, hf⟩ :=
    exists_bijective_matching_of_twoSided_many_pairs
      sampled deleted Delta hcard hleftDegree hrightDegree
      (by
        intro S T hTS hSsmall
        let o : SmallHallObstruction A B := ⟨⟨(S, T), hTS⟩, hSsmall⟩
        simpa [sampled, orientedSmallHallSize,
          card_orientedSmallHallCandidates_left] using hmany (Sum.inl o))
      (by
        intro S T hTS hSsmall
        let o : SmallHallObstruction B A := ⟨⟨(S, T), hTS⟩, hSsmall⟩
        simpa [sampled, orientedSmallHallSize,
          card_orientedSmallHallCandidates_right] using hmany (Sum.inr o))
  exact ⟨f, hfbij, fun a ↦ ⟨(hf a).1.1, (hf a).1.2, (hf a).2⟩⟩

/-- Index of every robust-Hall witness group at every center. -/
abbrev SimultaneousHallGroupIndex
    (O V : Type*) [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V) (Delta : ℕ) :=
  Σ o : O, Σ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
    OrientedSmallHallGroupIndex Delta h

/-- If no global witness group is missed, the restricted sample at every
center is two-sided robust. -/
theorem all_robust_of_global_groups_meet
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta : ℕ)
    (groups : ∀ o,
      (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right) →
      OrientedSmallHallGroupIndex Delta h →
        Finset (↥(K o).left × ↥(K o).right))
    (hgroups : ∀ o h i,
      groups o h i ⊆ orientedSmallHallCandidates (r o) h)
    (hdisjoint : ∀ o h i j, i ≠ j →
      Disjoint (groups o h i) (groups o h j))
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (ω : SimultaneousLinkPair O V K → Bool)
    (hmeets : ∀ z : SimultaneousHallGroupIndex O V K Delta,
      ¬ Disjoint ((groups z.1 z.2.1 z.2.2).map
        (simultaneousLinkPairAtEmbedding K z.1))
        (FiniteLaw.selectedByBits ω)) :
    ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
      (simultaneousLinkSelectedPairs K ω o) := by
  intro o
  apply isTwoSidedRobustMatchingSample_of_meets_groups
    (r o) Delta (groups o) (hgroups o) (hdisjoint o)
      (by simpa using hbalanced o)
  intro h i
  obtain ⟨x, hxGroup, hxSelected⟩ := Finset.not_disjoint_iff.mp
    (hmeets ⟨o, h, i⟩)
  obtain ⟨ab, habGroup, habx⟩ := mem_map.mp hxGroup
  subst x
  apply Finset.not_disjoint_iff.mpr
  refine ⟨ab, habGroup, ?_⟩
  exact mem_simultaneousLinkSelectedPairs_iff.mpr
    (FiniteLaw.mem_selectedByBits_iff.mp hxSelected)

/-- Finite union bound showing that every center is simultaneously robust. -/
theorem independentBits_probability_not_all_twoSidedRobust_le
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta groupSize : ℕ)
    (groups : ∀ o,
      (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right) →
      OrientedSmallHallGroupIndex Delta h →
        Finset (↥(K o).left × ↥(K o).right))
    (hgroupCard : ∀ o h i, (groups o h i).card = groupSize)
    (hgroups : ∀ o h i,
      groups o h i ⊆ orientedSmallHallCandidates (r o) h)
    (hdisjoint : ∀ o h i j, i ≠ j →
      Disjoint (groups o h i) (groups o h j))
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun ω ↦
        ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
          (simultaneousLinkSelectedPairs K ω o)) ≤
      (Fintype.card (SimultaneousHallGroupIndex O V K Delta) : ℝ≥0) *
        (1 - sigma) ^ groupSize := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let Missing : SimultaneousHallGroupIndex O V K Delta →
      (SimultaneousLinkPair O V K → Bool) → Prop := fun z ω ↦
    Disjoint ((groups z.1 z.2.1 z.2.2).map
      (simultaneousLinkPairAtEmbedding K z.1))
      (FiniteLaw.selectedByBits ω)
  calc
    L.probability (fun ω ↦
        ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
          (simultaneousLinkSelectedPairs K ω o)) ≤
        L.probability (fun ω ↦ ∃ z ∈
          (univ : Finset (SimultaneousHallGroupIndex O V K Delta)),
            Missing z ω) := by
      apply L.probability_mono
      intro ω hnot
      by_contra hnone
      push Not at hnone
      apply hnot
      apply all_robust_of_global_groups_meet K r Delta groups hgroups
        hdisjoint hbalanced ω
      intro z
      exact hnone z (mem_univ z)
    _ ≤ ∑ z ∈ (univ : Finset
          (SimultaneousHallGroupIndex O V K Delta)),
        L.probability (Missing z) :=
      L.probability_exists_le univ Missing
    _ = ∑ _z ∈ (univ : Finset
          (SimultaneousHallGroupIndex O V K Delta)),
        (1 - sigma) ^ groupSize := by
      apply sum_congr rfl
      intro z _hz
      rw [FiniteLaw.independentBits_probability_disjoint_selected]
      simp [hgroupCard z.1 z.2.1 z.2.2]
    _ = (Fintype.card (SimultaneousHallGroupIndex O V K Delta) : ℝ≥0) *
        (1 - sigma) ^ groupSize := by simp

/-- Candidate-count specialization: manufacture all witness groups and then
apply the simultaneous union bound. -/
theorem independentBits_probability_not_all_twoSidedRobust_le_of_candidates
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta groupSize : ℕ)
    (hcandidates : ∀ o,
      ∀ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
        (Delta * orientedSmallHallSize h + 1) * groupSize ≤
          (orientedSmallHallCandidates (r o) h).card)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun ω ↦
        ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
          (simultaneousLinkSelectedPairs K ω o)) ≤
      (Fintype.card (SimultaneousHallGroupIndex O V K Delta) : ℝ≥0) *
        (1 - sigma) ^ groupSize := by
  classical
  choose groups hgroups using fun o h ↦
    exists_pairwiseDisjoint_groups_of_mul_le_card
      (orientedSmallHallCandidates (r o) h)
      (Delta * orientedSmallHallSize h + 1) groupSize (hcandidates o h)
  apply independentBits_probability_not_all_twoSidedRobust_le
    K r Delta groupSize groups
  · intro o h i
    exact ((hgroups o h).1 i).1
  · intro o h i
    exact ((hgroups o h).1 i).2
  · intro o h
    exact (hgroups o h).2
  · exact hbalanced

end

end Erdos207
