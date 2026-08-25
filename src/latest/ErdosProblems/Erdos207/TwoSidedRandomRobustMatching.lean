/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoSidedRobustMatching

/-!
# Random sparsification for two-sided robust Hall

This is the balanced, two-sided version of `RandomRobustMatching`.  Its bad
events are only the Hall obstructions up to rounded-up half size, in both
orientations.  This is precisely the robust perfect-matching mechanism used
for KSSS link graphs.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- A Hall obstruction whose left set has size at most rounded-up half of
the ambient left side. -/
abbrev SmallHallObstruction
    (A B : Type*) [Fintype A] [DecidableEq A] [DecidableEq B] :=
  {o : HallObstruction A B // 2 * o.1.1.card ≤ Fintype.card A + 1}

/-- The two possible orientations of a small Hall obstruction. -/
abbrev OrientedSmallHallObstruction
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :=
  SmallHallObstruction A B ⊕ SmallHallObstruction B A

/-- Size of the obstruction's left set in its selected orientation. -/
def orientedSmallHallSize
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    OrientedSmallHallObstruction A B → ℕ
  | Sum.inl o => o.1.1.1.card
  | Sum.inr o => o.1.1.1.card

/-- Index set for the independent witness groups attached to an oriented
small Hall obstruction. -/
abbrev OrientedSmallHallGroupIndex
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (Delta : ℕ) (o : OrientedSmallHallObstruction A B) :=
  Fin (Delta * orientedSmallHallSize o + 1)

/-- Coordinate-swap embedding used to regard right-oriented relation-pairs
as coordinates of the original sampled relation. -/
def swapPairEmbedding (A B : Type*) : (B × A) ↪ (A × B) where
  toFun ba := (ba.2, ba.1)
  inj' := by
    intro x y h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- Candidate pairs for either orientation, always represented in the
original sample space `A × B`. -/
noncomputable def orientedSmallHallCandidates
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] :
    OrientedSmallHallObstruction A B → Finset (A × B)
  | Sum.inl o => relationPairsLeaving r o.1.1.1 o.1.1.2
  | Sum.inr o =>
      (relationPairsLeaving (transposeRelation r) o.1.1.1 o.1.1.2).map
        (swapPairEmbedding A B)

lemma card_orientedSmallHallCandidates_left
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (o : SmallHallObstruction A B) :
    (orientedSmallHallCandidates r (Sum.inl o)).card =
      (relationPairsLeaving r o.1.1.1 o.1.1.2).card := rfl

lemma card_orientedSmallHallCandidates_right
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (o : SmallHallObstruction B A) :
    (orientedSmallHallCandidates r (Sum.inr o)).card =
      (relationPairsLeaving (transposeRelation r)
        o.1.1.1 o.1.1.2).card := by
  simp [orientedSmallHallCandidates]

@[simp]
lemma mem_orientedSmallHallCandidates_left
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (o : SmallHallObstruction A B) (a : A) (b : B) :
    (a, b) ∈ orientedSmallHallCandidates r (Sum.inl o) ↔
      a ∈ o.1.1.1 ∧ b ∉ o.1.1.2 ∧ r a b := by
  exact mem_relationPairsLeaving_iff r

@[simp]
lemma mem_orientedSmallHallCandidates_right
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (o : SmallHallObstruction B A) (a : A) (b : B) :
    (a, b) ∈ orientedSmallHallCandidates r (Sum.inr o) ↔
      b ∈ o.1.1.1 ∧ a ∉ o.1.1.2 ∧ r a b := by
  classical
  constructor
  · intro h
    obtain ⟨ba, hba, hswap⟩ := mem_map.mp h
    have hfst : ba.2 = a := congrArg Prod.fst hswap
    have hsnd : ba.1 = b := congrArg Prod.snd hswap
    have hc := mem_relationPairsLeaving_iff (transposeRelation r) |>.mp hba
    simpa only [hfst, hsnd, transposeRelation_apply] using hc
  · rintro ⟨hb, ha, hr⟩
    apply mem_map.mpr
    refine ⟨(b, a), mem_relationPairsLeaving_iff
      (transposeRelation r) |>.mpr ?_, rfl⟩
    exact ⟨hb, ha, hr⟩

/-- Meeting every disjoint witness group gives enough sampled candidates in
both small-obstruction orientations. -/
theorem many_sampled_orientedSmallHallCandidates_of_groups
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (Delta : ℕ)
    (groups : (o : OrientedSmallHallObstruction A B) →
      OrientedSmallHallGroupIndex Delta o → Finset (A × B))
    (hgroups : ∀ o i, groups o i ⊆ orientedSmallHallCandidates r o)
    (hdisjoint : ∀ o i j, i ≠ j → Disjoint (groups o i) (groups o j))
    (R : Finset (A × B))
    (hmeets : ∀ o i, ¬ Disjoint (groups o i) R) :
    ∀ o : OrientedSmallHallObstruction A B,
      Delta * orientedSmallHallSize o <
        (orientedSmallHallCandidates
          (fun a b ↦ r a b ∧ (a, b) ∈ R) o).card := by
  classical
  intro o
  let witness : OrientedSmallHallGroupIndex Delta o → A × B := fun i ↦
    Classical.choose (Finset.not_disjoint_iff.mp (hmeets o i))
  have hwitnessGroup : ∀ i, witness i ∈ groups o i := by
    intro i
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets o i))).1
  have hwitnessR : ∀ i, witness i ∈ R := by
    intro i
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets o i))).2
  have hinjective : Function.Injective witness := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint o i j hne)
      (hwitnessGroup i) (hij ▸ hwitnessGroup j)
  have himage : univ.image witness ⊆
      orientedSmallHallCandidates
        (fun a b ↦ r a b ∧ (a, b) ∈ R) o := by
    intro e he
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp he
    rcases o with o | o
    · rw [mem_orientedSmallHallCandidates_left]
      have hc := hgroups (Sum.inl o) i (hwitnessGroup i)
      rw [mem_orientedSmallHallCandidates_left] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2, hwitnessR i⟩
    · rw [mem_orientedSmallHallCandidates_right]
      have hc := hgroups (Sum.inr o) i (hwitnessGroup i)
      rw [mem_orientedSmallHallCandidates_right] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2, hwitnessR i⟩
  have hcard : Delta * orientedSmallHallSize o + 1 ≤
      (orientedSmallHallCandidates
        (fun a b ↦ r a b ∧ (a, b) ∈ R) o).card := by
    calc
      Delta * orientedSmallHallSize o + 1 = (univ.image witness).card := by
        rw [card_image_of_injective _ hinjective, card_univ,
          Fintype.card_fin]
      _ ≤ _ := card_le_card himage
  omega

/-- Exact finite random two-sided robust-matching theorem. -/
theorem exists_bijective_twoSided_robust_matching_sample
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card)
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : NNReal) *
          (1 - sampleProbability) ^ groupSize < 1)
    (hcard : Fintype.card A = Fintype.card B) :
    ∃ R : Finset (A × B),
      ∀ (deleted : A → B → Prop) [DecidableRel deleted],
        (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
        (∀ b, (deletedNeighbors (transposeRelation deleted) b).card ≤ Delta) →
        ∃ f : A → B, Function.Bijective f ∧
          ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a) := by
  classical
  choose groups hgroups using fun o : OrientedSmallHallObstruction A B ↦
    exists_pairwiseDisjoint_groups_of_mul_le_card
      (orientedSmallHallCandidates r o)
      (Delta * orientedSmallHallSize o + 1) groupSize (hcandidates o)
  let indices : Finset
      (Σ o : OrientedSmallHallObstruction A B,
        OrientedSmallHallGroupIndex Delta o) := univ
  obtain ⟨R, hR⟩ :=
    FiniteLaw.exists_selected_meets_all_of_sum_avoidance_lt_one
      (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)
      indices (fun z ↦ groups z.1 z.2) (by
        calc
          ∑ z ∈ indices,
              ∏ _e ∈ groups z.1 z.2, (1 - sampleProbability) =
              (Fintype.card
                (Σ o : OrientedSmallHallObstruction A B,
                  OrientedSmallHallGroupIndex Delta o) : NNReal) *
                (1 - sampleProbability) ^ groupSize := by
            simp_rw [Finset.prod_const, (hgroups _).1 _ |>.1]
            simp [indices]
          _ < 1 := hsmall)
  refine ⟨R, ?_⟩
  intro deleted _ hleftDegree hrightDegree
  have hmany := many_sampled_orientedSmallHallCandidates_of_groups
    r Delta groups (fun o i ↦ (hgroups o).1 i |>.2)
    (fun o ↦ (hgroups o).2) R
    (fun o i ↦ hR ⟨o, i⟩ (by simp [indices]))
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

end Erdos207
