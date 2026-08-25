/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoSidedRandomRobustMatching

/-!
# Robust Hall sampling with an additional high-probability event

The KSSS link reservoir must simultaneously meet every robust-Hall witness
group and satisfy rooted-threat cutoffs.  Requiring the cutoff for every
possible reservoir is unnecessarily strong.  This file puts an arbitrary
reservoir predicate into the same finite union bound as the Hall events.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- Independent sampling can meet every prescribed group while also
satisfying any extra event whose failure probability fits in the remaining
union-bound budget. -/
theorem FiniteLaw.exists_selected_meets_all_and_good
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (S : Finset J) (groups : J → Finset I)
    (Good : Finset I → Prop) (epsilon : ℝ≥0)
    (hbad : (FiniteLaw.independentBits p hp).probability
      (fun omega ↦ ¬ Good (FiniteLaw.selectedByBits omega)) ≤ epsilon)
    (hsmall : epsilon +
      ∑ j ∈ S, ∏ i ∈ groups j, (1 - p i) < 1) :
    ∃ R : Finset I, Good R ∧
      ∀ j ∈ S, ¬ Disjoint (groups j) R := by
  let L := FiniteLaw.independentBits p hp
  let missing : (I → Bool) → Prop := fun omega ↦
    ∃ j ∈ S, Disjoint (groups j) (FiniteLaw.selectedByBits omega)
  have hmissing : L.probability missing ≤
      ∑ j ∈ S, ∏ i ∈ groups j, (1 - p i) := by
    calc
      L.probability missing ≤
          ∑ j ∈ S, L.probability (fun omega ↦
            Disjoint (groups j) (FiniteLaw.selectedByBits omega)) :=
        L.probability_exists_le S (fun j omega ↦
          Disjoint (groups j) (FiniteLaw.selectedByBits omega))
      _ = ∑ j ∈ S, ∏ i ∈ groups j, (1 - p i) := by
        apply sum_congr rfl
        intro j _hj
        exact FiniteLaw.independentBits_probability_disjoint_selected
          p hp (groups j)
  have htotal : L.probability (fun omega ↦
      ¬ Good (FiniteLaw.selectedByBits omega) ∨ missing omega) < 1 := by
    calc
      L.probability (fun omega ↦
          ¬ Good (FiniteLaw.selectedByBits omega) ∨ missing omega) ≤
          L.probability (fun omega ↦
            ¬ Good (FiniteLaw.selectedByBits omega)) +
            L.probability missing := L.probability_or_le _ _
      _ ≤ epsilon + ∑ j ∈ S,
          ∏ i ∈ groups j, (1 - p i) := add_le_add hbad hmissing
      _ < 1 := hsmall
  have hexists : ∃ omega : I → Bool,
      ¬ (¬ Good (FiniteLaw.selectedByBits omega) ∨ missing omega) := by
    by_contra hnone
    push Not at hnone
    have hall : (fun omega ↦
        ¬ Good (FiniteLaw.selectedByBits omega) ∨ missing omega) =
        (fun _ : I → Bool ↦ True) := by
      funext omega
      exact propext ⟨fun _ ↦ trivial, fun _ ↦ hnone omega⟩
    rw [hall, L.probability_true] at htotal
    exact (lt_irrefl 1 htotal)
  obtain ⟨omega, homega⟩ := hexists
  refine ⟨FiniteLaw.selectedByBits omega,
    not_not.mp (not_or.mp homega).1, ?_⟩
  intro j hj
  exact fun hdisjoint ↦ (not_or.mp homega).2 ⟨j, hj, hdisjoint⟩

/-- Two-sided robust Hall sampling while enforcing one additional predicate
of the sampled relation. -/
theorem exists_bijective_twoSided_robust_matching_sample_with_good
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (Good : Finset (A × B) → Prop) (epsilon : ℝ≥0)
    (hbad : (FiniteLaw.independentBits
      (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)).probability
        (fun omega ↦ ¬ Good (FiniteLaw.selectedByBits omega)) ≤ epsilon)
    (hsmall : epsilon +
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hcard : Fintype.card A = Fintype.card B) :
    ∃ R : Finset (A × B), Good R ∧
      ∀ (deleted : A → B → Prop) [DecidableRel deleted],
        (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
        (∀ b, (deletedNeighbors (transposeRelation deleted) b).card ≤
          Delta) →
        ∃ f : A → B, Function.Bijective f ∧
          ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧
            ¬ deleted a (f a) := by
  classical
  choose groups hgroups using
    fun o : OrientedSmallHallObstruction A B ↦
      exists_pairwiseDisjoint_groups_of_mul_le_card
        (orientedSmallHallCandidates r o)
        (Delta * orientedSmallHallSize o + 1) groupSize (hcandidates o)
  let indices : Finset
      (Σ o : OrientedSmallHallObstruction A B,
        OrientedSmallHallGroupIndex Delta o) := univ
  obtain ⟨R, hRgood, hRmeets⟩ :=
    FiniteLaw.exists_selected_meets_all_and_good
      (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)
      indices (fun z ↦ groups z.1 z.2) Good epsilon hbad (by
        calc
          epsilon + ∑ z ∈ indices,
              ∏ _e ∈ groups z.1 z.2, (1 - sampleProbability) =
              epsilon + (Fintype.card
                (Σ o : OrientedSmallHallObstruction A B,
                  OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
                (1 - sampleProbability) ^ groupSize := by
            simp_rw [Finset.prod_const, (hgroups _).1 _ |>.1]
            simp [indices]
          _ < 1 := hsmall)
  refine ⟨R, hRgood, ?_⟩
  intro deleted _ hleftDegree hrightDegree
  have hmany := many_sampled_orientedSmallHallCandidates_of_groups
    r Delta groups (fun o j ↦ (hgroups o).1 j |>.2)
    (fun o ↦ (hgroups o).2) R
    (fun o j ↦ hRmeets ⟨o, j⟩ (by simp [indices]))
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
