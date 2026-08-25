/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability
import ErdosProblems.Erdos207.RobustMatching

/-!
# Finite probabilistic construction of robust Hall matchings

This file joins the exact product-Bernoulli law to the deterministic robust
Hall criterion.  For every prospective Hall obstruction we are given enough
pairwise disjoint groups of candidate relation-pairs.  If the independently
sampled relation meets every group, then more than `Δ * |S|` sampled pairs
leave every obstruction `T` with `|T| < |S|`.  Hence no subsequent deletion
of maximum left degree `Δ` can destroy all perfect matchings.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- A prospective Hall obstruction, including the strict cardinality
inequality which makes it an obstruction. -/
abbrev HallObstruction (A B : Type*) [DecidableEq A] [DecidableEq B] :=
  {o : Finset A × Finset B // o.2.card < o.1.card}

/-- The number of disjoint witness groups demanded for an obstruction. -/
abbrev HallGroupIndex {A B : Type*} [DecidableEq A] [DecidableEq B]
    (Δ : ℕ) (o : HallObstruction A B) :=
  Fin (Δ * o.1.1.card + 1)

/-- A finite set of size at least `m * k` contains `m` pairwise disjoint
`k`-element subsets. -/
theorem exists_pairwiseDisjoint_groups_of_mul_le_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset X) (m k : ℕ) (hsize : m * k ≤ s.card) :
    ∃ groups : Fin m → Finset X,
      (∀ i, (groups i).card = k ∧ groups i ⊆ s) ∧
      ∀ i j, i ≠ j → Disjoint (groups i) (groups j) := by
  classical
  obtain ⟨u, hus, hucard⟩ := Finset.exists_subset_card_eq hsize
  have hcard : Fintype.card u = Fintype.card (Fin m × Fin k) := by
    simp [hucard]
  let e : u ≃ (Fin m × Fin k) := Fintype.equivOfCardEq hcard
  let groups : Fin m → Finset X := fun i ↦
    Finset.univ.image fun j : Fin k ↦ (e.symm (i, j)).1
  refine ⟨groups, ?_, ?_⟩
  · intro i
    constructor
    · rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        have hsub : e.symm (i, a) = e.symm (i, b) := Subtype.ext hab
        have hpair := e.symm.injective hsub
        exact congrArg Prod.snd hpair
    · intro x hx
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
      exact hus (e.symm (i, j)).2
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, _ha, hxa⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, _hb, hxb⟩ := Finset.mem_image.mp hxj
    have hsub : e.symm (i, a) = e.symm (j, b) :=
      Subtype.ext (hxa.trans hxb.symm)
    have hpair := e.symm.injective hsub
    exact hij (congrArg Prod.fst hpair)

/-- Hitting every group of a disjoint group certificate gives strictly more
than `Δ * |S|` sampled pairs leaving each Hall obstruction. -/
theorem many_sampled_pairs_of_group_certificate
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (Δ : ℕ)
    (groups : (o : HallObstruction A B) →
      HallGroupIndex Δ o → Finset (A × B))
    (hgroups : ∀ o i,
      groups o i ⊆ relationPairsLeaving r o.1.1 o.1.2)
    (hdisjoint : ∀ o i j, i ≠ j → Disjoint (groups o i) (groups o j))
    (R : Finset (A × B))
    (hmeets : ∀ o i, ¬ Disjoint (groups o i) R) :
    ∀ S : Finset A, ∀ T : Finset B, T.card < S.card →
      Δ * S.card <
        (relationPairsLeaving (fun a b ↦ r a b ∧ (a, b) ∈ R) S T).card := by
  classical
  intro S T hTS
  let o : HallObstruction A B := ⟨(S, T), hTS⟩
  let witness : HallGroupIndex Δ o → A × B := fun i ↦
    Classical.choose (Finset.not_disjoint_iff.mp (hmeets o i))
  have hwitness_group : ∀ i, witness i ∈ groups o i := by
    intro i
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets o i))).1
  have hwitness_R : ∀ i, witness i ∈ R := by
    intro i
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets o i))).2
  have hinjective : Function.Injective witness := by
    intro i j hij
    by_contra hne
    have hd := hdisjoint o i j hne
    exact (Finset.disjoint_left.mp hd (hwitness_group i))
      (hij ▸ hwitness_group j)
  have himage : Finset.univ.image witness ⊆
      relationPairsLeaving (fun a b ↦ r a b ∧ (a, b) ∈ R) S T := by
    intro e he
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
    have hcand := hgroups o i (hwitness_group i)
    rw [mem_relationPairsLeaving_iff] at hcand ⊢
    exact ⟨hcand.1, hcand.2.1, hcand.2.2, hwitness_R i⟩
  have hcard : Δ * S.card + 1 ≤
      (relationPairsLeaving (fun a b ↦ r a b ∧ (a, b) ∈ R) S T).card := by
    calc
      Δ * S.card + 1 = (Finset.univ.image witness).card := by
        rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ,
          Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card himage
  omega

/-- Exact finite probabilistic robust-matching lemma.  The numerical
hypothesis is precisely the union bound for missing one of the prescribed
candidate groups under independent, non-identically distributed sampling. -/
theorem exists_injective_robust_matching_sample
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (Δ : ℕ)
    (groups : (o : HallObstruction A B) →
      HallGroupIndex Δ o → Finset (A × B))
    (hgroups : ∀ o i,
      groups o i ⊆ relationPairsLeaving r o.1.1 o.1.2)
    (hdisjoint : ∀ o i j, i ≠ j → Disjoint (groups o i) (groups o j))
    (p : (A × B) → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (hsmall :
      ∑ z : Σ o : HallObstruction A B, HallGroupIndex Δ o,
          ∏ e ∈ groups z.1 z.2, (1 - p e) < 1) :
    ∃ R : Finset (A × B),
      ∀ (deleted : A → B → Prop) [DecidableRel deleted],
        (∀ a, (deletedNeighbors deleted a).card ≤ Δ) →
        ∃ f : A → B, Function.Injective f ∧
          ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a) := by
  classical
  let allGroups : Finset
      (Σ o : HallObstruction A B, HallGroupIndex Δ o) := Finset.univ
  obtain ⟨R, hR⟩ :=
    FiniteLaw.exists_selected_meets_all_of_sum_avoidance_lt_one
      p hp allGroups (fun z ↦ groups z.1 z.2) (by
        simpa [allGroups] using hsmall)
  refine ⟨R, ?_⟩
  intro deleted _ hdeleted
  have hmany := many_sampled_pairs_of_group_certificate r Δ groups hgroups
    hdisjoint R (fun o i ↦ hR ⟨o, i⟩ (by simp [allGroups]))
  have hrobust := survivesEveryHallObstruction_of_many_pairs
    (fun a b ↦ r a b ∧ (a, b) ∈ R) deleted Δ hdeleted hmany
  obtain ⟨f, hf, hrel⟩ :=
    exists_injective_matching_after_deletion
      (fun a b ↦ r a b ∧ (a, b) ∈ R) deleted hrobust
  exact ⟨f, hf, fun a ↦ ⟨(hrel a).1.1, (hrel a).1.2, (hrel a).2⟩⟩

/-- A cardinality lower bound on every Hall obstruction manufactures the
disjoint group certificate required by the preceding sampling theorem. -/
theorem exists_injective_robust_matching_sample_of_candidate_bound
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (Δ k : ℕ)
    (hcandidates : ∀ o : HallObstruction A B,
      (Δ * o.1.1.card + 1) * k ≤
        (relationPairsLeaving r o.1.1 o.1.2).card)
    (p : ℝ≥0) (hp : p ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : HallObstruction A B, HallGroupIndex Δ o) : ℝ≥0) *
          (1 - p) ^ k < 1) :
    ∃ R : Finset (A × B),
      ∀ (deleted : A → B → Prop) [DecidableRel deleted],
        (∀ a, (deletedNeighbors deleted a).card ≤ Δ) →
        ∃ f : A → B, Function.Injective f ∧
          ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a) := by
  classical
  choose groups hgroups using fun o : HallObstruction A B ↦
    exists_pairwiseDisjoint_groups_of_mul_le_card
      (relationPairsLeaving r o.1.1 o.1.2)
      (Δ * o.1.1.card + 1) k (hcandidates o)
  apply exists_injective_robust_matching_sample r Δ groups
    (fun o i ↦ (hgroups o).1 i |>.2) (fun o ↦ (hgroups o).2)
    (fun _ ↦ p) (fun _ ↦ hp)
  calc
    ∑ z : Σ o : HallObstruction A B, HallGroupIndex Δ o,
        ∏ _e ∈ groups z.1 z.2, (1 - p) =
        (Fintype.card
          (Σ o : HallObstruction A B, HallGroupIndex Δ o) : ℝ≥0) *
            (1 - p) ^ k := by
      simp_rw [Finset.prod_const, (hgroups _).1 _ |>.1]
      simp
    _ < 1 := hsmall

end Erdos207
