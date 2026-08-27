/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-!
# Sharp union bound for prescribed pair stars

The coarse preliminary estimate divided the sum of pair-star sizes by three.
For a fixed finite prescription this loses the decisive power of the leave
density.  Two distinct graph-edge stars intersect in at most one triangle,
so Bonferroni's first two terms instead give

`|union of stars| + choose(|B|,2) >= sum of star sizes`.

Thus a uniform star floor `d` yields the sharp loss
`|B| d - choose(|B|,2)`.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

lemma Sym2.eq_of_toFinset_eq_of_not_isDiag
    {V : Type*} [DecidableEq V] {e f : Sym2 V}
    (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag) (h : e.toFinset = f.toFinset) :
    e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
          rw [Sym2.mk_isDiag_iff] at he hf
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at h
          rw [Sym2.eq_iff]
          have ha : a = c ∨ a = d := by
            have : a ∈ ({c, d} : Finset V) := by
              rw [← h]
              simp
            simpa using this
          have hb : b = c ∨ b = d := by
            have : b ∈ ({c, d} : Finset V) := by
              rw [← h]
              simp
            simpa using this
          rcases ha with hac | had <;> rcases hb with hbc | hbd
          · exact (he (hac.trans hbc.symm)).elim
          · exact Or.inl ⟨hac, hbd⟩
          · exact Or.inr ⟨had, hbc⟩
          · exact (he (had.trans hbd.symm)).elim

/-- Two distinct off-diagonal pair stars contain at most one common
available triangle. -/
lemma card_inter_greedyChoicesCoveringEdge_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) {e f : Sym2 V}
    (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag) (hef : e ≠ f) :
    (greedyChoicesCoveringEdge S e ∩
      greedyChoicesCoveringEdge S f).card <= 1 := by
  classical
  by_cases hnonempty :
      (greedyChoicesCoveringEdge S e ∩
        greedyChoicesCoveringEdge S f).Nonempty
  · obtain ⟨T, hT⟩ := hnonempty
    apply (card_le_card ?_).trans (show ({T} : Finset S.available).card <= 1 by simp)
    intro U hU
    have hTe := (mem_filter.mp (mem_inter.mp hT).1).2
    have hTf := (mem_filter.mp (mem_inter.mp hT).2).2
    have hUe := (mem_filter.mp (mem_inter.mp hU).1).2
    have hUf := (mem_filter.mp (mem_inter.mp hU).2).2
    have heSubT :=
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T.1 he).mp hTe
    have hfSubT :=
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag f T.1 hf).mp hTf
    have heSubU :=
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e U.1 he).mp hUe
    have hfSubU :=
      (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag f U.1 hf).mp hUf
    have hpairNe : e.toFinset ≠ f.toFinset := by
      intro heq
      exact hef (Sym2.eq_of_toFinset_eq_of_not_isDiag he hf heq)
    have hcardUnion : (e.toFinset ∪ f.toFinset).card = 3 := by
      have heCard := Sym2.card_toFinset_of_not_isDiag e he
      have hfCard := Sym2.card_toFinset_of_not_isDiag f hf
      have hinter : (e.toFinset ∩ f.toFinset).card < 2 := by
        have hinterLe : (e.toFinset ∩ f.toFinset).card <= 2 := by
          exact (card_le_card inter_subset_left).trans_eq heCard
        by_contra hnot
        have hinterEq : (e.toFinset ∩ f.toFinset).card = 2 := by omega
        have hsub : e.toFinset ⊆ f.toFinset := by
          have hinterLeft : e.toFinset ∩ f.toFinset = e.toFinset := by
            apply eq_of_subset_of_card_le inter_subset_left
            rw [hinterEq, heCard]
          rw [← hinterLeft]
          exact inter_subset_right
        have heq : e.toFinset = f.toFinset :=
          eq_of_subset_of_card_le hsub (by rw [heCard, hfCard])
        exact hpairNe heq
      have hunion := card_union_add_card_inter e.toFinset f.toFinset
      have hunionLe : (e.toFinset ∪ f.toFinset).card <= 3 := by
        have hle := card_le_card (union_subset heSubT hfSubT)
        simpa only [T.1.2] using hle
      rw [heCard, hfCard] at hunion
      omega
    have hUnionT : e.toFinset ∪ f.toFinset = T.1 := by
      apply eq_of_subset_of_card_le
      · exact union_subset heSubT hfSubT
      · rw [hcardUnion, T.1.2]
    have hUnionU : e.toFinset ∪ f.toFinset = U.1 := by
      apply eq_of_subset_of_card_le
      · exact union_subset heSubU hfSubU
      · rw [hcardUnion, U.1.2]
    have hUT : U = T := by
      apply Subtype.ext
      apply Subtype.ext
      exact hUnionU.symm.trans hUnionT
    simpa [hUT]
  · rw [not_nonempty_iff_eq_empty.mp hnonempty]
    simp

/-- First two Bonferroni terms for a finite family whose pairwise
intersections have cardinality at most `c`. -/
lemma sum_card_le_card_biUnion_add_choose_two_mul
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I -> Finset A) (c : ℕ)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      (F i ∩ F j).card <= c) :
    ∑ i ∈ s, (F i).card <=
      (s.biUnion F).card + s.card.choose 2 * c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ih' := ih (by
        intro i hi j hj hij
        exact hinter i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
      have hinterUnion : (F a ∩ s.biUnion F).card <= s.card * c := by
        calc
          (F a ∩ s.biUnion F).card =
              (s.biUnion fun j => F a ∩ F j).card := by
            apply congrArg Finset.card
            ext x
            simp only [mem_inter, mem_biUnion]
            aesop
          _ <= ∑ j ∈ s, (F a ∩ F j).card := card_biUnion_le
          _ <= ∑ _j ∈ s, c := by
            apply sum_le_sum
            intro j hj
            exact hinter a (mem_insert_self a s) j (mem_insert_of_mem hj)
              (Ne.symm fun hja => ha (hja ▸ hj))
          _ = s.card * c := by simp
      have hunionCard := card_union_add_card_inter (F a) (s.biUnion F)
      rw [sum_insert ha, biUnion_insert, card_insert_of_notMem ha,
        Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_mul]
      calc
        (F a).card + ∑ x ∈ s, (F x).card <=
            (F a).card + ((s.biUnion F).card + s.card.choose 2 * c) := by
          omega
        _ = (F a ∪ s.biUnion F).card +
              (F a ∩ s.biUnion F).card + s.card.choose 2 * c := by
          omega
        _ <= (F a ∪ s.biUnion F).card +
              s.card * c + s.card.choose 2 * c := by
          omega
        _ = (F a ∪ s.biUnion F).card +
              (s.card * c + s.card.choose 2 * c) := by omega

/-- The prescribed pair-star incidence sum exceeds the union by at most one
for every unordered pair of prescribed edges. -/
theorem sum_card_greedyChoicesCoveringEdge_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hoffdiag : ∀ e ∈ B, ¬ e.IsDiag) :
    ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card <=
      (greedyCoveringChoices S B).card + B.card.choose 2 := by
  have hbonf := sum_card_le_card_biUnion_add_choose_two_mul B
    (greedyChoicesCoveringEdge S) 1 (by
      intro e he f hf hef
      exact card_inter_greedyChoicesCoveringEdge_le_one S
        (hoffdiag e he) (hoffdiag f hf) hef)
  have hunion : B.biUnion (greedyChoicesCoveringEdge S) =
      greedyCoveringChoices S B := by
    ext T
    simp [greedyChoicesCoveringEdge, greedyCoveringChoices,
      Finset.not_disjoint_iff]
  simpa only [hunion, Nat.mul_one] using hbonf

/-- A uniform pair-star floor gives the sharp additive-overlap lower bound
for the number of choices hitting at least one prescribed edge. -/
theorem card_mul_le_greedyCoveringChoices_add_choose_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) (d : ℕ)
    (hoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ e ∈ B, d <= (greedyChoicesCoveringEdge S e).card) :
    B.card * d <= (greedyCoveringChoices S B).card + B.card.choose 2 := by
  calc
    B.card * d = ∑ _e ∈ B, d := by simp [mul_comm]
    _ <= ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card := by
      apply sum_le_sum
      intro e he
      exact hsupply e he
    _ <= (greedyCoveringChoices S B).card + B.card.choose 2 :=
      sum_card_greedyChoicesCoveringEdge_le_sharp S B hoffdiag

end

end Erdos207
