/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# A finite Bonferroni bound

The clique-removal drift calculation needs the elementary lower union
bound obtained by subtracting all pairwise intersections.  We use ordered
pairs; this loses only a harmless factor two and avoids choosing an order
on the index type.
-/

namespace Erdos722.FiniteUnionBounds

open Finset

noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

private lemma card_filter_mul_pred_eq_ordered_pairs
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (s.filter p).card * ((s.filter p).card - 1) =
      ∑ i ∈ s, if p i then ((s.erase i).filter p).card else 0 := by
  let t := s.filter p
  calc
    t.card * (t.card - 1) = ∑ _i ∈ t, (t.card - 1) := by simp
    _ = ∑ i ∈ t, (t.erase i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_erase_of_mem hi]
    _ = ∑ i ∈ s, if p i then (t.erase i).card else 0 := by
      rw [← Finset.sum_filter]
    _ = ∑ i ∈ s, if p i then ((s.erase i).filter p).card else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpi : p i
      · have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hpi⟩
        have herase : t.erase i = (s.erase i).filter p := by
          ext j
          simp [t, and_left_comm, and_assoc]
        simp [hpi, herase]
      · simp [hpi]

private lemma sum_ordered_memberships_eq_intersections
    (s : Finset ι) (F : ι → Finset α) :
    ∑ x ∈ s.biUnion F,
        ((s.filter fun i ↦ x ∈ F i).card *
          ((s.filter fun i ↦ x ∈ F i).card - 1)) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, (F i ∩ F j).card := by
  calc
    ∑ x ∈ s.biUnion F,
        ((s.filter fun i ↦ x ∈ F i).card *
          ((s.filter fun i ↦ x ∈ F i).card - 1)) =
        ∑ x ∈ s.biUnion F,
          ∑ i ∈ s, (if x ∈ F i then
            ((s.erase i).filter fun j ↦ x ∈ F j).card else 0) := by
              apply Finset.sum_congr rfl
              intro x _hx
              exact card_filter_mul_pred_eq_ordered_pairs s
                (fun i ↦ x ∈ F i)
    _ = ∑ i ∈ s, ∑ x ∈ s.biUnion F,
          (if x ∈ F i then
            ((s.erase i).filter fun j ↦ x ∈ F j).card else 0) := by
              rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s.erase i, (F i ∩ F j).card := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ x ∈ s.biUnion F, (if x ∈ F i then
            ((s.erase i).filter fun j ↦ x ∈ F j).card else 0) =
            ∑ x ∈ s.biUnion F, ∑ j ∈ s.erase i,
              if x ∈ F i ∧ x ∈ F j then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hxi : x ∈ F i
                · simp only [hxi, if_true, true_and]
                  rw [Finset.card_filter]
                · simp [hxi]
        _ = ∑ j ∈ s.erase i, ∑ x ∈ s.biUnion F,
              if x ∈ F i ∧ x ∈ F j then 1 else 0 := by
                rw [Finset.sum_comm]
        _ = ∑ j ∈ s.erase i, (F i ∩ F j).card := by
          apply Finset.sum_congr rfl
          intro j hj
          have heq : ((s.biUnion F).filter fun x ↦
              x ∈ F i ∧ x ∈ F j) = F i ∩ F j := by
            ext x
            constructor
            · intro hx
              exact Finset.mem_inter.mpr (Finset.mem_filter.mp hx).2
            · intro hx
              have hm := Finset.mem_inter.mp hx
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_biUnion.mpr ⟨i, hi, hm.1⟩, hm⟩
          rw [← Finset.card_filter, heq]

/-- First Bonferroni inequality, with every unordered pair counted twice. -/
theorem sum_card_le_card_biUnion_add_ordered_intersections
    (s : Finset ι) (F : ι → Finset α) :
    (∑ i ∈ s, (F i).card) ≤ (s.biUnion F).card +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (F i ∩ F j).card := by
  have hdouble : (∑ i ∈ s, (F i).card) =
      ∑ x ∈ s.biUnion F, (s.filter fun i ↦ x ∈ F i).card := by
    rw [Finset.sum_card_eq_sum_biUnion_card]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ext i
    simp
  rw [hdouble]
  calc
    (∑ x ∈ s.biUnion F, (s.filter fun i ↦ x ∈ F i).card) ≤
        ∑ x ∈ s.biUnion F,
          (1 + (s.filter fun i ↦ x ∈ F i).card *
            ((s.filter fun i ↦ x ∈ F i).card - 1)) := by
              apply Finset.sum_le_sum
              intro x hx
              have hpos : 0 < (s.filter fun i ↦ x ∈ F i).card := by
                obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
                exact Finset.card_pos.mpr
                  ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
              let m := (s.filter fun i ↦ x ∈ F i).card
              by_cases hm : m = 1
              · simp [m, hm]
              · have hm2 : 2 ≤ m := by omega
                have hmul := Nat.mul_le_mul_left m
                  (show 1 ≤ m - 1 by omega)
                change m ≤ 1 + m * (m - 1)
                omega
    _ = (s.biUnion F).card +
        ∑ x ∈ s.biUnion F,
          ((s.filter fun i ↦ x ∈ F i).card *
            ((s.filter fun i ↦ x ∈ F i).card - 1)) := by
              simp [Finset.sum_add_distrib]
    _ = (s.biUnion F).card +
        ∑ i ∈ s, ∑ j ∈ s.erase i, (F i ∩ F j).card := by
              rw [sum_ordered_memberships_eq_intersections]

/-- Convenient numerical consequence when every ordered pairwise
intersection has cardinality at most `C`. -/
theorem sum_card_le_card_biUnion_add_sq_mul
    (s : Finset ι) (F : ι → Finset α) (C : ℕ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s.erase i, (F i ∩ F j).card ≤ C) :
    (∑ i ∈ s, (F i).card) ≤
      (s.biUnion F).card + s.card ^ 2 * C := by
  calc
    (∑ i ∈ s, (F i).card) ≤ (s.biUnion F).card +
        ∑ i ∈ s, ∑ j ∈ s.erase i, (F i ∩ F j).card :=
      sum_card_le_card_biUnion_add_ordered_intersections s F
    _ ≤ (s.biUnion F).card + ∑ i ∈ s, ∑ _j ∈ s.erase i, C := by
      gcongr with i hi j hj
      exact hpair i hi j hj
    _ ≤ (s.biUnion F).card + s.card ^ 2 * C := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      calc
        ∑ i ∈ s, (s.erase i).card * C ≤ ∑ _i ∈ s, s.card * C := by
          apply Finset.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_right C
            (Finset.card_erase_le (s := s) (a := i))
        _ = s.card ^ 2 * C := by simp [pow_two, Nat.mul_assoc]

end

end Erdos722.FiniteUnionBounds
