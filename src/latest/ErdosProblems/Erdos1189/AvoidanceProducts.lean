/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Product bounds for the coordinate version of the local lemma.
Informal argument: the finite union bound for product factors, with repeated
factors making a product of numbers in [0,1] smaller.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.LocalLemma

namespace Erdos1189

open Finset

variable {α ι : Type*}

lemma one_sub_sum_le_product (S : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a ∧ w a ≤ 1) :
    1 - ∑ a ∈ S, w a ≤ ∏ a ∈ S, (1 - w a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hwa := hw a (mem_insert_self _ _)
    have hwS : ∀ b ∈ S, 0 ≤ w b ∧ w b ≤ 1 := fun b hb => hw b (mem_insert_of_mem hb)
    have hmul := mul_le_mul_of_nonneg_left (ih hwS) (sub_nonneg.mpr hwa.2)
    have hsum : 0 ≤ ∑ b ∈ S, w b := sum_nonneg fun b hb => (hwS b hb).1
    rw [sum_insert ha, prod_insert ha]
    nlinarith [mul_nonneg hwa.1 hsum]

lemma product_union_ge [DecidableEq α] (S T : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ S ∪ T, 0 ≤ f a ∧ f a ≤ 1) :
    (∏ a ∈ S, f a) * (∏ a ∈ T, f a) ≤ ∏ a ∈ S ∪ T, f a := by
  rw [← prod_union_inter]
  have hinter := prod_le_one (s := S ∩ T)
    (fun a ha => (hf a (mem_union_left _ (mem_inter.mp ha).1)).1)
    (fun a ha => (hf a (mem_union_left _ (mem_inter.mp ha).1)).2)
  exact mul_le_of_le_one_right (prod_nonneg fun a ha => (hf a ha).1) hinter

lemma product_biUnion_ge [DecidableEq α] (I : Finset ι) (B : ι → Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ I, ∀ a ∈ B i, 0 ≤ f a ∧ f a ≤ 1) :
    (∏ i ∈ I, ∏ a ∈ B i, f a) ≤ ∏ a ∈ I.biUnion B, f a := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hfi := hf i (mem_insert_self _ _)
    have hfI : ∀ j ∈ I, ∀ a ∈ B j, 0 ≤ f a ∧ f a ≤ 1 :=
      fun j hj => hf j (mem_insert_of_mem hj)
    have hmul := mul_le_mul_of_nonneg_left (ih hfI) (prod_nonneg fun a ha => (hfi a ha).1)
    rw [prod_insert hi, biUnion_insert]
    apply hmul.trans
    apply product_union_ge
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact hfi a ha
    · obtain ⟨j, hj, ha⟩ := mem_biUnion.mp ha
      exact hfI j hj a ha

end Erdos1189
