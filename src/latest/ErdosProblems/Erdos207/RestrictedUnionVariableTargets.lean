/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RestrictedThreatUnionDeviation

/-! # Restricted finite unions with different targets and two overlap budgets -/

namespace Erdos207

open Finset

theorem sum_card_le_card_restricted_biUnion_add_separate
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I → Finset A) (R : Finset A) (Kr Ki : ℕ)
    (hroot : ∀ i ∈ s, (F i ∩ R).card ≤ Kr)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (F i ∩ F j).card ≤ Ki) :
    ∑ i ∈ s, (F i).card ≤
      (s.biUnion (fun i ↦ F i \ R)).card + s.card * Kr + s.card.choose 2 * Ki := by
  have hbonf := sum_card_le_card_biUnion_add_choose_two_mul s
    (fun i ↦ F i \ R) Ki (by
      intro i hi j hj hij
      exact (card_le_card (inter_subset_inter sdiff_subset sdiff_subset)).trans
        (hinter i hi j hj hij))
  have hsingle : ∀ i ∈ s, (F i).card ≤ (F i \ R).card + Kr := by
    intro i hi
    have hpartition := card_sdiff_add_card_inter (F i) R
    have hiK := hroot i hi
    omega
  have hsum := sum_le_sum hsingle
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  change (∑ i ∈ s, (F i).card) ≤ (∑ i ∈ s, (F i \ R).card) + s.card * Kr at hsum
  omega

theorem abs_card_restricted_biUnion_sub_sum_targets
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I → Finset A) (R : Finset A) (Kr Ki : ℕ)
    (target err : I → ℝ)
    (hroot : ∀ i ∈ s, (F i ∩ R).card ≤ Kr)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (F i ∩ F j).card ≤ Ki)
    (htrajectory : ∀ i ∈ s, |((F i).card : ℝ) - target i| ≤ err i) :
    |((s.biUnion (fun i ↦ F i \ R)).card : ℝ) - ∑ i ∈ s, target i| ≤
      (∑ i ∈ s, err i) + (s.card * Kr + s.card.choose 2 * Ki : ℕ) := by
  have hupper : ((s.biUnion (fun i ↦ F i \ R)).card : ℝ) ≤
      ∑ i ∈ s, ((F i).card : ℝ) := by
    exact_mod_cast card_restricted_biUnion_le_sum_card s F R
  have hlower : (∑ i ∈ s, ((F i).card : ℝ)) ≤
      (s.biUnion (fun i ↦ F i \ R)).card + (s.card * Kr + s.card.choose 2 * Ki : ℕ) := by
    have h := sum_card_le_card_restricted_biUnion_add_separate s F R Kr Ki hroot hinter
    exact_mod_cast (show ∑ i ∈ s, (F i).card ≤
      (s.biUnion (fun i ↦ F i \ R)).card + (s.card * Kr + s.card.choose 2 * Ki) by omega)
  have hdeficit : |((s.biUnion (fun i ↦ F i \ R)).card : ℝ) -
      ∑ i ∈ s, ((F i).card : ℝ)| ≤ (s.card * Kr + s.card.choose 2 * Ki : ℕ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith only [hlower]
  have hsum : |(∑ i ∈ s, ((F i).card : ℝ)) - ∑ i ∈ s, target i| ≤ ∑ i ∈ s, err i := by
    rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum htrajectory)
  calc
    _ ≤ |((s.biUnion (fun i ↦ F i \ R)).card : ℝ) - ∑ i ∈ s, ((F i).card : ℝ)| +
        |(∑ i ∈ s, ((F i).card : ℝ)) - ∑ i ∈ s, target i| := abs_sub_le _ _ _
    _ ≤ (s.card * Kr + s.card.choose 2 * Ki : ℕ) + ∑ i ∈ s, err i := add_le_add hdeficit hsum
    _ = _ := add_comm _ _

end Erdos207
