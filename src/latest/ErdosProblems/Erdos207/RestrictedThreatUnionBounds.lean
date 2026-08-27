/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpGreedyCoveringChoiceCount

/-! # Bonferroni bounds after excluding the root's threat set -/

namespace Erdos207

open Finset
open scoped BigOperators

theorem sum_card_le_card_restricted_biUnion_add
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I → Finset A) (R : Finset A) (K : ℕ)
    (hroot : ∀ i ∈ s, (F i ∩ R).card ≤ K)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (F i ∩ F j).card ≤ K) :
    ∑ i ∈ s, (F i).card ≤
      (s.biUnion (fun i ↦ F i \ R)).card + (s.card + s.card.choose 2) * K := by
  have hbonf := sum_card_le_card_biUnion_add_choose_two_mul s
    (fun i ↦ F i \ R) K (by
      intro i hi j hj hij
      exact (card_le_card (inter_subset_inter sdiff_subset sdiff_subset)).trans
        (hinter i hi j hj hij))
  have hsingle : ∀ i ∈ s, (F i).card ≤ (F i \ R).card + K := by
    intro i hi
    have hpartition := card_sdiff_add_card_inter (F i) R
    have hiK := hroot i hi
    omega
  have hsum := sum_le_sum hsingle
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  calc
    ∑ i ∈ s, (F i).card ≤ (∑ i ∈ s, (F i \ R).card) + s.card * K := hsum
    _ ≤ (s.biUnion (fun i ↦ F i \ R)).card + s.card.choose 2 * K + s.card * K :=
      Nat.add_le_add_right hbonf _
    _ = _ := by ring

theorem card_restricted_biUnion_le_sum_card
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I → Finset A) (R : Finset A) :
    (s.biUnion (fun i ↦ F i \ R)).card ≤ ∑ i ∈ s, (F i).card := by
  exact card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_le_card sdiff_subset)

end Erdos207
