/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RestrictedThreatUnionBounds

/-! # Real-valued trajectory error for a root-restricted threat union -/

namespace Erdos207

open Finset
open scoped BigOperators

theorem abs_card_restricted_biUnion_sub
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (F : I → Finset A) (R : Finset A) (K : ℕ)
    (H epsilon : ℝ)
    (hroot : ∀ i ∈ s, (F i ∩ R).card ≤ K)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (F i ∩ F j).card ≤ K)
    (htrajectory : ∀ i ∈ s, |((F i).card : ℝ) - H| ≤ epsilon) :
    |((s.biUnion (fun i ↦ F i \ R)).card : ℝ) - s.card * H| ≤
      s.card * epsilon + ((s.card + s.card.choose 2) * K : ℕ) := by
  have hupper : ((s.biUnion (fun i ↦ F i \ R)).card : ℝ) ≤
      ∑ i ∈ s, ((F i).card : ℝ) := by
    exact_mod_cast card_restricted_biUnion_le_sum_card s F R
  have hlower : (∑ i ∈ s, ((F i).card : ℝ)) ≤
      (s.biUnion (fun i ↦ F i \ R)).card + ((s.card + s.card.choose 2) * K : ℕ) := by
    exact_mod_cast sum_card_le_card_restricted_biUnion_add s F R K hroot hinter
  have hsumUpper : (∑ i ∈ s, ((F i).card : ℝ)) ≤ s.card * (H + epsilon) := by
    calc
      _ ≤ ∑ _i ∈ s, (H + epsilon) := sum_le_sum fun i hi ↦ by
        have h := (abs_le.mp (htrajectory i hi)).2
        linarith
      _ = _ := by simp [mul_add]
  have hsumLower : s.card * (H - epsilon) ≤ ∑ i ∈ s, ((F i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (H - epsilon) := by simp [mul_sub]
      _ ≤ _ := sum_le_sum fun i hi ↦ by
        have h := (abs_le.mp (htrajectory i hi)).1
        linarith
  have hcorrection : (0 : ℝ) ≤ ((s.card + s.card.choose 2) * K : ℕ) := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith only [hupper, hlower, hsumUpper, hsumLower, hcorrection]

end Erdos207
