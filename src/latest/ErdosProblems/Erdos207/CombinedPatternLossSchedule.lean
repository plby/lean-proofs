/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GlobalPatternJump
import ErdosProblems.Erdos207.LocalizedTwoAwayStateBounds
import ErdosProblems.Erdos207.DyadicStoppedCrudeTail

/-! # One size-proportional jump schedule for the outer and all inner levels -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem combined_pattern_loss_relative_schedule
    {I V : Type*} [DecidableEq I] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k : ℕ}
    (hS : GreedyInvariant F S) (hpack : ∀ C ∈ F, IsPackingOn C)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (sets : I → Finset V) (i₀ : I) (houter : sets i₀ = univ) (r : ℕ)
    (hlocal : AllLocalizedTwoAwayBounds F (fun j : {i : I // i ≠ i₀} ↦ sets j.1)
      (fun j ↦ ((sets j.1).card : ℝ≥0) / (t : ℝ≥0) ^ (r + 2)) S)
    (ht : 1 ≤ t) (hsize : ∀ i, (t : ℝ) ^ (r + 2) ≤ ((sets i).card : ℝ))
    (hambient : (t : ℝ) ^ (r + k + 1) ≤ (Fintype.card V : ℝ))
    (Q : SimpleGraph V) (hcoeff : 3 + ((graphEdges Q).card : ℝ) ≤ t)
    (i : I) (T : TripleOn V) (hT : T ∈ patternSurvivalSelectors Q S) :
    ((patternExtensionLoss F Q (sets i) S T).card : ℝ) ≤ (sets i).card / (t : ℝ) ^ r := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  by_cases hi : i = i₀
  · subst i
    rw [houter, card_univ]
    have hbound : ((patternExtensionLoss F Q univ S T).card : ℝ) ≤
        3 + (graphEdges Q).card * (t : ℝ) ^ k := by
      have hraw := hcrude.pattern_loss_bound hS hpack Q univ T hT
      change ((patternExtensionLoss F Q univ S T).card : ℝ≥0) ≤
        3 + (graphEdges Q).card * (t : ℝ≥0) ^ k at hraw
      exact_mod_cast hraw
    exact hbound.trans (global_pattern_loss_relative_scale (Fintype.card V) t (graphEdges Q).card r k htR
      (Nat.cast_nonneg _) hcoeff hambient)
  · let j : {i : I // i ≠ i₀} := ⟨i, hi⟩
    have hbound : ((patternExtensionLoss F Q (sets i) S T).card : ℝ) ≤
        3 + (graphEdges Q).card * ((sets i).card / (t : ℝ) ^ (r + 2)) := by
      have hraw := hlocal.pattern_loss_bound hS j Q T hT
      change ((patternExtensionLoss F Q (sets i) S T).card : ℝ≥0) ≤
        3 + (graphEdges Q).card * (((sets i).card : ℝ≥0) / (t : ℝ≥0) ^ (r + 2)) at hraw
      exact_mod_cast hraw
    have hpower : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ htR (show 1 ≤ 2 by omega)
    exact hbound.trans (localized_pattern_loss_relative_scale (sets i).card t (graphEdges Q).card r htpos
      (hsize i) (Nat.cast_nonneg _) (hcoeff.trans hpower))

theorem relative_cutoff_concentration_size
    (M t : ℝ) (r a : ℕ) (ht : 1 ≤ t) (hM : 0 ≤ M) (hsize : t ^ r ≤ M) (ha : a ≤ r) :
    1 ≤ M / t ^ r ∧ (M / t ^ r) * t ^ a ≤ M := by
  have htpos : 0 < t := by linarith
  constructor
  · exact (le_div_iff₀ (pow_pos htpos r)).mpr (by simpa only [one_mul] using hsize)
  · calc
      _ ≤ (M / t ^ r) * t ^ r := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht ha) (by positivity)
      _ = _ := by field_simp

end

end Erdos207
