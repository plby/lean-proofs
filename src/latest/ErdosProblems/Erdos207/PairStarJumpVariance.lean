/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStateConsequences
import ErdosProblems.Erdos207.PairExtensionTrajectory
import ErdosProblems.Erdos207.GreedyClosedThreatDrift

/-! # Pair-star jump and variance with the small expected-loss factor retained -/

namespace Erdos207

open Finset

noncomputable section

theorem pairStar_card_increment_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V) (T : TripleOn V) :
    ((availableTrianglesContainingPair (greedyStep F S T) P).card : ℝ) -
        (availableTrianglesContainingPair S P).card =
      greedyAvailableCountReal (availableTrianglesContainingPair S P) (greedyStep F S T) -
        greedyAvailableCountReal (availableTrianglesContainingPair S P) S := by
  unfold greedyAvailableCountReal
  rw [greedyAvailableIn_initialPairStar_eq_current (greedyStep_available_subset F S T),
    greedyAvailableIn_initialPairStar_eq_current (S₀ := S) (S := S) Subset.rfl]

theorem restrictedGreedyKernel_expectationReal_pairCard_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V)
    (R : TripleSystemOn V) (hR : R.Nonempty) (φ : ℝ → ℝ) :
    (restrictedGreedyKernel F S R hR).expectationReal
      (fun S' ↦ φ (((availableTrianglesContainingPair S' P).card : ℝ) -
        (availableTrianglesContainingPair S P).card)) =
      (restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ φ (greedyAvailableCountReal (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal (availableTrianglesContainingPair S P) S)) := by
  simp only [restrictedGreedyKernel_expectationReal, pairStar_card_increment_eq_current]

theorem pairStar_card_increment_eq_neg_closed_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (P : Finset V) {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    ((availableTrianglesContainingPair (greedyStep F S T) P).card : ℝ) -
        (availableTrianglesContainingPair S P).card =
      -((availableTrianglesContainingPair S P ∩ greedyClosedThreats F S T).card : ℝ) := by
  rw [pairStar_card_increment_eq_current, greedyAvailableCountReal_step_sub,
    greedyDeletedIn_eq_inter_closedThreats hS hT]

theorem CrudeStateBounds.pair_increment_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}
    (h : CrudeStateBounds F S q K) (P : PairOn V)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    {T : TripleOn V} (hT : T ∈ S.available \ availableTrianglesContainingPair S P.1) :
    -(3 + (K.pair : ℝ)) ≤
      ((availableTrianglesContainingPair (greedyStep F S T) P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card ∧
      ((availableTrianglesContainingPair (greedyStep F S T) P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card ≤ 0 := by
  have hTa := (mem_sdiff.mp hT).1
  have hPT : ¬ P.1 ⊆ T.1 := fun hsub ↦ (mem_sdiff.mp hT).2
    (mem_availableTrianglesContainingPair_iff.mpr ⟨hTa, hsub⟩)
  have hb := h.pair_inter P T hPT hpack
  have hbr : ((availableTrianglesContainingPair S P.1 ∩ greedyClosedThreats F S T).card : ℝ) ≤
      3 + (K.pair : ℝ) := by exact_mod_cast hb
  rw [pairStar_card_increment_eq_neg_closed_inter P.1 hS hTa]
  exact ⟨neg_le_neg hbr, neg_nonpos.mpr (Nat.cast_nonneg _)⟩

theorem restrictedGreedyKernel_secondMoment_le_negative_mean
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (R : TripleSystemOn V) (hR : R.Nonempty) (X : GreedyStateOn V → ℝ) (J : ℝ)
    (hinterval : ∀ T ∈ R, -J ≤ X (greedyStep F S T) ∧ X (greedyStep F S T) ≤ 0) :
    (restrictedGreedyKernel F S R hR).expectationReal (fun S' ↦ X S' ^ 2) ≤
      J * (-(restrictedGreedyKernel F S R hR).expectationReal X) := by
  simp only [restrictedGreedyKernel_expectationReal]
  calc
    _ ≤ (R.card : ℝ)⁻¹ * ∑ T ∈ R, J * (-X (greedyStep F S T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro T hT
      have hi := hinterval T hT
      have hm := mul_nonneg (neg_nonneg.mpr hi.2) (show 0 ≤ J + X (greedyStep F S T) by linarith)
      nlinarith only [hm]
    _ = _ := by rw [← mul_sum, sum_neg_distrib]; ring

theorem restrictedGreedyKernel_pairStar_secondMoment_le_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}
    (h : CrudeStateBounds F S q K) (P : PairOn V)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hR : (S.available \ availableTrianglesContainingPair S P.1).Nonempty)
    (slope epsilon : ℝ)
    (hmean : |(restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P.1) hR).expectationReal
      (fun S' ↦ ((availableTrianglesContainingPair S' P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card) - slope| ≤ epsilon) :
    (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P.1) hR).expectationReal
      (fun S' ↦ (((availableTrianglesContainingPair S' P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card) ^ 2) ≤
      (3 + (K.pair : ℝ)) * (|slope| + epsilon) := by
  have hb := restrictedGreedyKernel_secondMoment_le_negative_mean F S _ hR
    (fun S' ↦ ((availableTrianglesContainingPair S' P.1).card : ℝ) -
      (availableTrianglesContainingPair S P.1).card) (3 + (K.pair : ℝ))
    (fun T hT ↦ h.pair_increment_interval P hS hpack hT)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hm := (abs_le.mp hmean).1
  have hs := neg_abs_le slope
  linarith

end

end Erdos207
