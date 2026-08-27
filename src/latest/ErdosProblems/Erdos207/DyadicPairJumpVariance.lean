/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPairPowerBounds

/-! # The actual pair jump and variance powers from its small expected loss -/

namespace Erdos207

open Finset

noncomputable section

theorem dyadic_pair_jump_coefficient (t k : ℕ) (ht : 16 ≤ t) :
    3 + (t : ℝ) ^ k ≤ (t : ℝ) ^ (k + 1) := by
  have h := power_crude_overlap_le (t : ℝ) k (by exact_mod_cast ht)
  have hp : (0 : ℝ) ≤ (t : ℝ) ^ k := by positivity
  linarith

theorem CrudeStateBounds.dyadic_pair_jump
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k)) (P : PairOn V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D) (ht : 16 ≤ t)
    {T : TripleOn V} (hT : T ∈ S.available \ availableTrianglesContainingPair S P.1) :
    |((availableTrianglesContainingPair (greedyStep F S T) P.1).card : ℝ) -
      (availableTrianglesContainingPair S P.1).card| ≤ (t : ℝ) ^ (k + 1) := by
  have hi := h.pair_increment_interval P hS hpack hT
  have hbound : |((availableTrianglesContainingPair (greedyStep F S T) P.1).card : ℝ) -
      (availableTrianglesContainingPair S P.1).card| ≤ 3 + (t : ℝ) ^ k :=
    abs_le.mpr ⟨hi.1, hi.2.trans (by positivity)⟩
  exact hbound.trans (dyadic_pair_jump_coefficient t k ht)

theorem CrudeStateBounds.dyadic_pair_variance
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k b : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k)) (P : PairOn V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D) (ht : 16 ≤ t)
    (hR : (S.available \ availableTrianglesContainingPair S P.1).Nonempty)
    (slope epsilon : ℝ)
    (hmean : |(restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P.1) hR).expectationReal
      (fun S' ↦ ((availableTrianglesContainingPair S' P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card) - slope| ≤ epsilon)
    (hloss : |slope| + epsilon ≤ 1 / (Fintype.card V : ℝ) * (t : ℝ) ^ (2 * b + 1)) :
    (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P.1) hR).expectationReal
      (fun S' ↦ (((availableTrianglesContainingPair S' P.1).card : ℝ) -
        (availableTrianglesContainingPair S P.1).card) ^ 2) ≤
      1 / (Fintype.card V : ℝ) * (t : ℝ) ^ (k + 2 * b + 2) := by
  have hepsilon : 0 ≤ epsilon := (abs_nonneg _).trans hmean
  have hraw := restrictedGreedyKernel_pairStar_secondMoment_le_drift_error h P hS hpack hR
    slope epsilon hmean
  change _ ≤ (3 + (t : ℝ) ^ k) * (|slope| + epsilon) at hraw
  calc
    _ ≤ (3 + (t : ℝ) ^ k) * (|slope| + epsilon) := hraw
    _ ≤ (t : ℝ) ^ (k + 1) * (1 / (Fintype.card V : ℝ) * (t : ℝ) ^ (2 * b + 1)) :=
      mul_le_mul (dyadic_pair_jump_coefficient t k ht) hloss (add_nonneg (abs_nonneg _) hepsilon)
        (by positivity)
    _ = _ := by
      have hexp : k + 2 * b + 2 = (k + 1) + (2 * b + 1) := by omega
      rw [hexp, pow_add]
      ring

end

end Erdos207
