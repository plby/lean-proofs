/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborDynamics

/-! # Jump, variance, and pair-trajectory drift errors for neighbor counts -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyKernel_uncoveredNeighbor_increment_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V) (S : GreedyStateOn V) :
    (greedyKernel F S).SupportedOn fun S' ↦
      -2 ≤ ((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card ∧
      ((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card ≤ 0 := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, _hT, rfl⟩
  · simp
  · rw [uncoveredNeighbors_step_increment]
    have htwo : ((uncoveredNeighborLoss Q U v S T).card : ℝ) ≤ 2 := by
      exact_mod_cast uncoveredNeighborLoss_card_le_two Q U v S T
    have hzero : (0 : ℝ) ≤ (uncoveredNeighborLoss Q U v S T).card := Nat.cast_nonneg _
    constructor <;> linarith only [htwo, hzero]

theorem greedyKernel_uncoveredNeighbor_secondMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal (fun S' ↦
      (((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card) ^ 2) ≤
      2 * (∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) /
        S.available.card := by
  let X := fun S' ↦ ((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card
  have hpoint := greedyKernel_uncoveredNeighbor_increment_interval F Q U v S
  calc
    _ ≤ (greedyKernel F S).expectationReal (fun S' ↦ -2 * X S') := by
      apply (greedyKernel F S).expectationReal_mono_of_supported hpoint
      intro S' hS'
      change -2 ≤ X S' ∧ X S' ≤ 0 at hS'
      have hprod := mul_nonneg (show 0 ≤ X S' + 2 by linarith only [hS'.1])
        (show 0 ≤ -X S' by linarith only [hS'.2])
      change X S' ^ 2 ≤ -2 * X S'
      nlinarith only [hprod]
    _ = -2 * (greedyKernel F S).expectationReal X := FiniteLaw.expectationReal_const_mul _ _ _
    _ = _ := by
      dsimp only [X]
      rw [greedyKernel_uncoveredNeighbor_drift F Q U v S hA]
      ring

theorem greedyKernel_uncoveredNeighbor_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) (x e : ℝ)
    (hpair : ∀ u ∈ uncoveredNeighbors Q U v S,
      |((availableTrianglesContainingPair S {v, u}).card : ℝ) - x| ≤ e) :
    |(greedyKernel F S).expectationReal (fun S' ↦
      ((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card) -
      (-((uncoveredNeighbors Q U v S).card : ℝ) * x / S.available.card)| ≤
      ((uncoveredNeighbors Q U v S).card : ℝ) * e / S.available.card := by
  have hsum := abs_sum_sub_card_mul_le_sum_error (uncoveredNeighbors Q U v S)
    (fun u ↦ ((availableTrianglesContainingPair S {v, u}).card : ℝ)) (fun _ ↦ e) x hpair
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hApos : (0 : ℝ) < S.available.card := by exact_mod_cast card_pos.mpr hA
  rw [greedyKernel_uncoveredNeighbor_drift F Q U v S hA]
  have hid : -(∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) /
      S.available.card - (-((uncoveredNeighbors Q U v S).card : ℝ) * x / S.available.card) =
      -((∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) -
        (uncoveredNeighbors Q U v S).card * x) / S.available.card := by ring
  rw [hid, abs_div, abs_neg, abs_of_pos hApos]
  exact div_le_div_of_nonneg_right hsum hApos.le

end

end Erdos207
