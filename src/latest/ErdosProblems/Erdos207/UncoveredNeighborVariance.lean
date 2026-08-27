/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborCenteredDrift
import ErdosProblems.Erdos207.KSSSErrorEnvelopeUpper

/-! # Clock-scale variance budgets for the auxiliary degree martingale -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyKernel_uncoveredNeighbor_secondMoment_le_clock
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (hA : S.available.Nonempty) (L x : ℝ) (hL : 0 < L) (hx : 0 < x)
    (hr : L * x / 4 ≤ (S.available.card : ℝ))
    (hpair : ∀ u ∈ uncoveredNeighbors Q U v S,
      ((availableTrianglesContainingPair S {v, u}).card : ℝ) ≤ 5 * x / 4) :
    (greedyKernel F S).expectationReal (fun S' ↦
      (((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card) ^ 2) ≤
      10 * (U.card : ℝ) / L := by
  have hsum : (∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) ≤
      (U.card : ℝ) * (5 * x / 4) := by
    calc
      _ ≤ ∑ _u ∈ uncoveredNeighbors Q U v S, 5 * x / 4 := sum_le_sum hpair
      _ = ((uncoveredNeighbors Q U v S).card : ℝ) * (5 * x / 4) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_le_card (filter_subset _ _ : uncoveredNeighbors Q U v S ⊆ U)) (by positivity)
  calc
    _ ≤ 2 * (∑ u ∈ uncoveredNeighbors Q U v S, ((availableTrianglesContainingPair S {v, u}).card : ℝ)) /
        S.available.card := greedyKernel_uncoveredNeighbor_secondMoment F Q U v S hA
    _ ≤ 2 * ((U.card : ℝ) * (5 * x / 4)) / (L * x / 4) := by gcongr
    _ = _ := by field_simp; ring

theorem uncoveredNeighbor_deterministic_increment_le_clock
    (E M t time : ℝ) (b B : ℕ) (hE : 0 < E) (hM : 0 ≤ M) (ht : 0 < t) (htime : 0 ≤ time)
    (hclock : 3 * time + 6 ≤ E) (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hcoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t) :
    |uncoveredNeighborTarget E M (time + 1) - uncoveredNeighborTarget E M time| +
      |uncoveredNeighborErrorEnvelope E M t (ksssPowerErrorExponent b B) B (time + 1) -
        uncoveredNeighborErrorEnvelope E M t (ksssPowerErrorExponent b B) B time| ≤
      19 * M / (E * ksssEdgeDensity E time) := by
  let p := ksssEdgeDensity E time
  let L := E * p
  let s := ksssPowerErrorExponent b B
  let z := uncoveredNeighborErrorEnvelope E M t s B time
  have hp : 0 < p := ksssEdgeDensity_pos hE (by linarith)
  have hp1 : p ≤ 1 := ksssEdgeDensity_le_one hE htime
  have hL : 0 < L := mul_pos hE hp
  have hLE : L ≤ E := by dsimp only [L]; simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hE.le
  have hz : 0 ≤ z := by dsimp only [z, uncoveredNeighborErrorEnvelope, ksssErrorEnvelope]; positivity
  have hrelative : z ≤ (16 / t) * (M * p) := uncoveredNeighborErrorEnvelope_relative_upper E M t time b B hM ht hfloor
  have he := ksssErrorEnvelope_unitStep_abs_upper E (16 * M * t / t ^ s) time (B + 2) hE (by positivity) hclock
  have he' : |uncoveredNeighborErrorEnvelope E M t s B (time + 1) - z| ≤ 16 * M / L := by
    calc
      _ ≤ (6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2)) * z / L := he
      _ ≤ t * ((16 / t) * (M * p)) / L := by gcongr
      _ = 16 * M * p / L := by field_simp
      _ ≤ 16 * M / L := by
        apply div_le_div_of_nonneg_right _ hL.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 16 * M)
  have hf : |uncoveredNeighborTarget E M (time + 1) - uncoveredNeighborTarget E M time| ≤ 3 * M / L := by
    rw [uncoveredNeighborTarget_step, abs_div, abs_mul, abs_of_pos hE, abs_of_nonneg hM]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact div_le_div_of_nonneg_left (by positivity) hL hLE
  calc
    _ ≤ 3 * M / L + 16 * M / L := add_le_add hf he'
    _ = _ := by dsimp only [L]; ring

theorem neighbor_centered_secondMoment_clock_budget
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω) (X : Ω → ℝ)
    (M L sigma df de : ℝ) (hM : 0 ≤ M) (hL : 0 < L) (hsigma : |sigma| = 1)
    (hraw : law.expectationReal (fun ω ↦ X ω ^ 2) ≤ 10 * M / L)
    (hdet : |df| + |de| ≤ 19 * M / L) (hsmall : 19 * M / L ≤ 1) :
    law.expectationReal (fun ω ↦ (sigma * (X ω - df) - de) ^ 2) ≤ 64 * M / L := by
  have hnonneg : 0 ≤ 19 * M / L := by positivity
  have hsq : (|df| + |de|) ^ 2 ≤ 19 * M / L := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |df| + |de|) hdet 2
    have hprod := mul_nonneg hnonneg (show 0 ≤ 1 - 19 * M / L by linarith only [hsmall])
    nlinarith only [hpow, hprod]
  have hcenter := centered_step_secondMoment_le law X sigma df de (10 * M / L) hsigma hraw
  calc
    _ ≤ 2 * (10 * M / L) + 2 * (|df| + |de|) ^ 2 := hcenter
    _ ≤ 2 * (10 * M / L) + 2 * (19 * M / L) := by gcongr
    _ = 58 * M / L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hM]) hL.le

end

end Erdos207
