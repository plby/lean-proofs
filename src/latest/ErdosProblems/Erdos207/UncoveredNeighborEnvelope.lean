/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborClockDrift
import ErdosProblems.Erdos207.KSSSDyadicPairBounds
import ErdosProblems.Erdos207.KSSSPowerExponentChoice

/-! # A degree envelope which remains relatively small at the density cutoff -/

namespace Erdos207

open Finset

noncomputable section

def uncoveredNeighborErrorEnvelope (E M t : ℝ) (s B : ℕ) (time : ℝ) : ℝ :=
  ksssErrorEnvelope E (16 * M * t / t ^ s) (B + 2) time

theorem ksssPairTrajectory_lower_fixed_initial_ratio
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ)
    (hE : 0 < E) (hN : 0 < N) (ht : 0 < t) (hTime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hratio : N / 6 ≤ A / E) (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t) :
    N / (2 * t) * ksssEdgeDensity E time ^ 2 ≤ ksssPairTrajectory orders a E A time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have he := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E time t ha hab hTime (by linarith) hexp
  rw [ksssPairTrajectory_source orders a E A time hE.ne' hp.ne']
  calc
    _ = ksssEdgeDensity E time ^ 2 * (1 / t) * (3 * (N / 6)) := by ring
    _ ≤ ksssEdgeDensity E time ^ 2 * Real.exp (-ksssPoissonExponent orders a time) * (3 * (A / E)) := by gcongr
    _ = _ := by ring

theorem pair_error_le_neighbor_envelope
    (N M t p x : ℝ) (s B : ℕ) (hN : 0 < N) (hM : 0 ≤ M) (ht : 0 < t) (hp : 0 < p)
    (hx : N / (2 * t) * p ^ 2 ≤ x) :
    8 * M * (N / t ^ s / p ^ B) / x ≤ (16 * M * t / t ^ s) / p ^ (B + 2) := by
  have hlower : 0 < N / (2 * t) * p ^ 2 := by positivity
  calc
    _ ≤ 8 * M * (N / t ^ s / p ^ B) / (N / (2 * t) * p ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hlower hx
    _ = _ := by rw [pow_add]; field_simp; ring

theorem neighbor_pair_drift_error_le_envelope
    (Y M e r L x z : ℝ) (hY : 0 ≤ Y) (hYM : Y ≤ M) (he : 0 ≤ e)
    (hL : 0 < L) (hx : 0 < x) (hr : L * x / 4 ≤ r) (hz : 8 * M * e / x ≤ z) :
    2 * Y * e / r ≤ z / L := by
  have hlower : 0 < L * x / 4 := by positivity
  have hM : 0 ≤ M := hY.trans hYM
  calc
    _ ≤ 2 * M * e / r := div_le_div_of_nonneg_right (by gcongr) (hlower.trans_le hr).le
    _ ≤ 2 * M * e / (L * x / 4) := div_le_div_of_nonneg_left (by positivity) hlower hr
    _ = (8 * M * e / x) / L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hz hL.le

theorem uncoveredNeighborErrorEnvelope_growth_dominates
    (E M t time : ℝ) (s B : ℕ) (hE : 0 < E) (hM : 0 ≤ M) (ht : 0 < t)
    (hclock : 3 * (time + 1) < E) :
    4 * uncoveredNeighborErrorEnvelope E M t s B time / (E * ksssEdgeDensity E time) ≤
      uncoveredNeighborErrorEnvelope E M t s B (time + 1) - uncoveredNeighborErrorEnvelope E M t s B time := by
  have hg := ksssErrorEnvelope_unitStep_growth E (16 * M * t / t ^ s) time (B + 2) hE (by positivity) hclock
  have hp := ksssEdgeDensity_pos hE (show 3 * time < E by linarith)
  have hz : 0 ≤ uncoveredNeighborErrorEnvelope E M t s B time := by
    unfold uncoveredNeighborErrorEnvelope ksssErrorEnvelope
    positivity
  have hcoef : (4 : ℝ) ≤ 3 * ((B + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 4 ≤ 3 * (B + 2) by omega)
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hz) (mul_pos hE hp).le).trans hg

theorem uncoveredNeighborErrorEnvelope_relative_upper
    (E M t time : ℝ) (b B : ℕ) (hM : 0 ≤ M) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) :
    uncoveredNeighborErrorEnvelope E M t (ksssPowerErrorExponent b B) B time ≤
      (16 / t) * uncoveredNeighborTarget E M time := by
  let p := ksssEdgeDensity E time
  let s := ksssPowerErrorExponent b B
  have hp : 0 < p := (by positivity : 0 < 1 / t ^ b).trans_le hfloor
  have hinverse := inverse_density_power_le t p b (B + 3) ht hp hfloor
  have hratio : uncoveredNeighborErrorEnvelope E M t s B time / p ≤ 16 * M / t := by
    calc
      _ = (16 * M * t / t ^ s) * (1 / p ^ (B + 3)) := by
        unfold uncoveredNeighborErrorEnvelope ksssErrorEnvelope
        change (16 * M * t / t ^ s) / p ^ (B + 2) / p = _
        rw [show B + 3 = (B + 2) + 1 by omega, pow_succ]
        ring
      _ ≤ (16 * M * t / t ^ s) * t ^ (b * (B + 3)) :=
        mul_le_mul_of_nonneg_left hinverse (by positivity)
      _ = _ := by
        have hexp : s = b * (B + 3) + 2 := by dsimp only [s, ksssPowerErrorExponent]; ring
        rw [hexp, pow_add]
        field_simp
  have hm := (div_le_iff₀ hp).mp hratio
  change _ ≤ (16 / t) * (M * p)
  calc
    _ ≤ (16 * M / t) * p := hm
    _ = _ := by ring

end

end Erdos207
