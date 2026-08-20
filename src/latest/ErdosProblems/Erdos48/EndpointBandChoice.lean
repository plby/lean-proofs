/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointPageMean

/-!
# Choosing the endpoint zero bands

The number of equal Page-width bands is chosen by a natural floor.  These
elementary bounds verify both the middle-band width and a fixed power saving
for the far-zero remainder.
-/

namespace Erdos48

noncomputable section

/-- Number of equal Page-width bands retained before the far-zero tail. -/
noncomputable def endpointBandCount (eta : ℝ) : ℕ :=
  Nat.floor (1 / (16 * eta))

theorem endpointBandCount_cast_le {eta : ℝ} (heta : 0 < eta) :
    (endpointBandCount eta : ℝ) ≤ 1 / (16 * eta) := by
  exact Nat.floor_le (by positivity)

theorem endpointBandCount_inv_lt_succ {eta : ℝ} :
    1 / (16 * eta) < (endpointBandCount eta : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

theorem endpointBandCount_width
    {eta : ℝ} (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 16) :
    ∀ j ∈ Finset.range (endpointBandCount eta),
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8 := by
  intro j hj
  have hjNat : j + 2 ≤ endpointBandCount eta + 1 := by
    have := Finset.mem_range.mp hj
    omega
  have hjCast : ((j + 2 : ℕ) : ℝ) ≤
      (endpointBandCount eta : ℝ) + 1 := by exact_mod_cast hjNat
  have hfloor := endpointBandCount_cast_le heta
  have hmul : ((j + 2 : ℕ) : ℝ) * eta ≤
      (1 / (16 * eta) + 1) * eta := by
    apply mul_le_mul_of_nonneg_right _ heta.le
    linarith
  have hcancel : (1 / (16 * eta)) * eta = 1 / 16 := by
    field_simp
  rw [add_mul, hcancel, one_mul] at hmul
  linarith

theorem endpointBandCount_far_saving
    {eta : ℝ} (heta : 0 < eta) :
    1 / 16 ≤ (((endpointBandCount eta + 1 : ℕ) : ℝ) * eta) := by
  have hfloor := endpointBandCount_inv_lt_succ (eta := eta)
  have hmul := mul_lt_mul_of_pos_right hfloor heta
  have hcancel : (1 / (16 * eta)) * eta = 1 / 16 := by
    field_simp
  simpa only [Nat.cast_add, Nat.cast_one, hcancel] using hmul.le

theorem endpointBandCount_far_cutoff_half
    {eta : ℝ} (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 16) :
    1 / 2 ≤ 1 -
      (((endpointBandCount eta + 1 : ℕ) : ℝ) * eta) := by
  have hfloor := endpointBandCount_cast_le heta
  have hcancel : (1 / (16 * eta)) * eta = 1 / 16 := by
    field_simp
  have hmul : ((endpointBandCount eta : ℝ) + 1) * eta ≤
      1 / 16 + eta := by
    calc
      ((endpointBandCount eta : ℝ) + 1) * eta ≤
          (1 / (16 * eta) + 1) * eta := by
        apply mul_le_mul_of_nonneg_right _ heta.le
        linarith
      _ = 1 / 16 + eta := by rw [add_mul, hcancel, one_mul]
  push_cast
  linarith

end

end Erdos48
