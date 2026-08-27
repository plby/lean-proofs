/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CubicSurvivalCancellation

/-! # A fractional affine envelope remains within twice the exact residual clock -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem affineSurvivalEnvelope_clock_comparison
    (E eps : ℝ≥0) (n i : ℕ) (hclock : 3 * (n : ℝ≥0) < E)
    (heps : eps ≤ 1) (hepsClock : eps * E ≤ E - 3 * (n : ℝ≥0)) (hi : i ≤ n) :
    E - 3 * (i : ℝ≥0) ≤ affineSurvivalEnvelope E (3 * (1 - eps)) i ∧
      affineSurvivalEnvelope E (3 * (1 - eps)) i ≤ 2 * (E - 3 * (i : ℝ≥0)) := by
  have hcurrent : 3 * (i : ℝ≥0) ≤ E :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hi : (i : ℝ≥0) ≤ n) zero_le).trans hclock.le
  have hslope : 3 * (1 - eps) ≤ (3 : ℝ≥0) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (tsub_le_self : 1 - eps ≤ (1 : ℝ≥0)) (by norm_num)
  have hchosen : (i : ℝ≥0) * (3 * (1 - eps)) ≤ E := by
    calc
      _ ≤ (i : ℝ≥0) * 3 := mul_le_mul_of_nonneg_left hslope zero_le
      _ = 3 * (i : ℝ≥0) := mul_comm _ _
      _ ≤ E := hcurrent
  have hidentity : (affineSurvivalEnvelope E (3 * (1 - eps)) i : ℝ) =
      (E : ℝ) - 3 * i + 3 * eps * i := by
    rw [affineSurvivalEnvelope, NNReal.coe_sub hchosen]
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_sub heps, NNReal.coe_one]
    ring
  have hclockR : (3 : ℝ) * i ≤ E := by exact_mod_cast hcurrent
  have hepsR : ((eps * E : ℝ≥0) : ℝ) ≤ ((E - 3 * (n : ℝ≥0) : ℝ≥0) : ℝ) := hepsClock
  simp only [NNReal.coe_mul, NNReal.coe_sub hclock.le, NNReal.coe_ofNat, NNReal.coe_natCast] at hepsR
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hproduct := mul_le_mul_of_nonneg_left hclockR (NNReal.coe_nonneg eps)
  have hnonneg : 0 ≤ 3 * (eps : ℝ) * i := by positivity
  constructor <;> rw [← NNReal.coe_le_coe] <;>
    simp only [NNReal.coe_sub hcurrent, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, hidentity]
  · linarith only [hnonneg]
  · nlinarith only [hepsR, hiR, hproduct]

theorem sharp_quadratic_pair_scale
    (N E p x C : ℝ≥0) (hC : 0 < C) (hE : E ≤ N ^ 2)
    (hx : N * p ^ 2 / (2 * C) ≤ x) :
    (E * p) ^ 2 ≤ (2 * C) * N ^ 3 * x := by
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 * C)).mp hx
  calc
    _ ≤ (N ^ 2 * p) ^ 2 := by gcongr
    _ = N ^ 3 * (N * p ^ 2) := by ring
    _ ≤ N ^ 3 * (x * (2 * C)) := mul_le_mul_of_nonneg_left hmul zero_le
    _ = _ := by ring

theorem sharp_clock_cubic_cancellation
    (N E p x C D R : ℝ≥0) (hC : 0 < C) (hx : 0 < x) (hD : 0 < D)
    (hE : E ≤ N ^ 2) (hpair : N * p ^ 2 / (2 * C) ≤ x)
    (hfloor : E * p * x ≤ 8 * D) (henvelope : R ≤ 2 * (E * p)) :
    D⁻¹ * R ^ 3 ≤ (128 * C) * N ^ 3 := by
  have hbound := inv_mul_cube_le_of_quadratic_pairScale hx hD hfloor henvelope
    (sharp_quadratic_pair_scale N E p x C hC hE hpair)
  convert hbound using 1 <;> ring

end

end Erdos207
