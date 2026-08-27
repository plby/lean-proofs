/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RoundedSharpClockArithmetic

/-! # A constant retrospective transfer factor, including a growing prescription cutoff -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem boundedSharpSurvivalTheta_coe_eq
    (M d K : ℕ) (hM : 0 < M) (hdM : d ≤ M) :
    (boundedSharpSurvivalTheta M d K : ℝ) = 1 - ((d - K : ℕ) : ℝ) / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : d - K ≤ M := (Nat.sub_le d K).trans hdM
  simp only [boundedSharpSurvivalTheta, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_inv, Nat.cast_sub hsub]
  field_simp

theorem boundedSharpTransferFactor_le_two
    (M d K : ℕ) (hM : 0 < M) (hdM : d ≤ M)
    (hsmall : 2 * K * (d - K) ≤ M) :
    (boundedSharpSurvivalTheta M d K ^ K)⁻¹ ≤ (2 : ℝ≥0) := by
  let theta : ℝ := boundedSharpSurvivalTheta M d K
  have ht0 : 0 ≤ theta := NNReal.coe_nonneg _
  have hBernoulli := one_add_mul_sub_le_pow (by linarith only [ht0] : -1 ≤ theta) K
  have hidentity : theta = 1 - ((d - K : ℕ) : ℝ) / M := boundedSharpSurvivalTheta_coe_eq M d K hM hdM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsmallR : (2 : ℝ) * K * ((d - K : ℕ) : ℝ) ≤ M := by exact_mod_cast hsmall
  have hratio : (K : ℝ) * (((d - K : ℕ) : ℝ) / M) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hMr]
    linarith only [hsmallR]
  have hhalf : (1 / 2 : ℝ) ≤ theta ^ K := by
    apply le_trans _ hBernoulli
    rw [hidentity]
    nlinarith only [hratio]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat]
  change (theta ^ K)⁻¹ ≤ 2
  apply (inv_le_iff_one_le_mul₀ (by linarith only [hhalf] : 0 < theta ^ K)).mpr
  linarith only [hhalf]

theorem rounded_sharp_transfer_small
    (L x e : ℝ) (K : ℕ) (hL : 6 ≤ L) (hx : 0 < x) (he : 0 ≤ e)
    (hsmall : 6 * (K : ℝ) ≤ L) :
    2 * K * (⌊x - e⌋₊ - K) ≤ ⌈L * (x + e) / 3⌉₊ := by
  have hfloor : (⌊x - e⌋₊ : ℝ) ≤ x := by
    by_cases hxe : 0 ≤ x - e
    · exact (Nat.floor_le hxe).trans (by linarith only [he])
    · rw [Nat.floor_eq_zero.mpr (show x - e < 1 by linarith only [hxe])]
      simpa only [Nat.cast_zero] using hx.le
  have hsubFloor : ((⌊x - e⌋₊ - K : ℕ) : ℝ) ≤ (⌊x - e⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_le ⌊x - e⌋₊ K
  have hsub : ((⌊x - e⌋₊ - K : ℕ) : ℝ) ≤ x := hsubFloor.trans hfloor
  have hceil := Nat.le_ceil (L * (x + e) / 3)
  have hLe := mul_nonneg (by linarith only [hL] : 0 ≤ L) he
  have hproduct := mul_le_mul_of_nonneg_right hsmall hx.le
  have hbound : (2 : ℝ) * K * ((⌊x - e⌋₊ - K : ℕ) : ℝ) ≤ (⌈L * (x + e) / 3⌉₊ : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 2 * K)
    nlinarith only [hceil, hLe, hproduct, hscaled]
  exact_mod_cast hbound

theorem rounded_sharp_transfer_factor_le_two
    (L x e : ℝ) (K : ℕ) (hL : 6 ≤ L) (hx : 0 < x) (he : 0 ≤ e)
    (hsmall : 6 * (K : ℝ) ≤ L) :
    (boundedSharpSurvivalTheta ⌈L * (x + e) / 3⌉₊ ⌊x - e⌋₊ K ^ K)⁻¹ ≤ (2 : ℝ≥0) := by
  have hcoherence := rounded_sharp_schedule_coherence L x e K hL hx he
  exact boundedSharpTransferFactor_le_two _ _ _ hcoherence.1 hcoherence.2.1
    (rounded_sharp_transfer_small L x e K hL hx he hsmall)

end

end Erdos207
