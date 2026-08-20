/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Elementary bounds for the disk Poisson kernel

This file supplies the real inequalities used to dominate a disk Poisson
kernel by the one-dimensional Hardy--Littlewood kernel.  The constants are
deliberately non-optimal: their only purpose is to be uniform in the two
radii.
-/

namespace Erdos515

/-- On `[-π, π]`, the angular defect of cosine dominates `x² / 8`. -/
lemma one_eighth_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ Real.pi) :
    x ^ 2 / 8 ≤ 1 - Real.cos x := by
  have hpi_sq : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  have hcoef : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith
  have hcos := Real.cos_le_one_sub_mul_cos_sq hx
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
  nlinarith

/--
Normalized near-boundary Poisson-kernel estimate.  The denominator on the
right is the standard approximate-identity kernel at scale `1 - ρ`.
-/
lemma normalized_poisson_kernel_le {rho x : ℝ}
    (hrho_lower : (1 / 2 : ℝ) ≤ rho) (hrho_upper : rho < 1)
    (hx : |x| ≤ Real.pi) :
    (1 - rho ^ 2) / (1 + rho ^ 2 - 2 * rho * Real.cos x) ≤
      16 * (1 - rho) / ((1 - rho) ^ 2 + x ^ 2) := by
  have hdelta : 0 < 1 - rho := sub_pos.mpr hrho_upper
  have hcos : x ^ 2 / 8 ≤ 1 - Real.cos x := one_eighth_sq_le_one_sub_cos hx
  have hcos_nonneg : 0 ≤ 1 - Real.cos x :=
    le_trans (by positivity : 0 ≤ x ^ 2 / 8) hcos
  have hone : 1 ≤ 2 * rho := by linarith
  have hang : x ^ 2 / 8 ≤ 2 * rho * (1 - Real.cos x) := by
    calc
      x ^ 2 / 8 ≤ 1 - Real.cos x := hcos
      _ = 1 * (1 - Real.cos x) := by ring
      _ ≤ (2 * rho) * (1 - Real.cos x) :=
        mul_le_mul_of_nonneg_right hone hcos_nonneg
  have hden : (1 - rho) ^ 2 + x ^ 2 / 8 ≤
      1 + rho ^ 2 - 2 * rho * Real.cos x := by
    nlinarith
  have hden_pos : 0 < 1 + rho ^ 2 - 2 * rho * Real.cos x := by
    have hs : 0 < (1 - rho) ^ 2 := sq_pos_of_pos hdelta
    nlinarith [sq_nonneg x]
  have hmodel_pos : 0 < (1 - rho) ^ 2 + x ^ 2 := by
    have hs : 0 < (1 - rho) ^ 2 := sq_pos_of_pos hdelta
    nlinarith [sq_nonneg x]
  rw [div_le_div_iff₀ hden_pos hmodel_pos]
  have hnum : 1 - rho ^ 2 ≤ 2 * (1 - rho) := by
    nlinarith [sq_nonneg (1 - rho)]
  have hmodel_nonneg : 0 ≤ (1 - rho) ^ 2 + x ^ 2 := by positivity
  have hmul₁ := mul_le_mul_of_nonneg_right hnum hmodel_nonneg
  have hmodel_le : (1 - rho) ^ 2 + x ^ 2 ≤
      8 * (1 + rho ^ 2 - 2 * rho * Real.cos x) := by
    nlinarith [sq_nonneg (1 - rho), sq_nonneg x]
  have hmul₂ := mul_le_mul_of_nonneg_left hmodel_le
    (show 0 ≤ 2 * (1 - rho) by positivity)
  calc
    (1 - rho ^ 2) * ((1 - rho) ^ 2 + x ^ 2) ≤
        (2 * (1 - rho)) * ((1 - rho) ^ 2 + x ^ 2) := hmul₁
    _ ≤ (2 * (1 - rho)) *
        (8 * (1 + rho ^ 2 - 2 * rho * Real.cos x)) := hmul₂
    _ = 16 * (1 - rho) *
        (1 + rho ^ 2 - 2 * rho * Real.cos x) := by ring

/--
Unnormalized near-boundary estimate for the Poisson kernel on a circle of
radius `R`.  It is stated in the form used by the maximal-function bridge.
-/
lemma poisson_kernel_near_boundary_le {R r x : ℝ}
    (hR : 0 < R) (hr_lower : R / 2 ≤ r) (hr_upper : r < R)
    (hx : |x| ≤ Real.pi) :
    (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos x) ≤
      16 * ((R - r) / R) / (((R - r) / R) ^ 2 + x ^ 2) := by
  have hrho_lower : (1 / 2 : ℝ) ≤ r / R := by
    rw [le_div_iff₀ hR]
    simpa [div_eq_mul_inv, mul_comm] using hr_lower
  have hrho_upper : r / R < 1 := (div_lt_one hR).2 hr_upper
  have h := normalized_poisson_kernel_le hrho_lower hrho_upper hx
  have hRne : R ≠ 0 := ne_of_gt hR
  convert h using 1 <;> field_simp

/--
Away from the boundary the Poisson kernel is uniformly bounded.  The bound
`4` is sufficient for all later integral estimates.
-/
lemma poisson_kernel_small_radius_le {R r x : ℝ}
    (hR : 0 < R) (hr_nonneg : 0 ≤ r) (hr_upper : r ≤ R / 2) :
    (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos x) ≤ 4 := by
  have hcos_nonneg : 0 ≤ 1 - Real.cos x := by
    linarith [Real.cos_le_one x]
  have hcoef_nonneg : 0 ≤ 2 * R * r := by positivity
  have hgap_pos : 0 < R - r := by linarith
  have hden_lower : (R - r) ^ 2 ≤
      R ^ 2 + r ^ 2 - 2 * R * r * Real.cos x := by
    have := mul_nonneg hcoef_nonneg hcos_nonneg
    nlinarith
  have hden_pos : 0 < R ^ 2 + r ^ 2 - 2 * R * r * Real.cos x :=
    lt_of_lt_of_le (sq_pos_of_pos hgap_pos) hden_lower
  rw [div_le_iff₀ hden_pos]
  have hleft : 0 ≤ R / 2 - r := by linarith
  have hright : 0 ≤ 3 * R / 2 - r := by linarith
  have hgap_lower : R ^ 2 / 4 ≤ (R - r) ^ 2 := by
    have := mul_nonneg hleft hright
    nlinarith
  have hnum : R ^ 2 - r ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg r]
  nlinarith

end Erdos515
