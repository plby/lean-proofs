/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.FiniteCap

/-!
# The direction-cap scale

The direction cap and the boundary graph use different integer scales in
Pham--Zakharov's argument.  The cap scale is reciprocal to the physical
graph-window radius `q`; its pigeonhole fraction is consequently a fixed
multiple of `q ^ n`.  The graph scale, by contrast, is the power of `delta`
defined in `GraphScale`.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- The real scale whose ceiling is used for the deterministic direction
cap.  The factor four simultaneously supplies the cap diameter bound and the
minimum mesh required by the Householder chart. -/
def realCapScale (n : ℕ) (q outer : ℝ) : ℝ :=
  4 * outer * Real.sqrt n / q

/-- Integral direction-cap scale. -/
def capGridSize (n : ℕ) (q outer : ℝ) : ℕ :=
  Nat.ceil (realCapScale n q outer)

theorem realCapScale_pos {n : ℕ} (hn : 0 < n) {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) :
    0 < realCapScale n q outer := by
  simp only [realCapScale]
  positivity

theorem capGridSize_pos {n : ℕ} (hn : 0 < n) {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) :
    0 < capGridSize n q outer := by
  exact Nat.ceil_pos.mpr (realCapScale_pos hn hq houter)

theorem realCapScale_le_capGridSize_cast (n : ℕ) (q outer : ℝ) :
    realCapScale n q outer ≤ (capGridSize n q outer : ℝ) := by
  exact Nat.le_ceil _

/-- Rounding the cap scale costs at most two when the physical window is no
wider than the enclosing radius. -/
theorem capGridSize_cast_le_two_mul_realCapScale
    {n : ℕ} (hn : 0 < n) {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) (hqouter : q ≤ outer) :
    (capGridSize n q outer : ℝ) ≤ 2 * realCapScale n q outer := by
  apply Nat.ceil_le_two_mul
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hratio : 1 ≤ outer / q := (le_div_iff₀ hq).2 (by simpa using hqouter)
  have hscale : 4 ≤ realCapScale n q outer := by
    rw [realCapScale]
    calc
      (4 : ℝ) ≤ 4 * (outer / q) * Real.sqrt n := by nlinarith
      _ = 4 * outer * Real.sqrt n / q := by field_simp
  linarith

/-- The chosen cap mesh is fine enough for both hypotheses of the centered
Householder cap chart. -/
theorem capGridSize_geometry_of_le
    {n : ℕ} (hn : 0 < n) {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) (hqouter : q ≤ outer) :
    4 * Real.sqrt n ≤ (capGridSize n q outer : ℝ) ∧
      outer * (2 * Real.sqrt n / (capGridSize n q outer : ℝ)) ≤ q := by
  have hmLower := realCapScale_le_capGridSize_cast n q outer
  have hmPos : (0 : ℝ) < capGridSize n q outer := by
    exact_mod_cast capGridSize_pos hn hq houter
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
  constructor
  · rw [realCapScale] at hmLower
    calc
      4 * Real.sqrt n ≤ 4 * outer * Real.sqrt n / q := by
        rw [le_div_iff₀ hq]
        nlinarith
      _ ≤ (capGridSize n q outer : ℝ) := hmLower
  · rw [show outer * (2 * Real.sqrt n /
        (capGridSize n q outer : ℝ)) =
        (outer * (2 * Real.sqrt n)) /
          (capGridSize n q outer : ℝ) by ring,
      div_le_iff₀ hmPos]
    calc
      outer * (2 * Real.sqrt n) ≤
          q * realCapScale n q outer := by
        rw [realCapScale]
        field_simp
        nlinarith [mul_pos houter hsqrt]
      _ ≤ q * (capGridSize n q outer : ℝ) :=
        mul_le_mul_of_nonneg_left hmLower hq.le

/-- Explicit lower fraction retained by the direction-cap pigeonhole after
rounding.  It is written in reciprocal-scale form so later algebra can
rewrite it directly as a dimension-dependent constant times `q ^ n`. -/
def roundedCapFractionLower (n : ℕ) (q outer : ℝ) : ℝ :=
  ((((2 * realCapScale n q outer)⁻¹ / 3) ^ n) / (2 * (n + 1)))

/-- Dimension/enclosing-radius coefficient in the cap fraction. -/
def capFractionCoefficient (n : ℕ) (outer : ℝ) : ℝ :=
  ((24 * outer * Real.sqrt n)⁻¹ ^ n) / (2 * (n + 1))

theorem capFractionCoefficient_pos {n : ℕ} (hn : 0 < n)
    {outer : ℝ} (houter : 0 < outer) :
    0 < capFractionCoefficient n outer := by
  simp only [capFractionCoefficient]
  positivity

theorem roundedCapFractionLower_eq {n : ℕ} (hn : 0 < n)
    {q outer : ℝ} (hq : 0 < q) (houter : 0 < outer) :
    roundedCapFractionLower n q outer =
      capFractionCoefficient n outer * q ^ n := by
  simp only [roundedCapFractionLower, realCapScale,
    capFractionCoefficient]
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
  rw [show (2 * (4 * outer * Real.sqrt (n : ℝ) / q))⁻¹ / 3 =
      (24 * outer * Real.sqrt (n : ℝ))⁻¹ * q by
    field_simp
    ring]
  rw [mul_pow]
  ring

theorem roundedCapFractionLower_le
    {n : ℕ} (hn : 0 < n) {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) (hqouter : q ≤ outer) :
    roundedCapFractionLower n q outer ≤
      ((((capGridSize n q outer : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) := by
  have hmPos : (0 : ℝ) < capGridSize n q outer := by
    exact_mod_cast capGridSize_pos hn hq houter
  have hsPos : 0 < realCapScale n q outer := realCapScale_pos hn hq houter
  have hmUpper := capGridSize_cast_le_two_mul_realCapScale hn hq houter hqouter
  have hinv : (2 * realCapScale n q outer)⁻¹ ≤
      (capGridSize n q outer : ℝ)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) hmPos).2 hmUpper
  have hthird : (2 * realCapScale n q outer)⁻¹ / 3 ≤
      (capGridSize n q outer : ℝ)⁻¹ / 3 := by linarith
  have hpow := pow_le_pow_left₀ (by positivity) hthird n
  simp only [roundedCapFractionLower]
  exact div_le_div_of_nonneg_right hpow (by positivity)

end
end Erdos186.PZ.ConvexDensity
