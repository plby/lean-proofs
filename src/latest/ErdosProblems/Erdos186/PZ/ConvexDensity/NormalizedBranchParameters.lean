/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.CapScale
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphScale
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedGeometry

/-! # Explicit parameters for the normalized large-hull branch -/

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Absolute volume supplied by the normalized relative-volume dichotomy. -/
def normalizedLargeHullVolume (d : ℕ) (epsilon delta : ℝ) : ℝ :=
  delta ^ tau epsilon * (((d + 1 : ℕ) : ℝ)⁻¹) ^ d

/-- Inball radius obtained from the elementary volume-to-inradius theorem. -/
def normalizedLargeHullInradius (d : ℕ) (epsilon delta : ℝ) : ℝ :=
  (normalizedLargeHullVolume d epsilon delta /
      (2 * Real.sqrt d) ^ (d - 1)) /
    (((d + 1 : ℕ) : ℝ))

/-- Physical half-width of the upper-boundary graph window. -/
def normalizedGraphWindowRadius (d : ℕ) (epsilon delta : ℝ) : ℝ :=
  normalizedLargeHullInradius d epsilon delta /
    (4 * Real.sqrt (d - 1 : ℕ))

/-- Every point of the common hull is within this distance of its inball
centre, because both lie in the normalized outer ball. -/
def normalizedCommonHullOuterRadius (d : ℕ) : ℝ :=
  2 * Real.sqrt d

/-- Dimension-only coefficient in the graph-window radius. -/
def normalizedGraphWindowCoefficient (d : ℕ) : ℝ :=
  (((((d + 1 : ℕ) : ℝ)⁻¹) ^ d /
      (2 * Real.sqrt d) ^ (d - 1)) /
      (((d + 1 : ℕ) : ℝ))) /
    (4 * Real.sqrt (d - 1 : ℕ))

theorem normalizedLargeHullVolume_pos {d : ℕ} {epsilon delta : ℝ}
    (hdelta : 0 < delta) :
    0 < normalizedLargeHullVolume d epsilon delta := by
  simp only [normalizedLargeHullVolume]
  positivity

theorem normalizedLargeHullInradius_pos {d : ℕ} (hd : 0 < d)
    {epsilon delta : ℝ} (hdelta : 0 < delta) :
    0 < normalizedLargeHullInradius d epsilon delta := by
  rw [normalizedLargeHullInradius]
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by positivity
  exact div_pos
    (div_pos (normalizedLargeHullVolume_pos hdelta)
      (pow_pos (mul_pos (by norm_num) hsqrt) _))
    (by positivity)

theorem normalizedGraphWindowRadius_pos {d : ℕ} (hd : 2 ≤ d)
    {epsilon delta : ℝ} (hdelta : 0 < delta) :
    0 < normalizedGraphWindowRadius d epsilon delta := by
  rw [normalizedGraphWindowRadius]
  exact div_pos
    (normalizedLargeHullInradius_pos (by omega : 0 < d) hdelta)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by exact_mod_cast
      (show 0 < d - 1 by omega))))

theorem normalizedCommonHullOuterRadius_pos {d : ℕ} (hd : 0 < d) :
    0 < normalizedCommonHullOuterRadius d := by
  simp only [normalizedCommonHullOuterRadius]
  positivity

theorem normalizedGraphWindowCoefficient_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < normalizedGraphWindowCoefficient d := by
  rw [normalizedGraphWindowCoefficient]
  have hsd : 0 < Real.sqrt (d : ℝ) := by positivity
  have hsp : 0 < Real.sqrt ((d - 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d - 1 by omega))
  positivity

theorem normalizedGraphWindowRadius_eq {d : ℕ} (hd : 2 ≤ d)
    {epsilon delta : ℝ} (hdelta : 0 < delta) :
    normalizedGraphWindowRadius d epsilon delta =
      normalizedGraphWindowCoefficient d * delta ^ tau epsilon := by
  simp only [normalizedGraphWindowRadius, normalizedLargeHullInradius,
    normalizedLargeHullVolume, normalizedGraphWindowCoefficient]
  have hpow : 0 < delta ^ tau epsilon := Real.rpow_pos_of_pos hdelta _
  field_simp

theorem normalizedGraphWindowRadius_lt_inradius {d : ℕ} (hd : 2 ≤ d)
    {epsilon delta : ℝ} (hdelta : 0 < delta) :
    normalizedGraphWindowRadius d epsilon delta <
      normalizedLargeHullInradius d epsilon delta := by
  have hinner := normalizedLargeHullInradius_pos
    (epsilon := epsilon) (delta := delta) (by omega : 0 < d) hdelta
  have hsqrt : 1 ≤ Real.sqrt ((d - 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d - 1 by omega))
  rw [normalizedGraphWindowRadius]
  have hden : 1 < 4 * Real.sqrt ((d - 1 : ℕ) : ℝ) := by linarith
  exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)

theorem normalizedGraphWindowRadius_le_outer {d : ℕ} (hd : 2 ≤ d)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    normalizedGraphWindowRadius d epsilon delta ≤
      normalizedCommonHullOuterRadius d := by
  have hpow : delta ^ tau epsilon ≤ 1 :=
    Real.rpow_le_one hdelta.le hdeltaOne (tau_pos hepsilon).le
  have hunit : normalizedLargeHullInradius d epsilon delta ≤ 1 := by
    simp only [normalizedLargeHullInradius, normalizedLargeHullVolume]
    have hsqrt : 1 ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
    have hd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have hinv : (((d + 1 : ℕ) : ℝ)⁻¹) ^ d ≤ 1 := by
      exact pow_le_one₀ (by positivity)
        ((inv_le_one₀ (by positivity)).2 hd1)
    have hden : 1 ≤ (2 * Real.sqrt (d : ℝ)) ^ (d - 1) := by
      exact one_le_pow₀ (by nlinarith)
    have hnum :
        delta ^ tau epsilon * (((d + 1 : ℕ) : ℝ)⁻¹) ^ d ≤ 1 := by
      have hpowNonneg : 0 ≤ delta ^ tau epsilon :=
        Real.rpow_nonneg hdelta.le _
      have hinvNonneg : 0 ≤ (((d + 1 : ℕ) : ℝ)⁻¹) ^ d := by
        positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hpow)
        (sub_nonneg.mpr hinv)]
    apply (div_le_one (by positivity)).2
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hq := (normalizedGraphWindowRadius_lt_inradius hd hdelta).le.trans hunit
  have hsqrt : 1 ≤ Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
  rw [normalizedCommonHullOuterRadius]
  nlinarith

theorem two_mul_normalizedGraphWindowRadius_le {d : ℕ} (hd : 2 ≤ d)
    {epsilon delta : ℝ} (hdelta : 0 < delta) :
    2 * normalizedGraphWindowRadius d epsilon delta ≤
      normalizedLargeHullInradius d epsilon delta /
        Real.sqrt (d - 1 : ℕ) := by
  exact two_mul_graphWindowRadius_le (by omega : 0 < d - 1)
    (normalizedLargeHullInradius_pos (by omega : 0 < d) hdelta).le

end
end Erdos186.PZ.ConvexDensity
