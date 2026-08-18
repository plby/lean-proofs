/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedBranchParameters

/-! # The initial-cell error is negligible in graph coordinates -/

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Radius of an initial assignment fibre after the centered graph-window
chart, using the elementary Lipschitz constant of `GraphWindowAffine`. -/
def normalizedChartFiberRadius (d : ℕ) (epsilon delta : ℝ) : ℝ :=
  4 * (Real.sqrt d * (initialRadius d delta / 2)) *
    ((2 * normalizedGraphWindowRadius d epsilon delta)⁻¹ +
      (normalizedCommonHullOuterRadius d)⁻¹)

def chartFiberSaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  1 / (d : ℝ) - tau epsilon - 2 * gridRate d

theorem chartFiberSaving_pos {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    0 < chartFiberSaving d epsilon := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : epsilon * ((d : ℝ) + 1) ≤ 1 := by
    have hden : 0 < (d : ℝ) + 1 := by positivity
    calc
      epsilon * ((d : ℝ) + 1) ≤
          (1 / ((d : ℝ) + 1)) * ((d : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hepsilonLe hden.le
      _ = 1 := by field_simp
  simp only [chartFiberSaving, tau, gridRate]
  field_simp
  nlinarith

/-- One cutoff makes every initial assignment fibre have chart radius at
most the square of the integral graph mesh. -/
theorem exists_deltaZero_chartFiberRadius
    {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        normalizedChartFiberRadius d epsilon delta ≤
          1 / (graphGridSize d delta : ℝ) ^ (2 : ℕ) := by
  let c0 := normalizedGraphWindowCoefficient d
  have hc0 : 0 < c0 := normalizedGraphWindowCoefficient_pos hd
  let C : ℝ := 256 * Real.sqrt d / c0
  obtain ⟨deltaPower, hpowerPos, hpowerOne, hpower⟩ :=
    exists_deltaZero_const_mul_log_one_div_pow_mul_rpow_le
      C 0 (chartFiberSaving_pos hd hepsilon hepsilonLe) zero_lt_one
  let deltaZero := min deltaPower (1 / 2)
  refine ⟨deltaZero, by positivity, by
    calc deltaZero ≤ 1 / 2 := min_le_right _ _
         _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hsmall
  have hdeltaOne : delta ≤ 1 :=
    hsmall.le.trans (min_le_right _ _) |>.trans (by norm_num)
  have hq : 0 < normalizedGraphWindowRadius d epsilon delta :=
    normalizedGraphWindowRadius_pos hd hdelta
  have houter : 0 < normalizedCommonHullOuterRadius d :=
    normalizedCommonHullOuterRadius_pos (by omega : 0 < d)
  have hqouter := normalizedGraphWindowRadius_le_outer hd hepsilon
    hdelta hdeltaOne
  have ha :
      (2 * normalizedGraphWindowRadius d epsilon delta)⁻¹ +
          (normalizedCommonHullOuterRadius d)⁻¹ ≤
        2 / normalizedGraphWindowRadius d epsilon delta := by
    have h₁ : (2 * normalizedGraphWindowRadius d epsilon delta)⁻¹ ≤
        1 / normalizedGraphWindowRadius d epsilon delta := by
      simpa only [one_div] using
        (inv_le_inv₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hq) hq).2
          (by linarith)
    have h₂ : (normalizedCommonHullOuterRadius d)⁻¹ ≤
        1 / normalizedGraphWindowRadius d epsilon delta := by
      simpa only [one_div] using (inv_le_inv₀ houter hq).2 hqouter
    simp only [one_div] at h₁ h₂
    rw [div_eq_mul_inv]
    linarith
  have hradius : normalizedChartFiberRadius d epsilon delta ≤
      (64 * Real.sqrt d / c0) *
        delta ^ (1 / (d : ℝ) - tau epsilon) := by
    rw [normalizedGraphWindowRadius_eq hd hdelta] at ha
    rw [normalizedChartFiberRadius, initialRadius,
      normalizedGraphWindowRadius_eq hd hdelta]
    have hpowTau : 0 < delta ^ tau epsilon := by positivity
    calc
      4 * (Real.sqrt (d : ℝ) *
            (16 * delta ^ (1 / (d : ℝ)) / 2)) *
          ((2 * (c0 * delta ^ tau epsilon))⁻¹ +
            (normalizedCommonHullOuterRadius d)⁻¹)
          ≤ 4 * (Real.sqrt (d : ℝ) *
            (16 * delta ^ (1 / (d : ℝ)) / 2)) *
              (2 / (c0 * delta ^ tau epsilon)) := by
                gcongr
      _ = (64 * Real.sqrt d / c0) *
          delta ^ (1 / (d : ℝ) - tau epsilon) := by
            rw [Real.rpow_sub hdelta,
              show delta ^ tau epsilon = delta ^ tau epsilon by rfl]
            field_simp
            ring
  have hpow' := hpower delta hdelta
    (hsmall.trans_le (min_le_left _ _))
  have hscale : 4 * normalizedChartFiberRadius d epsilon delta *
      (realGridScale d delta) ^ (2 : ℕ) ≤ 1 := by
    calc
      4 * normalizedChartFiberRadius d epsilon delta *
          realGridScale d delta ^ (2 : ℕ) ≤
        C * delta ^ chartFiberSaving d epsilon := by
          rw [realGridScale, Real.rpow_neg hdelta.le, chartFiberSaving]
          calc
            4 * normalizedChartFiberRadius d epsilon delta *
                (delta ^ gridRate d)⁻¹ ^ 2 ≤
              4 * ((64 * Real.sqrt d / c0) *
                delta ^ (1 / (d : ℝ) - tau epsilon)) *
                (delta ^ gridRate d)⁻¹ ^ 2 := by gcongr
            _ = C * delta ^
                (1 / (d : ℝ) - tau epsilon - 2 * gridRate d) := by
                  have hpowEq :
                      delta ^ (1 / (d : ℝ) - tau epsilon - 2 * gridRate d) =
                        delta ^ (1 / (d : ℝ) - tau epsilon) *
                          (delta ^ gridRate d)⁻¹ ^ 2 := by
                    rw [show 2 * gridRate d = gridRate d * (2 : ℕ) by ring,
                      Real.rpow_sub hdelta,
                      Real.rpow_mul_natCast hdelta.le]
                    simp only [div_eq_mul_inv, inv_pow]
                  rw [hpowEq]
                  dsimp only [C]
                  ring
      _ ≤ 1 := by simpa [C] using hpow'
  have hmUpper := graphGridSize_cast_le_two_mul_realGridScale d
    hdelta hdeltaOne
  have hmPos : (0 : ℝ) < graphGridSize d delta := by
    exact_mod_cast graphGridSize_pos d hdelta hdeltaOne
  have hsPos := realGridScale_pos d hdelta
  rw [le_div_iff₀ (pow_pos hmPos 2)]
  have hmSq : (graphGridSize d delta : ℝ) ^ 2 ≤
      4 * realGridScale d delta ^ 2 := by nlinarith
  have hrNonneg : 0 ≤ normalizedChartFiberRadius d epsilon delta := by
    rw [normalizedChartFiberRadius]
    have hinitial : 0 < initialRadius d delta := by
      simp only [initialRadius]
      positivity
    positivity
  calc
    normalizedChartFiberRadius d epsilon delta *
          (graphGridSize d delta : ℝ) ^ 2 ≤
        normalizedChartFiberRadius d epsilon delta *
          (4 * realGridScale d delta ^ 2) :=
      mul_le_mul_of_nonneg_left hmSq hrNonneg
    _ = 4 * normalizedChartFiberRadius d epsilon delta *
          realGridScale d delta ^ 2 := by ring
    _ ≤ 1 := hscale

end
end Erdos186.PZ.ConvexDensity
