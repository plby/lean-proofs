/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Selector normalization and relative-drift budgets for a small pattern -/

namespace Erdos207

theorem pattern_selector_denominator_bounds
    (r R excluded L x e : ℝ) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hcount : r = R + excluded) (hexcluded : 0 ≤ excluded)
    (hsmallExcluded : excluded ≤ L * e / 3)
    (hglobal : |r - L * x / 3| ≤ L * e / 3) (hsmall : e ≤ x / 4) :
    |R - L * x / 3| ≤ 2 * L * e / 3 ∧ L * x / 6 ≤ R := by
  have hband : |R - L * x / 3| ≤ 2 * L * e / 3 := by
    calc
      _ = |(r - L * x / 3) - excluded| := by rw [hcount]; congr 1; ring
      _ ≤ |r - L * x / 3| + |excluded| := abs_sub _ _
      _ ≤ L * e / 3 + L * e / 3 := by
        rw [abs_of_nonneg hexcluded]
        exact add_le_add hglobal hsmallExcluded
      _ = _ := by ring
  refine ⟨hband, ?_⟩
  have hproduct := mul_le_mul_of_nonneg_left hsmall hL
  have hlo := (abs_le.mp hband).1
  nlinarith only [hproduct, hlo]

theorem pattern_relative_hazard_rate_le
    (C G e L x H R A er : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) (he : 0 ≤ e)
    (hL : 0 < L) (hx : 0 < x) (hR : L * x / 6 ≤ R)
    (hA : A = L * x / 3) (hH : |H| ≤ G * x) (her : er ≤ 2 * L * e / 3) :
    C * e / R + |H| * er / (R * A) ≤ 6 * (C + 2 * G) * e / (L * x) := by
  subst A
  have hRpos : 0 < R := (by positivity : 0 < L * x / 6).trans_le hR
  have hfirst : C * e / R ≤ 6 * C * e / (L * x) := by
    calc
      _ ≤ C * e / (L * x / 6) := div_le_div_of_nonneg_left (by positivity) (by positivity) hR
      _ = _ := by ring
  have hsecond : |H| * er / (R * (L * x / 3)) ≤ 12 * G * e / (L * x) := by
    calc
      _ ≤ |H| * (2 * L * e / 3) / (R * (L * x / 3)) := by
        gcongr
      _ ≤ (G * x) * (2 * L * e / 3) / (R * (L * x / 3)) := by
        gcongr
      _ ≤ (G * x) * (2 * L * e / 3) / ((L * x / 6) * (L * x / 3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hR (by positivity))
      _ = _ := by field_simp; ring
  calc
    _ ≤ 6 * C * e / (L * x) + 12 * G * e / (L * x) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem pattern_relative_drift_envelope_budget
    (C G e L x z tau f prefactor : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) (he : 0 ≤ e)
    (hL : 0 < L) (hx : 0 < x) (hf : 0 < f) (htau : 0 ≤ tau)
    (hprefactor : prefactor ≤ 4) (hz : 8 * (C + 2 * G) * e / x ≤ z)
    (htaylor : 4 * tau / f ≤ 3 * z / L) :
    prefactor * (6 * (C + 2 * G) * e / (L * x) + tau / f) ≤ 6 * z / L := by
  have hpair : 24 * (C + 2 * G) * e / (L * x) ≤ 3 * z / L := by
    calc
      _ = 3 * (8 * (C + 2 * G) * e / x) / L := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) hL.le
  calc
    _ ≤ 4 * (6 * (C + 2 * G) * e / (L * x) + tau / f) :=
      mul_le_mul_of_nonneg_right hprefactor (by positivity)
    _ = 24 * (C + 2 * G) * e / (L * x) + 4 * tau / f := by ring
    _ ≤ 3 * z / L + 3 * z / L := add_le_add hpair htaylor
    _ = _ := by ring

end Erdos207
