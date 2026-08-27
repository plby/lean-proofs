/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeObservableArithmetic

/-! # Clock-normalized relative moments with small-set jump cutoffs -/

namespace Erdos207

theorem relative_pattern_prefactor_bounds
    (Y f fp : ℝ) (hY : 0 ≤ Y) (hf : 0 < f) (hYf : Y ≤ 2 * f) (hfp : f / 2 ≤ fp) :
    Y / fp ≤ 4 ∧ 1 / fp ≤ 2 / f := by
  have hhalf : 0 < f / 2 := by positivity
  constructor
  · calc
      _ ≤ (2 * f) / (f / 2) := by gcongr
      _ = _ := by field_simp; norm_num
  · calc
      _ ≤ 1 / (f / 2) := one_div_le_one_div_of_le hhalf hfp
      _ = _ := by ring

theorem inverse_clock_le_relative_jump_scale
    (f L J : ℝ) (hf : 0 < f) (hfL : f ≤ L) (hJ : 1 ≤ J) : 1 / L ≤ J / f := by
  calc
    _ ≤ 1 / f := one_div_le_one_div_of_le hf hfL
    _ ≤ _ := div_le_div_of_nonneg_right hJ hf.le

theorem relative_pattern_clock_jump_budget
    (Y f fp L J D : ℝ) (hY : 0 ≤ Y) (hf : 0 < f) (hYf : Y ≤ 2 * f)
    (hfp : f / 2 ≤ fp) (hfL : f ≤ L) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hstep : |fp - f| / f ≤ D / L) :
    (J + Y * |fp - f| / f) / fp ≤ (2 + 4 * D) * J / f := by
  have hL : 0 < L := hf.trans_le hfL
  have hfpPos : 0 < fp := (by positivity : 0 < f / 2).trans_le hfp
  have hrat := relative_pattern_prefactor_bounds Y f fp hY hf hYf hfp
  have hJ0 : 0 ≤ J := by linarith
  have hclock := inverse_clock_le_relative_jump_scale f L J hf hfL hJ
  have hfirst : J / fp ≤ 2 * J / f := by
    calc
      _ = J * (1 / fp) := by ring
      _ ≤ J * (2 / f) := mul_le_mul_of_nonneg_left hrat.2 hJ0
      _ = _ := by ring
  have hsecond : (Y / fp) * (|fp - f| / f) ≤ 4 * D * J / f := by
    calc
      _ ≤ 4 * (D / L) := mul_le_mul hrat.1 hstep (by positivity) (by norm_num)
      _ = (4 * D) * (1 / L) := by ring
      _ ≤ (4 * D) * (J / f) := mul_le_mul_of_nonneg_left hclock (by positivity)
      _ = _ := by ring
  calc
    _ = J / fp + (Y / fp) * (|fp - f| / f) := by ring
    _ ≤ 2 * J / f + 4 * D * J / f := add_le_add hfirst hsecond
    _ = _ := by ring

theorem relative_pattern_clock_secondMoment_budget
    (Y f fp L J D G v : ℝ) (hY : 0 ≤ Y) (hf : 0 < f) (hYf : Y ≤ 2 * f)
    (hfp : f / 2 ≤ fp) (hfL : f ≤ L) (hJ : 1 ≤ J) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hstep : |fp - f| / f ≤ D / L) (hv : v ≤ 6 * G * J * Y / L) :
    (2 * v + 2 * (Y * (fp - f) / f) ^ 2) / fp ^ 2 ≤
      (96 * G + 32 * D ^ 2) * J / (f * L) := by
  have hL : 0 < L := hf.trans_le hfL
  have hfpPos : 0 < fp := (by positivity : 0 < f / 2).trans_le hfp
  have hrat := relative_pattern_prefactor_bounds Y f fp hY hf hYf hfp
  have hJ0 : 0 ≤ J := by linarith
  have hclock := inverse_clock_le_relative_jump_scale f L J hf hfL hJ
  have hratioSq : Y / fp ^ 2 ≤ 8 / f := by
    calc
      _ = (Y / fp) * (1 / fp) := by ring
      _ ≤ 4 * (2 / f) := mul_le_mul hrat.1 hrat.2 (by positivity) (by norm_num)
      _ = _ := by ring
  have hraw : 2 * v / fp ^ 2 ≤ 96 * G * J / (f * L) := by
    calc
      _ ≤ 2 * (6 * G * J * Y / L) / fp ^ 2 := by gcongr
      _ = (12 * G * J / L) * (Y / fp ^ 2) := by ring
      _ ≤ (12 * G * J / L) * (8 / f) :=
        mul_le_mul_of_nonneg_left hratioSq (by positivity)
      _ = _ := by ring
  have hdetAbs : |(Y / fp) * ((fp - f) / f)| ≤ 4 * D / L := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hY hfpPos.le), abs_div, abs_of_pos hf]
    calc
      _ ≤ 4 * (D / L) := mul_le_mul hrat.1 hstep (by positivity) (by norm_num)
      _ = _ := by ring
  have hdetSq := pow_le_pow_left₀ (abs_nonneg ((Y / fp) * ((fp - f) / f))) hdetAbs 2
  rw [sq_abs] at hdetSq
  have hdet : 2 * (Y * (fp - f) / f) ^ 2 / fp ^ 2 ≤ 32 * D ^ 2 * J / (f * L) := by
    calc
      _ = 2 * ((Y / fp) * ((fp - f) / f)) ^ 2 := by ring
      _ ≤ 2 * (4 * D / L) ^ 2 := mul_le_mul_of_nonneg_left hdetSq (by norm_num)
      _ = (32 * D ^ 2 / L) * (1 / L) := by ring
      _ ≤ (32 * D ^ 2 / L) * (J / f) :=
        mul_le_mul_of_nonneg_left hclock (by positivity)
      _ = _ := by ring
  calc
    _ = 2 * v / fp ^ 2 + 2 * (Y * (fp - f) / f) ^ 2 / fp ^ 2 := by ring
    _ ≤ 96 * G * J / (f * L) + 32 * D ^ 2 * J / (f * L) := add_le_add hraw hdet
    _ = _ := by ring

theorem relative_pattern_centered_clock_jump_budget
    (X sigma de f L J D Z : ℝ) (hf : 0 < f) (hfL : f ≤ L) (hJ : 1 ≤ J)
    (hZ : 0 ≤ Z) (hsigma : |sigma| = 1)
    (hX : |X| ≤ (2 + 4 * D) * J / f) (hde : |de| ≤ Z / L) :
    |sigma * X - de| ≤ (2 + 4 * D + Z) * J / f := by
  have hclock := inverse_clock_le_relative_jump_scale f L J hf hfL hJ
  have hdet : |de| ≤ Z * J / f := by
    calc
      _ ≤ Z / L := hde
      _ = Z * (1 / L) := by ring
      _ ≤ Z * (J / f) := mul_le_mul_of_nonneg_left hclock hZ
      _ = _ := by ring
  calc
    _ ≤ |sigma * X| + |de| := abs_sub _ _
    _ = |X| + |de| := by rw [abs_mul, hsigma, one_mul]
    _ ≤ (2 + 4 * D) * J / f + Z * J / f := add_le_add hX hdet
    _ = _ := by ring

theorem relative_pattern_centered_clock_secondMoment_budget
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω) (X : Ω → ℝ)
    (sigma de f L J D G Z : ℝ) (hf : 0 < f) (hfL : f ≤ L) (hJ : 1 ≤ J)
    (hsigma : |sigma| = 1)
    (hraw : law.expectationReal (fun ω ↦ X ω ^ 2) ≤ (96 * G + 32 * D ^ 2) * J / (f * L))
    (hde : |de| ≤ Z / L) :
    law.expectationReal (fun ω ↦ (sigma * X ω - de) ^ 2) ≤
      (192 * G + 64 * D ^ 2 + 2 * Z ^ 2) * J / (f * L) := by
  have hL : 0 < L := hf.trans_le hfL
  have hclock := inverse_clock_le_relative_jump_scale f L J hf hfL hJ
  have hdeSq : |de| ^ 2 ≤ Z ^ 2 * J / (f * L) := by
    calc
      _ ≤ (Z / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hde 2
      _ = (Z ^ 2 / L) * (1 / L) := by ring
      _ ≤ (Z ^ 2 / L) * (J / f) := mul_le_mul_of_nonneg_left hclock (by positivity)
      _ = _ := by ring
  have h := centered_step_secondMoment_le law X sigma 0 de _ hsigma hraw
  simp only [sub_zero, abs_zero, zero_add] at h
  calc
    _ ≤ 2 * ((96 * G + 32 * D ^ 2) * J / (f * L)) + 2 * |de| ^ 2 := h
    _ ≤ 2 * ((96 * G + 32 * D ^ 2) * J / (f * L)) + 2 * (Z ^ 2 * J / (f * L)) := by gcongr
    _ = _ := by ring

end Erdos207
