/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredStepBounds

/-! # Exact cancellation and moments for a statistic divided by its target -/

namespace Erdos207

theorem relative_observable_increment
    (Y X f fp : ℝ) (hf : f ≠ 0) (hfp : fp ≠ 0) :
    (Y + X) / fp - Y / f = (X - Y * (fp - f) / f) / fp := by
  field_simp
  <;> ring

theorem relative_observable_expectation
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (Y f fp : ℝ) (hf : f ≠ 0) (hfp : fp ≠ 0) :
    L.expectationReal (fun ω ↦ (Y + X ω) / fp - Y / f) =
      (L.expectationReal X - Y * (fp - f) / f) / fp := by
  simp_rw [relative_observable_increment Y _ f fp hf hfp, div_eq_mul_inv]
  rw [FiniteLaw.expectationReal_mul_const, FiniteLaw.expectationReal_sub,
    FiniteLaw.expectationReal_const]

theorem relative_observable_drift_error
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (Y f fp H A rawError targetError : ℝ)
    (hY : 0 ≤ Y) (hf : 0 < f) (hfp : 0 < fp)
    (hraw : |L.expectationReal X + Y * H / A| ≤ rawError)
    (htarget : |fp - f + f * H / A| ≤ targetError) :
    |L.expectationReal (fun ω ↦ (Y + X ω) / fp - Y / f)| ≤
      (rawError + Y * targetError / f) / fp := by
  rw [relative_observable_expectation L X Y f fp hf.ne' hfp.ne', abs_div, abs_of_pos hfp]
  apply div_le_div_of_nonneg_right _ hfp.le
  have heq : L.expectationReal X - Y * (fp - f) / f =
      (L.expectationReal X + Y * H / A) - (Y / f) * (fp - f + f * H / A) := by
    field_simp
    <;> ring
  rw [heq]
  calc
    _ ≤ |L.expectationReal X + Y * H / A| + |Y / f * (fp - f + f * H / A)| := abs_sub _ _
    _ = |L.expectationReal X + Y * H / A| + (Y / f) * |fp - f + f * H / A| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hY hf.le)]
    _ ≤ rawError + (Y / f) * targetError :=
      add_le_add hraw (mul_le_mul_of_nonneg_left htarget (div_nonneg hY hf.le))
    _ = _ := by ring

theorem relative_observable_jump_bound
    (Y X f fp J : ℝ) (hY : 0 ≤ Y) (hf : 0 < f) (hfp : 0 < fp) (hJ : |X| ≤ J) :
    |(Y + X) / fp - Y / f| ≤ (J + Y * |fp - f| / f) / fp := by
  rw [relative_observable_increment Y X f fp hf.ne' hfp.ne', abs_div, abs_of_pos hfp]
  apply div_le_div_of_nonneg_right _ hfp.le
  calc
    _ ≤ |X| + |Y * (fp - f) / f| := abs_sub _ _
    _ = |X| + Y * |fp - f| / f := by rw [abs_div, abs_mul, abs_of_nonneg hY, abs_of_pos hf]
    _ ≤ _ := add_le_add hJ le_rfl

theorem relative_observable_secondMoment
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (Y f fp v : ℝ) (hf : f ≠ 0) (hfp : fp ≠ 0)
    (hv : L.expectationReal (fun ω ↦ X ω ^ 2) ≤ v) :
    L.expectationReal (fun ω ↦ ((Y + X ω) / fp - Y / f) ^ 2) ≤
      (2 * v + 2 * (Y * (fp - f) / f) ^ 2) / fp ^ 2 := by
  let d := Y * (fp - f) / f
  have hpoint : ∀ ω, (X ω - d) ^ 2 ≤ 2 * X ω ^ 2 + 2 * d ^ 2 := by
    intro ω
    nlinarith only [sq_nonneg (X ω + d)]
  simp_rw [relative_observable_increment Y _ f fp hf hfp, div_pow]
  change L.expectationReal (fun ω ↦ (X ω - d) ^ 2 / fp ^ 2) ≤ _
  simp only [div_eq_mul_inv, FiniteLaw.expectationReal_mul_const]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg fp))
  calc
    _ ≤ L.expectationReal (fun ω ↦ 2 * X ω ^ 2 + 2 * d ^ 2) := L.expectationReal_mono hpoint
    _ = 2 * L.expectationReal (fun ω ↦ X ω ^ 2) + 2 * d ^ 2 := by
      rw [FiniteLaw.expectationReal_add, FiniteLaw.expectationReal_const_mul, FiniteLaw.expectationReal_const]
    _ ≤ 2 * v + 2 * d ^ 2 := add_le_add (mul_le_mul_of_nonneg_left hv (by norm_num)) le_rfl
    _ = _ := by simp only [d, div_eq_mul_inv, mul_pow, inv_pow]

theorem relative_observable_hazard_drift_error
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (Y f fp H A R delta er targetError : ℝ)
    (hY : 0 ≤ Y) (hf : 0 < f) (hfp : 0 < fp) (hA : 0 < A) (hR : 0 < R)
    (hraw : |L.expectationReal X + Y * H / R| ≤ Y * delta / R)
    (hdenom : |R - A| ≤ er)
    (htarget : |fp - f + f * H / A| ≤ targetError) :
    |L.expectationReal (fun ω ↦ (Y + X ω) / fp - Y / f)| ≤
      (Y / fp) * (delta / R + |H| * er / (R * A) + targetError / f) := by
  have hchange := abs_div_sub_div_le_of_errors (x := Y * H) (y := Y * H)
    (ex := 0) hR hA (by simp) hdenom
  simp only [zero_div, zero_add, abs_mul, abs_of_nonneg hY] at hchange
  have hrawA : |L.expectationReal X + Y * H / A| ≤
      Y * delta / R + Y * |H| * er / (R * A) := by
    calc
      _ = |(L.expectationReal X + Y * H / R) - (Y * H / R - Y * H / A)| := by
        congr 1
        ring
      _ ≤ |L.expectationReal X + Y * H / R| + |Y * H / R - Y * H / A| := abs_sub _ _
      _ ≤ _ := add_le_add hraw hchange
  calc
    _ ≤ (Y * delta / R + Y * |H| * er / (R * A) + Y * targetError / f) / fp :=
      relative_observable_drift_error L X Y f fp H A _ targetError hY hf hfp hrawA htarget
    _ = _ := by ring

end Erdos207
