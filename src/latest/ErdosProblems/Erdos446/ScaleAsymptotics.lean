/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerCoefficient

/-!
# Erdős Problem 446: asymptotics of the selected depth

At the maximal admissible depth, `log y` is within a fixed factor of `2^K`,
and `log log y` is within a fixed factor of `K`.  These two comparisons are
the bridge from the finite combinatorial construction to Ford's final scale.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

noncomputable def fordScaleConstant (M : ℕ) : ℝ :=
  128 * (2 : ℝ) ^ M * Real.log 2

theorem fordScaleConstant_pos (M : ℕ) : 0 < fordScaleConstant M := by
  dsimp [fordScaleConstant]
  positivity

theorem log_fordConstructionScale (M K : ℕ) :
    Real.log (fordConstructionScale M K : ℝ) =
      fordScaleConstant M * (2 : ℝ) ^ K := by
  change Real.log (((2 ^ (128 * 2 ^ (M + K)) : ℕ) : ℝ)) = _
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  rw [pow_add]
  dsimp [fordScaleConstant]
  ring

theorem fordScaleDepth_log_bounds {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    fordScaleConstant M * (2 : ℝ) ^ fordScaleDepth M y ≤
        Real.log (y : ℝ) ∧
      Real.log (y : ℝ) ≤
        2 * fordScaleConstant M * (2 : ℝ) ^ fordScaleDepth M y := by
  let K := fordScaleDepth M y
  have hinter := fordScaleDepth_interval hy
  have hscalePos : (0 : ℝ) < fordConstructionScale M K := by
    exact_mod_cast (show 0 < fordConstructionScale M K by
      dsimp [fordConstructionScale]
      positivity)
  have hyPosNat : 0 < y :=
    (Nat.zero_lt_of_lt (depth_lt_fordConstructionScale M K)).trans_le hinter.1
  have hyPos : (0 : ℝ) < y := by exact_mod_cast hyPosNat
  constructor
  · rw [← log_fordConstructionScale]
    exact Real.log_le_log hscalePos (by exact_mod_cast hinter.1)
  · calc
      Real.log (y : ℝ) ≤
          Real.log ((fordConstructionScale M K : ℝ) ^ 2) :=
        Real.log_le_log hyPos (by exact_mod_cast hinter.2.le)
      _ = 2 * Real.log (fordConstructionScale M K : ℝ) := by
        rw [Real.log_pow]
        norm_num
      _ = 2 * fordScaleConstant M * (2 : ℝ) ^ K := by
        rw [log_fordConstructionScale]
        ring

theorem tendsto_fordScaleDepth_atTop (M : ℕ) :
    Tendsto (fordScaleDepth M) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop
    (max (fordConstructionScale M 1) (fordConstructionScale M K))] with y hy
  have h1 : fordConstructionScale M 1 ≤ y :=
    (le_max_left _ _).trans hy
  by_cases hK : K = 0
  · omega
  have hKy : K ≤ y := by
    exact (depth_lt_fordConstructionScale M K).le.trans
      ((le_max_right _ _).trans hy)
  exact Nat.le_findGreatest
    (P := fun j ↦ fordConstructionScale M j ≤ y) hKy
    ((le_max_right _ _).trans hy)

theorem tendsto_fordScaleDepth_cast_atTop (M : ℕ) :
    Tendsto (fun y : ℕ ↦ (fordScaleDepth M y : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_fordScaleDepth_atTop M)

theorem log_nat_isTheta_pow_fordScaleDepth (M : ℕ) :
    (fun y : ℕ ↦ Real.log (y : ℝ)) =Θ[atTop]
      (fun y : ℕ ↦ (2 : ℝ) ^ fordScaleDepth M y) := by
  let c := fordScaleConstant M
  have hc : 0 < c := fordScaleConstant_pos M
  constructor
  · apply Asymptotics.IsBigO.of_bound (2 * c)
    filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    have hb := (fordScaleDepth_log_bounds hy).2
    have hlog : 0 ≤ Real.log (y : ℝ) := by
      exact (fordScaleDepth_log_bounds hy).1.trans' (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ fordScaleDepth M y)]
    simpa only [c, mul_assoc] using hb
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    have hb := (fordScaleDepth_log_bounds hy).1
    have hlog : 0 ≤ Real.log (y : ℝ) := hb.trans' (by positivity)
    rw [Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ fordScaleDepth M y),
      Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hc).2
    simpa only [c, mul_comm] using hb

theorem log_log_nat_isTheta_fordScaleDepth (M : ℕ) :
    (fun y : ℕ ↦ Real.log (Real.log (y : ℝ))) =Θ[atTop]
      (fun y : ℕ ↦ (fordScaleDepth M y : ℝ)) := by
  let c := fordScaleConstant M
  let U := |Real.log (2 * c)| + Real.log 2
  let D := 2 / Real.log 2
  have hc : 0 < c := fordScaleConstant_pos M
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hlarge : ∀ᶠ y : ℕ in atTop,
      fordConstructionScale M 1 ≤ y ∧
      1 ≤ (fordScaleDepth M y : ℝ) ∧
      2 * |Real.log c| / Real.log 2 ≤ (fordScaleDepth M y : ℝ) := by
    filter_upwards [eventually_ge_atTop (fordConstructionScale M 1),
      (tendsto_fordScaleDepth_cast_atTop M).eventually
        (eventually_ge_atTop (1 : ℝ)),
      (tendsto_fordScaleDepth_cast_atTop M).eventually
        (eventually_ge_atTop (2 * |Real.log c| / Real.log 2))]
      with y hy hK1 hKlarge
    exact ⟨hy, hK1, hKlarge⟩
  have hcompare : ∀ᶠ y : ℕ in atTop,
      (Real.log 2 / 2) * (fordScaleDepth M y : ℝ) ≤
          Real.log (Real.log (y : ℝ)) ∧
        Real.log (Real.log (y : ℝ)) ≤
          U * (fordScaleDepth M y : ℝ) := by
    filter_upwards [hlarge] with y hy
    let K := fordScaleDepth M y
    have hb := fordScaleDepth_log_bounds hy.1
    have hlowPos : 0 < c * (2 : ℝ) ^ K := by positivity
    have hlogPos : 0 < Real.log (y : ℝ) := hlowPos.trans_le hb.1
    have hlowLog := Real.log_le_log hlowPos hb.1
    have hupLog := Real.log_le_log hlogPos hb.2
    have hlowFormula : Real.log (c * (2 : ℝ) ^ K) =
        Real.log c + (K : ℝ) * Real.log 2 := by
      rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]
    have hupFormula : Real.log (2 * c * (2 : ℝ) ^ K) =
        Real.log (2 * c) + (K : ℝ) * Real.log 2 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [hlowFormula] at hlowLog
    rw [hupFormula] at hupLog
    constructor
    · have habs : |Real.log c| ≤
          (Real.log 2 / 2) * (K : ℝ) := by
        have hlarge' := (div_le_iff₀ (Real.log_pos one_lt_two)).mp hy.2.2
        dsimp [K] at hlarge' ⊢
        nlinarith
      calc
        (Real.log 2 / 2) * (K : ℝ) ≤
            Real.log c + (K : ℝ) * Real.log 2 := by
          linarith [neg_abs_le (Real.log c)]
        _ ≤ Real.log (Real.log (y : ℝ)) := hlowLog
    · calc
        Real.log (Real.log (y : ℝ)) ≤
            Real.log (2 * c) + (K : ℝ) * Real.log 2 := hupLog
        _ ≤ U * (K : ℝ) := by
          have hlogAbs := le_abs_self (Real.log (2 * c))
          have hlogAbsNonneg := abs_nonneg (Real.log (2 * c))
          dsimp [U]
          nlinarith [hy.2.1]
  constructor
  · apply Asymptotics.IsBigO.of_bound U
    filter_upwards [hcompare] with y hy
    have hloglog : 0 ≤ Real.log (Real.log (y : ℝ)) :=
      (by positivity : 0 ≤ (Real.log 2 / 2) *
        (fordScaleDepth M y : ℝ)).trans hy.1
    rw [Real.norm_eq_abs, abs_of_nonneg hloglog, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact hy.2
  · apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hcompare] with y hy
    have hloglog : 0 ≤ Real.log (Real.log (y : ℝ)) :=
      (by positivity : 0 ≤ (Real.log 2 / 2) *
        (fordScaleDepth M y : ℝ)).trans hy.1
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hloglog]
    dsimp [D]
    calc
      (fordScaleDepth M y : ℝ) =
          (2 / Real.log 2) *
            ((Real.log 2 / 2) * (fordScaleDepth M y : ℝ)) := by
        field_simp [ne_of_gt (Real.log_pos one_lt_two)]
      _ ≤ (2 / Real.log 2) * Real.log (Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hy.1 (by positivity)

end Erdos446
