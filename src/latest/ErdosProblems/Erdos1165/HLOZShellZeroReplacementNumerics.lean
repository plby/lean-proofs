/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementProduct

/-!
# Fixed-ratio numerics for the shell-zero replacement product

For every fixed finite local-ratio constant `C ≥ 0`, the exact replacement
base

`(1 + C / (1 + C)) / 2`

lies strictly between zero and one.  Consequently its power at the HLOZ
initial budget is summable, even when `C` is much larger than the canonical
`4 / 3` specialization.
-/

open scoped ENNReal

namespace Erdos1165.HLOZShellZeroReplacementNumerics

open HLOZProposition48Candidates HLOZShellZeroReplacementProduct

noncomputable section

lemma replacementBase_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < replacementBase C := by
  unfold replacementBase
  have hden : 0 < 1 + C := by linarith
  have hfrac : 0 ≤ C / (1 + C) := div_nonneg hC hden.le
  linarith

lemma replacementBase_lt_one {C : ℝ} (hC : 0 ≤ C) :
    replacementBase C < 1 := by
  unfold replacementBase
  have hden : 0 < 1 + C := by linarith
  have hfrac : C / (1 + C) < 1 :=
    (div_lt_one₀ hden).2 (by linarith)
  linarith

/-- The positive exponential rate corresponding to a fixed replacement
ratio constant. -/
noncomputable def fixedReplacementRate (C : ℝ) : ℝ :=
  -Real.log (replacementBase C)

lemma fixedReplacementRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < fixedReplacementRate C := by
  unfold fixedReplacementRate
  exact neg_pos.mpr
    (Real.log_neg (replacementBase_pos hC) (replacementBase_lt_one hC))

lemma replacementBase_pow_eq_exp {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    replacementBase C ^ n =
      Real.exp (-fixedReplacementRate C * (n : ℝ)) := by
  have hpos := replacementBase_pos hC
  rw [show replacementBase C = Real.exp (Real.log (replacementBase C)) by
    rw [Real.exp_log hpos]]
  rw [← Real.exp_nat_mul]
  congr 1
  unfold fixedReplacementRate
  ring

/-- Real-valued fixed-ratio replacement cost at the HLOZ initial budget. -/
noncomputable def fixedReplacementRealCost (C : ℝ) (m : ℕ) : ℝ :=
  replacementBase C ^ (initialBudget48 m + 1)

lemma fixedReplacementRealCost_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ fixedReplacementRealCost C m := by
  unfold fixedReplacementRealCost
  exact pow_nonneg (replacementBase_nonneg hC) _

/-- A fixed local-ratio constant changes only the positive rate multiplying
`log(m)^2`. -/
theorem fixedReplacementRealCost_le_exp_neg_log_sq
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    fixedReplacementRealCost C m ≤
      Real.exp
        (-fixedReplacementRate C * Real.log (m : ℝ) ^ 2) := by
  rw [fixedReplacementRealCost, replacementBase_pow_eq_exp hC]
  rw [Real.exp_le_exp]
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) :=
    Nat.le_ceil (Real.log (m : ℝ) ^ 2)
  have hbudget : Real.log (m : ℝ) ^ 2 ≤
      ((initialBudget48 m + 1 : ℕ) : ℝ) := by
    unfold initialBudget48
    push_cast
    linarith
  nlinarith [fixedReplacementRate_pos hC]

/-- For every fixed finite nonnegative `C`, the real replacement costs are
summable. -/
theorem summable_fixedReplacementRealCost {C : ℝ} (hC : 0 ≤ C) :
    Summable (fixedReplacementRealCost C) := by
  let r := fixedReplacementRate C
  have hr : 0 < r := fixedReplacementRate_pos hC
  have hlog : Filter.Tendsto
      (fun m : ℕ ↦ Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have htarget : Summable
      (fun m : ℕ ↦ Real.exp (-r * Real.log (m : ℝ) ^ 2)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hlarge : ∀ᶠ m : ℕ in Filter.cofinite,
        2 / r ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (Filter.eventually_ge_atTop (2 / r))
    have hmpos : ∀ᶠ m : ℕ in Filter.cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using
        (Filter.eventually_gt_atTop 0)
    filter_upwards [hlarge, hmpos] with m hlogm hmpos
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -r * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hrMul : 2 ≤ r * Real.log (m : ℝ) := by
        calc
          2 = r * (2 / r) := by field_simp
          _ ≤ r * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hr.le
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
    exact Real.exp_le_exp.mpr hexponent
  apply Summable.of_nonneg_of_le
    (fun m ↦ fixedReplacementRealCost_nonneg hC m)
    (fun m ↦ fixedReplacementRealCost_le_exp_neg_log_sq hC m)
    htarget

/-- Exact ENNReal coefficient consumed by the global replacement
certificate for an arbitrary fixed local-ratio constant. -/
noncomputable def fixedReplacementCost (C : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (replacementBase C ^ (initialBudget48 m + 1))

theorem fixedReplacementCost_le_exp_neg_log_sq
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    fixedReplacementCost C m ≤
      ENNReal.ofReal
        (Real.exp
          (-fixedReplacementRate C * Real.log (m : ℝ) ^ 2)) := by
  apply ENNReal.ofReal_mono
  exact fixedReplacementRealCost_le_exp_neg_log_sq hC m

/-- The exact generic ENNReal replacement coefficient has finite total
mass. -/
theorem tsum_fixedReplacementCost_ne_top {C : ℝ} (hC : 0 ≤ C) :
    ∑' m, fixedReplacementCost C m ≠ ∞ := by
  let f : ℕ → NNReal := fun m ↦
    ⟨fixedReplacementRealCost C m,
      fixedReplacementRealCost_nonneg hC m⟩
  have hf : Summable (fun m : ℕ ↦ ((f m : NNReal) : ℝ)) := by
    change Summable (fixedReplacementRealCost C)
    exact summable_fixedReplacementRealCost hC
  have hsum : ∑' m, ((f m : NNReal) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hf
  have hcoe : ∀ m, ((f m : NNReal) : ℝ≥0∞) =
      fixedReplacementCost C m := by
    intro m
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← tsum_congr hcoe]
  exact hsum

end

end Erdos1165.HLOZShellZeroReplacementNumerics
