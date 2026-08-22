/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZQuarterCutCentralTail
import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition

/-!
# Central shell-zero tail for one oriented spatial source

After normalizing a raw site to its tiling base, the all-six source routing
has four canonical/opposite-by-orientation classes.  Its uniform literal
source cut is therefore `initialBudget48 m / 8`.  This file proves that the
corresponding exact-count central tail still has positive logarithmic-square
decay.
-/

open Filter
open scoped ENNReal

namespace Erdos1165.HLOZOrientedSourceCentralTail

open HLOZProposition48Candidates HLOZQuarterCutCentralTail
open HLOZShellZeroCentralTail HLOZShellZeroReplacementProduct
open HLOZShellZeroReplacementNumerics
open TilingOrientedShellZeroSourcePartition

noncomputable section

lemma initialBudget48_lt_eight_mul_orientedSourceCut48_add_one (m : ℕ) :
    initialBudget48 m < 8 * (orientedSourceCut48 m + 1) := by
  unfold orientedSourceCut48
  omega

lemma log_sq_le_eight_mul_orientedSourceCut48_add_one (m : ℕ) :
    Real.log (m : ℝ) ^ 2 ≤
      8 * ((orientedSourceCut48 m + 1 : ℕ) : ℝ) := by
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) := Nat.le_ceil _
  have hnat := initialBudget48_lt_eight_mul_orientedSourceCut48_add_one m
  unfold initialBudget48 at hnat
  have hcast : ((Nat.ceil (Real.log (m : ℝ) ^ 2) : ℕ) : ℝ) ≤
      8 * ((orientedSourceCut48 m + 1 : ℕ) : ℝ) := by
    exact_mod_cast
      (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ 1) hnat))
  exact hceil.trans hcast

/-- Positive rate retained after the four oriented spatial source classes. -/
def orientedSourceCentralTailRate (C : ℝ) : ℝ :=
  fixedReplacementRate C / 16

lemma orientedSourceCentralTailRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < orientedSourceCentralTailRate C := by
  unfold orientedSourceCentralTailRate
  positivity [fixedReplacementRate_pos hC]

/-- The concrete all-tiling oriented cut retains logarithmic-square decay. -/
theorem eventually_centralReplacementTailCost_orientedSourceCut48_le_exp
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      centralReplacementTailCost C (orientedSourceCut48 m) ≤
        ENNReal.ofReal (Real.exp
          (-orientedSourceCentralTailRate C * Real.log (m : ℝ) ^ 2)) := by
  let A := centralTailPrefactor C
  let R := fixedReplacementRate C
  have hA : 0 < A := centralTailPrefactor_pos hC
  have hR : 0 < R := fixedReplacementRate_pos hC.le
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in atTop,
      max 1 (16 * Real.log A / R) ≤ Real.log (m : ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with m hm
  have hlogA : Real.log A ≤
      R / 16 * Real.log (m : ℝ) ^ 2 := by
    have hone : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hm
    have hthreshold : 16 * Real.log A / R ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hm
    have hsq : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ) - 1)]
    have hmul : 16 * Real.log A ≤ R * Real.log (m : ℝ) := by
      rw [div_le_iff₀ hR] at hthreshold
      simpa only [mul_comm] using hthreshold
    nlinarith
  have hAexp : A ≤ Real.exp
      (R / 16 * Real.log (m : ℝ) ^ 2) := by
    rw [show A = Real.exp (Real.log A) by rw [Real.exp_log hA]]
    exact Real.exp_le_exp.mpr hlogA
  have hpow : replacementBase C ^ (orientedSourceCut48 m + 1) ≤
      Real.exp (-(R / 8) * Real.log (m : ℝ) ^ 2) := by
    rw [replacementBase_pow_eq_exp hC.le]
    apply Real.exp_le_exp.mpr
    have hcut := log_sq_le_eight_mul_orientedSourceCut48_add_one m
    nlinarith
  have hreal : A * replacementBase C ^ (orientedSourceCut48 m + 1) ≤
      Real.exp (-orientedSourceCentralTailRate C *
        Real.log (m : ℝ) ^ 2) := by
    calc
      A * replacementBase C ^ (orientedSourceCut48 m + 1) ≤
          Real.exp (R / 16 * Real.log (m : ℝ) ^ 2) *
            Real.exp (-(R / 8) * Real.log (m : ℝ) ^ 2) := by
        exact mul_le_mul hAexp hpow
          (pow_nonneg (replacementBase_nonneg hC.le) _)
          (Real.exp_pos _).le
      _ = Real.exp (-orientedSourceCentralTailRate C *
          Real.log (m : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        unfold orientedSourceCentralTailRate R
        congr 1
        ring
  calc
    centralReplacementTailCost C (orientedSourceCut48 m) ≤
        centralReplacementTailMajorant C (orientedSourceCut48 m) :=
      centralReplacementTailCost_le_majorant hC _
    _ = ENNReal.ofReal
        (A * replacementBase C ^ (orientedSourceCut48 m + 1)) := by
      exact centralReplacementTailMajorant_eq_ofReal_prefactor_mul_pow hC _
    _ ≤ ENNReal.ofReal (Real.exp
        (-orientedSourceCentralTailRate C * Real.log (m : ℝ) ^ 2)) :=
      ENNReal.ofReal_mono hreal

end

end Erdos1165.HLOZOrientedSourceCentralTail
