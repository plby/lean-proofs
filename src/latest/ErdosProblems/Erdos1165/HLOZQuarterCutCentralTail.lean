/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroCentralTail

/-!
# Central shell-zero tail after the spatial parity split

The raw first-shell budget remains `initialBudget48 m`.  The deterministic
factor-two spatial-source decomposition only guarantees that one of its two
source families exceeds one quarter of that budget.  This file proves that
the exact-count central tail beginning at that reduced cut still has a
positive logarithmic-square rate.
-/

open Filter
open scoped ENNReal

namespace Erdos1165.HLOZQuarterCutCentralTail

open HLOZProposition48Candidates HLOZShellZeroCentralTail
open HLOZShellZeroReplacementProduct
open HLOZShellZeroReplacementNumerics

noncomputable section

/-- The exact-count cut used after the canonical/opposite spatial split. -/
def sourceCut48 (m : ℕ) : ℕ := initialBudget48 m / 4

lemma initialBudget48_lt_four_mul_sourceCut48_add_one (m : ℕ) :
    initialBudget48 m < 4 * (sourceCut48 m + 1) := by
  unfold sourceCut48
  omega

lemma log_sq_le_four_mul_sourceCut48_add_one (m : ℕ) :
    Real.log (m : ℝ) ^ 2 ≤ 4 * ((sourceCut48 m + 1 : ℕ) : ℝ) := by
  have hceil : Real.log (m : ℝ) ^ 2 ≤
      (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) := Nat.le_ceil _
  have hnat := initialBudget48_lt_four_mul_sourceCut48_add_one m
  unfold initialBudget48 at hnat
  have hcast : ((Nat.ceil (Real.log (m : ℝ) ^ 2) : ℕ) : ℝ) ≤
      4 * ((sourceCut48 m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ 1) hnat))
  exact hceil.trans hcast

lemma centralReplacementTailMajorant_eq_ofReal_prefactor_mul_pow
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementTailMajorant C cut =
      ENNReal.ofReal
        (centralTailPrefactor C * replacementBase C ^ (cut + 1)) := by
  have hb0 : 0 ≤ replacementBase C := replacementBase_nonneg hC.le
  have hb1 : replacementBase C < 1 := replacementBase_lt_one hC.le
  rw [ENNReal.ofReal_mul (centralTailPrefactor_pos hC).le]
  unfold centralReplacementTailMajorant centralTailPrefactor
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hb1),
    ENNReal.ofReal_sub 1 hb0, ENNReal.ofReal_one,
    ENNReal.ofReal_pow hb0]
  simp only [div_eq_mul_inv]
  ring

lemma centralReplacementTailCost_ne_top_at_cut
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementTailCost C cut ≠ ∞ := by
  have hmajorant : centralReplacementTailMajorant C cut ≠ ∞ := by
    rw [centralReplacementTailMajorant_eq_ofReal_prefactor_mul_pow hC]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hmajorant
    (centralReplacementTailCost_le_majorant hC cut)

/-- Positive rate retained by the quarter-cut tail after absorbing its fixed
prefactor. -/
def quarterCutCentralTailRate (C : ℝ) : ℝ := fixedReplacementRate C / 8

lemma quarterCutCentralTailRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < quarterCutCentralTailRate C := by
  unfold quarterCutCentralTailRate
  positivity [fixedReplacementRate_pos hC]

/-- The reduced exact-count tail still has logarithmic-square decay. -/
theorem eventually_centralReplacementTailCost_sourceCut48_le_exp_neg_log_sq
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      centralReplacementTailCost C (sourceCut48 m) ≤
        ENNReal.ofReal (Real.exp
          (-quarterCutCentralTailRate C * Real.log (m : ℝ) ^ 2)) := by
  let A := centralTailPrefactor C
  let R := fixedReplacementRate C
  have hA : 0 < A := centralTailPrefactor_pos hC
  have hR : 0 < R := fixedReplacementRate_pos hC.le
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in atTop,
      max 1 (8 * Real.log A / R) ≤ Real.log (m : ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with m hm
  have hlogA : Real.log A ≤
      R / 8 * Real.log (m : ℝ) ^ 2 := by
    have hone : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hm
    have hthreshold : 8 * Real.log A / R ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hm
    have hsq : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ) - 1)]
    have hmul : 8 * Real.log A ≤ R * Real.log (m : ℝ) := by
      rw [div_le_iff₀ hR] at hthreshold
      simpa only [mul_comm] using hthreshold
    nlinarith
  have hAexp : A ≤ Real.exp
      (R / 8 * Real.log (m : ℝ) ^ 2) := by
    rw [show A = Real.exp (Real.log A) by rw [Real.exp_log hA]]
    exact Real.exp_le_exp.mpr hlogA
  have hpow : replacementBase C ^ (sourceCut48 m + 1) ≤
      Real.exp (-(R / 4) * Real.log (m : ℝ) ^ 2) := by
    rw [replacementBase_pow_eq_exp hC.le]
    apply Real.exp_le_exp.mpr
    have hcut := log_sq_le_four_mul_sourceCut48_add_one m
    nlinarith
  have hreal : A * replacementBase C ^ (sourceCut48 m + 1) ≤
      Real.exp (-quarterCutCentralTailRate C *
        Real.log (m : ℝ) ^ 2) := by
    calc
      A * replacementBase C ^ (sourceCut48 m + 1) ≤
          Real.exp (R / 8 * Real.log (m : ℝ) ^ 2) *
            Real.exp (-(R / 4) * Real.log (m : ℝ) ^ 2) := by
        exact mul_le_mul hAexp hpow
          (pow_nonneg (replacementBase_nonneg hC.le) _)
          (Real.exp_pos _).le
      _ = Real.exp (-quarterCutCentralTailRate C *
          Real.log (m : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        unfold quarterCutCentralTailRate R
        congr 1
        ring
  calc
    centralReplacementTailCost C (sourceCut48 m) ≤
        centralReplacementTailMajorant C (sourceCut48 m) :=
      centralReplacementTailCost_le_majorant hC _
    _ = ENNReal.ofReal
        (A * replacementBase C ^ (sourceCut48 m + 1)) := by
      exact centralReplacementTailMajorant_eq_ofReal_prefactor_mul_pow hC _
    _ ≤ ENNReal.ofReal (Real.exp
        (-quarterCutCentralTailRate C * Real.log (m : ℝ) ^ 2)) :=
      ENNReal.ofReal_mono hreal

end

end Erdos1165.HLOZQuarterCutCentralTail
