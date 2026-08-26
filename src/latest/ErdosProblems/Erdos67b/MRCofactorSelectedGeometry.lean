import ErdosProblems.Erdos67b.MRCofactorRectangleRounding
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rounded geometry for fixed-power selected cofactors

The selected-factor cutoff and the complementary lower scale fit below
every actual rectangle prefix. All products and divisions retain their
natural-number rounding.
-/

namespace Erdos67b

noncomputable section

def mrSelectedCofactorLowerScale (X : ℕ) : ℕ := ⌈Real.sqrt (X : ℝ)⌉₊

def mrSelectedCofactorFactorCutoff (tau b : ℝ) : ℕ := ⌈Real.exp (tau * b)⌉₊

theorem mrSelectedCofactorLowerScale_pos {X : ℕ} (hX : 0 < X) :
    0 < mrSelectedCofactorLowerScale X := by
  apply Nat.ceil_pos.mpr
  exact Real.sqrt_pos.mpr (by exact_mod_cast hX)

theorem mrSelectedCofactorLowerScale_le {X : ℕ} (hX : 1 ≤ X) :
    mrSelectedCofactorLowerScale X ≤ X := by
  apply Nat.ceil_le.mpr
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hs := Real.sq_sqrt (Nat.cast_nonneg X)
  have hn := Real.sqrt_nonneg (X : ℝ)
  nlinarith

theorem mrSelectedCofactorLowerScale_ge {X Y₀ : ℕ} (hX : Y₀ ^ 2 ≤ X) :
    Y₀ ≤ mrSelectedCofactorLowerScale X := by
  have hh : (Y₀ : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2
    exact_mod_cast hX
  exact_mod_cast hh.trans (Nat.le_ceil _)

theorem mrSelectedCofactorLowerScale_log {X : ℕ} (hX : 0 < X) :
    Real.log (X : ℝ) ≤ 2 * Real.log (mrSelectedCofactorLowerScale X : ℝ) := by
  have hh := Real.log_le_log
    (Real.sqrt_pos.mpr (show (0 : ℝ) < X by exact_mod_cast hX))
    (Nat.le_ceil (Real.sqrt (X : ℝ)))
  rw [Real.log_sqrt (Nat.cast_nonneg X)] at hh
  change Real.log (X : ℝ) ≤ 2 * Real.log (⌈Real.sqrt (X : ℝ)⌉₊ : ℝ)
  linarith

theorem mrSelectedCofactorFactorCutoff_pos (tau b : ℝ) :
    0 < mrSelectedCofactorFactorCutoff tau b := Nat.ceil_pos.mpr (Real.exp_pos _)

theorem mrSelectedCofactor_cutoffs_mul_upper_le {X Q : ℕ} (hX : 0 < X)
    {tau b : ℝ} (htau : 0 ≤ tau) (hb : 0 ≤ b)
    (hlog : 16 ≤ Real.log (X : ℝ))
    (hbudget : (tau + 1) * b ≤ Real.log (X : ℝ) / 4)
    (hQ : (Q : ℝ) ≤ Real.exp (b + 1)) :
    mrSelectedCofactorFactorCutoff tau b * mrSelectedCofactorLowerScale X * Q ≤ X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hSone : 1 ≤ Real.sqrt (X : ℝ) := by
    simpa using Real.sqrt_le_sqrt hXone
  have hS : Real.sqrt (X : ℝ) = Real.exp (Real.log (X : ℝ) / 2) := by
    rw [← Real.log_sqrt (Nat.cast_nonneg X), Real.exp_log (Real.sqrt_pos.mpr hXR)]
  have hY : (mrSelectedCofactorLowerScale X : ℝ) ≤ 2 * Real.sqrt (X : ℝ) :=
    Nat.ceil_le_two_mul (by linarith)
  have hEone : 1 ≤ Real.exp (tau * b) := Real.one_le_exp (mul_nonneg htau hb)
  have hK : (mrSelectedCofactorFactorCutoff tau b : ℝ) ≤ 2 * Real.exp (tau * b) :=
    Nat.ceil_le_two_mul (by linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hreal : (mrSelectedCofactorFactorCutoff tau b : ℝ) *
      mrSelectedCofactorLowerScale X * Q ≤ (X : ℝ) := by
    calc
      _ ≤ (2 * Real.exp (tau * b)) * (2 * Real.sqrt (X : ℝ)) *
          Real.exp (b + 1) := by gcongr
      _ = 4 * Real.exp (tau * b + Real.log (X : ℝ) / 2 + (b + 1)) := by
        simp only [Real.exp_add, ← hS]
        ring
      _ = Real.exp (Real.log 4 + (tau * b + Real.log (X : ℝ) / 2 + (b + 1))) := by
        rw [Real.exp_add (Real.log 4), Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ Real.exp (Real.log (X : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = X := Real.exp_log hXR
  exact_mod_cast hreal

theorem mrSelectedCofactor_cutoffs_le_rectangle_lower {X Q : ℕ} (hX : 0 < X)
    (hQpos : 0 < Q) {tau b : ℝ} (htau : 0 ≤ tau) (hb : 0 ≤ b)
    (hlog : 16 ≤ Real.log (X : ℝ))
    (hbudget : (tau + 1) * b ≤ Real.log (X : ℝ) / 4)
    (hQ : (Q : ℝ) ≤ Real.exp (b + 1)) :
    mrSelectedCofactorFactorCutoff tau b * mrSelectedCofactorLowerScale X ≤ X / Q :=
  (Nat.le_div_iff_mul_le hQpos).2
    (mrSelectedCofactor_cutoffs_mul_upper_le hX htau hb hlog hbudget hQ)

end

end Erdos67b
