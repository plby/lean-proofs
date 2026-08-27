/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SmoothRankin
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A full-ray Euler-product bound for the complete smooth-number exception -/

namespace Erdos4b.FGKMT

noncomputable section

theorem harmonic_rankinSplitPoint_le {L δ : ℝ} (hL : 1 ≤ L)
    (hℓ : 1 ≤ Real.log L) (hδ : 0 < δ) (hinv : δ⁻¹ ≤ L) :
    (harmonic (SmoothRankin.rankinSplitPoint δ) : ℝ) ≤ 3 * Real.log L := by
  have hLpos : 0 < L := by linarith
  have hRpos : (0 : ℝ) < SmoothRankin.rankinSplitPoint δ :=
    (inv_pos.mpr hδ).trans_le (Nat.le_ceil _)
  have hR : (SmoothRankin.rankinSplitPoint δ : ℝ) ≤ 2 * L := by
    have hh := Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)
    change (SmoothRankin.rankinSplitPoint δ : ℝ) < δ⁻¹ + 1 at hh
    linarith
  have hlogR := Real.log_le_log hRpos hR
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at hlogR
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hh := harmonic_le_one_add_log (SmoothRankin.rankinSplitPoint δ)
  linarith

theorem smoothRankin_dyadic_tail_le {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {Z : ℕ} (hZ : 0 < Z) :
    ((2 : ℝ) ^ δ) ^ (Nat.log 2 Z + 2) ≤ 2 * (Z : ℝ) ^ δ := by
  have hpower : (2 : ℝ) ^ Nat.log 2 Z ≤ (Z : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hZ.ne'
  have hfirst : ((2 : ℝ) ^ δ) ^ Nat.log 2 Z ≤ (Z : ℝ) ^ δ := by
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow (by positivity) hpower hδ.le
  have hlast : ((2 : ℝ) ^ δ) ^ 2 ≤ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (2 : ℝ) ^ (δ * (2 : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  rw [pow_add]
  calc
    _ ≤ (Z : ℝ) ^ δ * 2 :=
      mul_le_mul hfirst hlast (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := mul_comm _ _

def smoothEulerLogConstant (C : ℝ) : ℝ :=
  Erdos469.rankinEulerConstant * (2 * C / Real.log 2) * (12 + 2 / Real.log 2)

theorem smoothEulerLogConstant_pos {C : ℝ} (hC : 0 < C) :
    0 < smoothEulerLogConstant C := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos (mul_pos Erdos469.rankinEulerConstant_pos (by positivity)) (by positivity)

theorem smoothRankinEulerProduct_le_exp_loglog {C L δ : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t → (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hL : 1 ≤ L) (hℓ : 1 ≤ Real.log L) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hinv : δ⁻¹ ≤ L) {Z : ℕ} (hZ : 0 < Z) (hZpow : (Z : ℝ) ^ δ ≤ Real.log L) :
    Erdos469.smoothRankinEulerProduct δ Z ≤
      Real.exp (smoothEulerLogConstant C * Real.log L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := harmonic_rankinSplitPoint_le hL hℓ hδ hinv
  have ht := (smoothRankin_dyadic_tail_le hδ hδhalf hZ).trans
    (mul_le_mul_of_nonneg_left hZpow (by norm_num : (0 : ℝ) ≤ 2))
  have hbracket :
      4 * (harmonic (SmoothRankin.rankinSplitPoint δ) : ℝ) +
        ((2 : ℝ) ^ δ) ^ (Nat.log 2 Z + 2) / Real.log 2 ≤
      (12 + 2 / Real.log 2) * Real.log L := by
    calc
      _ ≤ 4 * (3 * Real.log L) + (2 * Real.log L) / Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4))
          (div_le_div_of_nonneg_right ht hlog2.le)
      _ = _ := by ring
  apply (SmoothRankin.smoothRankinEulerProduct_le_exp_dyadic_canonical
    hC hδ hδhalf hcheb Z).trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg Erdos469.rankinEulerConstant_pos.le (by positivity : 0 ≤ 2 * C / Real.log 2))
  simpa only [smoothEulerLogConstant, mul_assoc] using hmul

end

end Erdos4b.FGKMT
