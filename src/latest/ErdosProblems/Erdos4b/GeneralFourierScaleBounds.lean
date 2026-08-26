/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineEnvelope
import ErdosProblems.Erdos4b.GeneralFourierProfileAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit scales for the affine Fourier comparison

A quarter-power exponent bound works on the square-root Fourier box
whenever each logarithmic divisor scale is at least twice the
three-quarter power of the ambient logarithmic size.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

def fourierQuarterExponent (V : ℝ) : ℝ := (V + 1) ^ (-(1 / 4 : ℝ))

theorem eventually_two_mul_log_add_one_le
    {α : Type*} {l : Filter α} {V : α → ℝ} (hV : Tendsto V l atTop) :
    ∀ᶠ a in l, 2 * Real.log (V a + 1) ≤ V a := by
  have hplus : Tendsto (fun a ↦ V a + 1) l atTop :=
    hV.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlog := hplus.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hlog, hV.eventually_ge_atTop 1] with a ha hVa
  have hpos : 0 < V a + 1 := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hpos] at ha
  have h := le_abs_self (Real.log (V a + 1))
  linarith

theorem eventually_log_primorial_le_ambient
    {α : Type*} {l : Filter α} (w : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1)) :
    ∀ᶠ a in l, Real.log (primorial (w a)) ≤ V a := by
  filter_upwards [hw.eventually eventually_log_primorial_lt_two_mul,
    eventually_two_mul_log_add_one_le hV, hcutoff] with a hP hlog hwV
  linarith

theorem fourierQuarterExponent_nonneg {V : ℝ} (hV : -1 ≤ V) :
    0 ≤ fourierQuarterExponent V := Real.rpow_nonneg (by linarith) _

theorem tendsto_fourierQuarterExponent_zero
    {α : Type*} {l : Filter α} {V : α → ℝ} (hV : Tendsto V l atTop) :
    Tendsto (fun a ↦ fourierQuarterExponent (V a)) l (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    (hV.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))

theorem tendsto_fourierQuarterExponent_mul_log_zero
    {α : Type*} {l : Filter α} {V : α → ℝ} (hV : Tendsto V l atTop) :
    Tendsto (fun a ↦ fourierQuarterExponent (V a) * Real.log (V a + 1)) l (𝓝 0) := by
  have hplus : Tendsto (fun a ↦ V a + 1) l atTop :=
    hV.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have h := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hplus
  apply h.congr'
  filter_upwards [hV.eventually_ge_atTop 0] with a ha
  simp only [Function.comp_def, fourierQuarterExponent, Real.rpow_neg (by linarith : 0 ≤ V a + 1),
    div_eq_mul_inv, mul_comm]

theorem fourierScale_pos_of_threeQuarter_bound {V L : ℝ}
    (hV : 1 ≤ V) (hL : 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ L) : 0 < L := by
  have hpow := Real.rpow_pos_of_pos (by linarith : 0 < V + 1) (3 / 4 : ℝ)
  linarith

theorem sqrt_box_scale_le_fourierQuarterExponent {V L : ℝ}
    (hV : 1 ≤ V) (hL : 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ L) :
    (1 + Real.sqrt V) / L ≤ fourierQuarterExponent V := by
  have hpos : 0 < V + 1 := by linarith
  have hσ : 0 ≤ fourierQuarterExponent V := fourierQuarterExponent_nonneg (by linarith)
  have hsqrt : 1 ≤ Real.sqrt (V + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hsqrtV : Real.sqrt V ≤ Real.sqrt (V + 1) := Real.sqrt_le_sqrt (by linarith)
  have hid : fourierQuarterExponent V * (2 * (V + 1) ^ (3 / 4 : ℝ)) =
      2 * Real.sqrt (V + 1) := by
    rw [fourierQuarterExponent, Real.sqrt_eq_rpow]
    rw [mul_left_comm, ← Real.rpow_add hpos]
    norm_num
  apply (div_le_iff₀ (fourierScale_pos_of_threeQuarter_bound hV hL)).mpr
  calc
    1 + Real.sqrt V ≤ 2 * Real.sqrt (V + 1) := by linarith
    _ = fourierQuarterExponent V * (2 * (V + 1) ^ (3 / 4 : ℝ)) := hid.symm
    _ ≤ fourierQuarterExponent V * L := mul_le_mul_of_nonneg_left hL hσ

end

end Erdos4b
