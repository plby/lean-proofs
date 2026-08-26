import ErdosProblems.Erdos69.FiniteExpectation
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def fourierPhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem fourierPhase_zero : fourierPhase 0 = 1 := by
  simp [fourierPhase]

@[simp] theorem norm_fourierPhase (x : ℝ) : ‖fourierPhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem fourierPhase_add (x y : ℝ) :
    fourierPhase (x + y) = fourierPhase x * fourierPhase y := by
  simp [fourierPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierPhase_sub_mul (x y : ℝ) :
    fourierPhase (x - y) * fourierPhase y = fourierPhase x := by
  rw [← fourierPhase_add, sub_add_cancel]

theorem norm_fourierPhase_sub_one_le (x : ℝ) :
    ‖fourierPhase x - 1‖ ≤ 2 * Real.pi * |x| := by
  unfold fourierPhase
  rw [mul_comm ((2 * Real.pi * x : ℝ) : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |Real.sin (2 * Real.pi * x / 2)| ≤ 2 * |2 * Real.pi * x / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2 * Real.pi * |x| := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      ring

theorem norm_fourierPhase_sub_le (x y : ℝ) :
    ‖fourierPhase x - fourierPhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : fourierPhase x - fourierPhase y =
      (fourierPhase (x - y) - 1) * fourierPhase y := by
    rw [sub_mul, fourierPhase_sub_mul, one_mul]
  rw [heq, norm_mul, norm_fourierPhase, mul_one]
  exact norm_fourierPhase_sub_one_le (x - y)

@[simp] theorem fourierPhase_intCast (z : ℤ) : fourierPhase (z : ℝ) = 1 := by
  unfold fourierPhase
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  congr 1
  push_cast
  ring

theorem fourierPhase_add_intCast (x : ℝ) (z : ℤ) :
    fourierPhase (x + z) = fourierPhase x := by
  rw [fourierPhase_add, fourierPhase_intCast, mul_one]

theorem fourierPhase_neg (x : ℝ) : fourierPhase (-x) = star (fourierPhase x) := by
  unfold fourierPhase
  change Complex.exp ((2 * Real.pi * -x : ℝ) * Complex.I) =
    (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_ofNat, map_ofNat]
  ring

theorem fourierPhase_sub (x y : ℝ) :
    fourierPhase (x - y) = fourierPhase x * star (fourierPhase y) := by
  rw [sub_eq_add_neg, fourierPhase_add, fourierPhase_neg]

theorem fourierPhase_sub_realPart (x y : ℝ) :
    (fourierPhase (x - y)).re =
      (fourierPhase x).re * (fourierPhase y).re +
        (fourierPhase x).im * (fourierPhase y).im := by
  rw [fourierPhase_sub, Complex.mul_re]
  simp

theorem fourierPhase_realPart (x : ℝ) :
    (fourierPhase x).re = Real.cos (2 * Real.pi * x) := by
  simp only [fourierPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem fourierPhase_realPart_le_one (x : ℝ) : (fourierPhase x).re ≤ 1 := by
  rw [fourierPhase_realPart]
  exact Real.cos_le_one _

noncomputable def phaseDeficit (x y : ℝ) : ℝ := 1 - (fourierPhase (x - y)).re

theorem phaseDeficit_nonneg (x y : ℝ) : 0 ≤ phaseDeficit x y :=
  sub_nonneg.mpr (fourierPhase_realPart_le_one _)

theorem phaseDeficit_symm (x y : ℝ) : phaseDeficit x y = phaseDeficit y x := by
  simp only [phaseDeficit, fourierPhase_sub_realPart]
  ring

theorem fourierPhase_deficit_lower {x : ℝ} (hx : |x| ≤ 1 / 2) :
    8 * x ^ 2 ≤ 1 - (fourierPhase x).re := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hnorm : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hnorm] at hsin
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |x|) hsin 2
  simp only [mul_pow, sq_abs] at hsquare
  rw [fourierPhase_realPart, show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
    Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem norm_mean_fourierPhase_le_one (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ≤ 1 := by
  simpa only [norm_fourierPhase, μ.mean_const] using
    μ.norm_complexMean_le (fun x ↦ fourierPhase (X x))

theorem norm_mean_fourierPhase_sub_le (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      μ.complexMean (fun x ↦ fourierPhase (Y x))‖ ≤
        (2 * Real.pi) * μ.mean (fun x ↦ |X x - Y x|) := by
  calc
    _ ≤ μ.mean (fun x ↦ ‖fourierPhase (X x) - fourierPhase (Y x)‖) :=
      μ.norm_complexMean_sub_le _ _
    _ ≤ μ.mean (fun x ↦ (2 * Real.pi) * |X x - Y x|) :=
      μ.mean_mono (fun x ↦ norm_fourierPhase_sub_le _ _)
    _ = _ := μ.mean_const_mul _ _

end FiniteLaw

end Erdos69.Elementary
