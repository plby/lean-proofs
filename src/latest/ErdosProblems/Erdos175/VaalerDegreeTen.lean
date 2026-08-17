/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos175.Sawtooth

/-!
# An unconditional small Fourier majorant for the centered sawtooth

This file proves the pointwise analytic input needed in Section 7 of
Granville--Ramaré.  We use the order-three Vaaler polynomial and allow the
constant `13 / 80`, slightly larger than its optimal constant `1 / 8` but
still strictly smaller than `1 / 6`.  The slack makes the verification a
short, completely algebraic argument after the tangent half-angle
substitution.
-/

namespace Erdos175.VaalerDegreeTen

open scoped BigOperators

open Erdos175.Sawtooth

private lemma deriv_cubicPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3) y = 1 - y ^ 2 := by
  change deriv ((fun z : ℝ ↦ z) - (fun z : ℝ ↦ z ^ 3 / 3)) y = _
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 3).div_const 3).deriv
  change deriv (fun z : ℝ ↦ z ^ 3 / 3) y = _ at hpow
  rw [show deriv (fun z : ℝ ↦ z) y = 1 from congrFun deriv_id'' y, hpow]
  norm_num

private lemma deriv_quinticPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) y =
      1 - y ^ 2 + y ^ 4 := by
  change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3) +
    (fun z : ℝ ↦ z ^ 5 / 5)) y = _
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_cubicPartialSum]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 5).div_const 5).deriv
  change deriv (fun z : ℝ ↦ z ^ 5 / 5) y = _ at hpow
  rw [hpow]
  norm_num

private lemma deriv_septicPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7) y =
      1 - y ^ 2 + y ^ 4 - y ^ 6 := by
  change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) -
    (fun z : ℝ ↦ z ^ 7 / 7)) y = _
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_quinticPartialSum]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 7).div_const 7).deriv
  change deriv (fun z : ℝ ↦ z ^ 7 / 7) y = _ at hpow
  rw [hpow]
  norm_num

private lemma arctan_lower_cubic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun y ↦ Real.arctan y - (y - y ^ 3 / 3)
  have hf : Differentiable ℝ f := by
    exact Real.differentiable_arctan.sub (by fun_prop)
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 4 / (1 + y ^ 2) := by
      change deriv (Real.arctan - (fun z : ℝ ↦ z - z ^ 3 / 3)) y = _
      rw [deriv_sub (Real.differentiableAt_arctan y) (by fun_prop),
        Real.deriv_arctan, deriv_cubicPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private lemma arctan_upper_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let f : ℝ → ℝ := fun y ↦
    (y - y ^ 3 / 3 + y ^ 5 / 5) - Real.arctan y
  have hf : Differentiable ℝ f := by
    exact (by fun_prop : Differentiable ℝ (fun y : ℝ ↦
      y - y ^ 3 / 3 + y ^ 5 / 5)).sub Real.differentiable_arctan
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 6 / (1 + y ^ 2) := by
      change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) -
        Real.arctan) y = _
      rw [deriv_sub (by fun_prop) (Real.differentiableAt_arctan y),
        Real.deriv_arctan, deriv_quinticPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private lemma arctan_lower_septic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun y ↦
    Real.arctan y - (y - y ^ 3 / 3 + y ^ 5 / 5 - y ^ 7 / 7)
  have hf : Differentiable ℝ f := by
    exact Real.differentiable_arctan.sub (by fun_prop)
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 8 / (1 + y ^ 2) := by
      change deriv (Real.arctan -
        (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7)) y = _
      rw [deriv_sub (Real.differentiableAt_arctan y) (by fun_prop),
        Real.deriv_arctan, deriv_septicPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private noncomputable def c1 : ℂ :=
  ⟨3 / 32, 3 / 32 + 1 / (8 * Real.pi)⟩

private noncomputable def c2 : ℂ :=
  ⟨1 / 16, 1 / (8 * Real.pi)⟩

private noncomputable def c3 : ℂ :=
  ⟨1 / 32, 1 / (8 * Real.pi) - 1 / 32⟩

/-- The order-three upper Vaaler coefficients.  They are written out
explicitly so that neither the pointwise theorem nor its coefficient bound
depends on a numerical oracle. -/
noncomputable def degreeThreePlusCoefficient (r : ℤ) : ℂ :=
  if r = 1 then c1
  else if r = -1 then starRingEnd ℂ c1
  else if r = 2 then c2
  else if r = -2 then starRingEnd ℂ c2
  else if r = 3 then c3
  else if r = -3 then starRingEnd ℂ c3
  else 0

/-- Reflection of the upper coefficients; this majorizes `-psi`. -/
noncomputable def degreeThreeMinusCoefficient (r : ℤ) : ℂ :=
  degreeThreePlusCoefficient (-r)

/-- The real trigonometric polynomial represented by
`degreeThreePlusCoefficient`. -/
noncomputable def degreeThreePolynomial (x : ℝ) : ℝ :=
  (3 / 16 : ℝ) * Real.cos (2 * Real.pi * x) +
    (1 / 8 : ℝ) * Real.cos (4 * Real.pi * x) +
    (1 / 16 : ℝ) * Real.cos (6 * Real.pi * x) -
    (3 / 16 + 1 / (4 * Real.pi) : ℝ) * Real.sin (2 * Real.pi * x) -
    (1 / (4 * Real.pi) : ℝ) * Real.sin (4 * Real.pi * x) -
    (1 / (4 * Real.pi) - 1 / 16 : ℝ) * Real.sin (6 * Real.pi * x)

private lemma frequencies_three : frequencies 3 = {-3, -2, -1, 1, 2, 3} := by
  change (Finset.Icc (-3 : ℤ) 3).erase 0 = _
  decide

private lemma e_eq_cos_add_sin (x : ℝ) : e x =
    (Real.cos (2 * Real.pi * x) : ℂ) +
      Real.sin (2 * Real.pi * x) * Complex.I := by
  exact Complex.exp_ofReal_mul_I _

private lemma degreeThreePolynomial_eq (x : ℝ) :
    (fourierPolynomial (frequencies 3) degreeThreePlusCoefficient x).re =
      degreeThreePolynomial x := by
  rw [frequencies_three]
  simp only [fourierPolynomial, Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, not_false_eq_true,
    Finset.sum_singleton]
  simp only [degreeThreePlusCoefficient]
  norm_num
  simp only [c1, c2, c3, e_eq_cos_add_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_mul, Real.cos_neg, Real.sin_neg,
    map_neg, Complex.conj_re, Complex.conj_im]
  simp only [degreeThreePolynomial]
  ring_nf
  simp only [Real.cos_neg, Real.sin_neg]
  ring

private lemma degreeThreeMinusPolynomial_eq (x : ℝ) :
    (fourierPolynomial (frequencies 3) degreeThreeMinusCoefficient x).re =
      degreeThreePolynomial (-x) := by
  rw [frequencies_three]
  simp only [fourierPolynomial, Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, not_false_eq_true,
    Finset.sum_singleton]
  simp only [degreeThreeMinusCoefficient, degreeThreePlusCoefficient]
  norm_num
  simp only [c1, c2, c3, e_eq_cos_add_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_mul, Real.cos_neg, Real.sin_neg,
    degreeThreePolynomial, map_neg, Complex.conj_re, Complex.conj_im]
  ring_nf
  simp only [Real.cos_neg, Real.sin_neg]
  ring

private lemma degreeThreePolynomial_compressed (x : ℝ) :
    degreeThreePolynomial x =
      (-2 * Real.pi * (Real.sin (2 * Real.pi * x)) ^ 3 +
        2 * Real.pi * (Real.cos (2 * Real.pi * x)) ^ 3 +
        2 * Real.pi * (Real.cos (2 * Real.pi * x)) ^ 2 - Real.pi +
        8 * (Real.sin (2 * Real.pi * x)) ^ 3 -
        4 * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) -
        8 * Real.sin (2 * Real.pi * x)) / (8 * Real.pi) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [degreeThreePolynomial]
  have h4 : 4 * Real.pi * x = 2 * (2 * Real.pi * x) := by ring
  have h6 : 6 * Real.pi * x = 3 * (2 * Real.pi * x) := by ring
  rw [h4, h6, Real.sin_two_mul, Real.cos_two_mul,
    Real.sin_three_mul, Real.cos_three_mul]
  have hs := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  field_simp
  nlinarith

private lemma sin_two_arctan (u : ℝ) :
    Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  rw [Real.sin_two_mul]
  have hc : Real.cos (Real.arctan u) ≠ 0 := (Real.cos_arctan_pos u).ne'
  have ht := Real.tan_arctan u
  rw [Real.tan_eq_sin_div_cos] at ht
  have hs : Real.sin (Real.arctan u) = u * Real.cos (Real.arctan u) := by
    apply (div_eq_iff hc).mp
    simpa [mul_comm] using ht
  rw [hs]
  calc
    2 * (u * Real.cos (Real.arctan u)) * Real.cos (Real.arctan u) =
        2 * u * Real.cos (Real.arctan u) ^ 2 := by ring
    _ = 2 * u / (1 + u ^ 2) := by rw [Real.cos_sq_arctan]; ring

private lemma cos_two_arctan (u : ℝ) :
    Real.cos (2 * Real.arctan u) = (1 - u ^ 2) / (1 + u ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have h : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma psi_eq_sub_half {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    psi x = x - 1 / 2 := by
  have hf : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩
  rw [psi, if_neg]
  · simp [Int.fract, hf]
  · simpa [hf] using hx0.ne'

private lemma lowPolynomial_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ 129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
      480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
      48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
      320 * u ^ 3 - 960 * u := by
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hc0 : 0 ≤ 249 * Real.pi := by positivity
  have hc1 : 0 ≤ 3 * (913 * Real.pi - 320) := by nlinarith [Real.pi_gt_d2]
  have hc2 : 0 ≤ 6 * (2307 * Real.pi - 1600) := by nlinarith [Real.pi_gt_d2]
  have hc3 : 0 ≤ 8 * (5241 * Real.pi - 5360) := by nlinarith [Real.pi_gt_d2]
  have hc4 : 0 ≤ 84129 * Real.pi - 112640 := by nlinarith [Real.pi_gt_d2]
  have hc5 : 0 ≤ 117495 * Real.pi - 193408 := by nlinarith [Real.pi_gt_d2]
  have hc6 : 0 ≤ 16 * (7341 * Real.pi - 14288) := by nlinarith [Real.pi_gt_d2]
  have hc7 : 0 ≤ 2 * (42741 * Real.pi - 95432) := by nlinarith [Real.pi_gt_d2]
  have hc8 : 0 ≤ 116 * (393 * Real.pi - 976) := by nlinarith [Real.pi_gt_d2]
  have hc9 : 0 ≤ 4 * (4371 * Real.pi - 11672) := by nlinarith [Real.pi_gt_d2]
  have hc10 : 0 ≤ 64 * (69 * Real.pi - 193) := by nlinarith [Real.pi_gt_d2]
  have hc11 : 0 ≤ 8 * (69 * Real.pi - 208) := by nlinarith [Real.pi_gt_d2]
  have hB : 0 ≤
      (249 * Real.pi) * (1 - u) ^ 11 +
      (3 * (913 * Real.pi - 320)) * u * (1 - u) ^ 10 +
      (6 * (2307 * Real.pi - 1600)) * u ^ 2 * (1 - u) ^ 9 +
      (8 * (5241 * Real.pi - 5360)) * u ^ 3 * (1 - u) ^ 8 +
      (84129 * Real.pi - 112640) * u ^ 4 * (1 - u) ^ 7 +
      (117495 * Real.pi - 193408) * u ^ 5 * (1 - u) ^ 6 +
      (16 * (7341 * Real.pi - 14288)) * u ^ 6 * (1 - u) ^ 5 +
      (2 * (42741 * Real.pi - 95432)) * u ^ 7 * (1 - u) ^ 4 +
      (116 * (393 * Real.pi - 976)) * u ^ 8 * (1 - u) ^ 3 +
      (4 * (4371 * Real.pi - 11672)) * u ^ 9 * (1 - u) ^ 2 +
      (64 * (69 * Real.pi - 193)) * u ^ 10 * (1 - u) +
      (8 * (69 * Real.pi - 208)) * u ^ 11 := by positivity
  have hid :
      (249 * Real.pi) * (1 - u) ^ 11 +
      (3 * (913 * Real.pi - 320)) * u * (1 - u) ^ 10 +
      (6 * (2307 * Real.pi - 1600)) * u ^ 2 * (1 - u) ^ 9 +
      (8 * (5241 * Real.pi - 5360)) * u ^ 3 * (1 - u) ^ 8 +
      (84129 * Real.pi - 112640) * u ^ 4 * (1 - u) ^ 7 +
      (117495 * Real.pi - 193408) * u ^ 5 * (1 - u) ^ 6 +
      (16 * (7341 * Real.pi - 14288)) * u ^ 6 * (1 - u) ^ 5 +
      (2 * (42741 * Real.pi - 95432)) * u ^ 7 * (1 - u) ^ 4 +
      (116 * (393 * Real.pi - 976)) * u ^ 8 * (1 - u) ^ 3 +
      (4 * (4371 * Real.pi - 11672)) * u ^ 9 * (1 - u) ^ 2 +
      (64 * (69 * Real.pi - 193)) * u ^ 10 * (1 - u) +
      (8 * (69 * Real.pi - 208)) * u ^ 11 =
      129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
        480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
        48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
        320 * u ^ 3 - 960 * u := by ring
  linarith

private lemma highPolynomial_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
      3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
      240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
      1344 * v ^ 5 + 11200 * v ^ 3 := by
  have hw : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hc0 : 0 ≤ 63 * Real.pi := by positivity
  have hc1 : 0 ≤ 819 * Real.pi := by positivity
  have hc2 : 0 ≤ 5943 * Real.pi := by positivity
  have hc3 : 0 ≤ 7 * (3711 * Real.pi + 1600) := by positivity
  have hc4 : 0 ≤ 7 * (9507 * Real.pi + 16000) := by positivity
  have hc5 : 0 ≤ 21 * (4107 * Real.pi + 23936) := by positivity
  have hc6 : 0 ≤ 21 * (63488 - 395 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc7 : 0 ≤ 3 * (771712 - 80339 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc8 : 0 ≤ 24 * (114656 - 19131 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc9 : 0 ≤ 22 * (103144 - 21693 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc10 : 0 ≤ 4 * (320752 - 77259 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc11 : 0 ≤ 12 * (39656 - 10367 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc12 : 0 ≤ 80 * (1300 - 357 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc13 : 0 ≤ 8 * (1216 - 357 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hB : 0 ≤
      (63 * Real.pi) * (1 - v) ^ 13 +
      (819 * Real.pi) * v * (1 - v) ^ 12 +
      (5943 * Real.pi) * v ^ 2 * (1 - v) ^ 11 +
      (7 * (3711 * Real.pi + 1600)) * v ^ 3 * (1 - v) ^ 10 +
      (7 * (9507 * Real.pi + 16000)) * v ^ 4 * (1 - v) ^ 9 +
      (21 * (4107 * Real.pi + 23936)) * v ^ 5 * (1 - v) ^ 8 +
      (21 * (63488 - 395 * Real.pi)) * v ^ 6 * (1 - v) ^ 7 +
      (3 * (771712 - 80339 * Real.pi)) * v ^ 7 * (1 - v) ^ 6 +
      (24 * (114656 - 19131 * Real.pi)) * v ^ 8 * (1 - v) ^ 5 +
      (22 * (103144 - 21693 * Real.pi)) * v ^ 9 * (1 - v) ^ 4 +
      (4 * (320752 - 77259 * Real.pi)) * v ^ 10 * (1 - v) ^ 3 +
      (12 * (39656 - 10367 * Real.pi)) * v ^ 11 * (1 - v) ^ 2 +
      (80 * (1300 - 357 * Real.pi)) * v ^ 12 * (1 - v) +
      (8 * (1216 - 357 * Real.pi)) * v ^ 13 := by positivity
  have hid :
      (63 * Real.pi) * (1 - v) ^ 13 +
      (819 * Real.pi) * v * (1 - v) ^ 12 +
      (5943 * Real.pi) * v ^ 2 * (1 - v) ^ 11 +
      (7 * (3711 * Real.pi + 1600)) * v ^ 3 * (1 - v) ^ 10 +
      (7 * (9507 * Real.pi + 16000)) * v ^ 4 * (1 - v) ^ 9 +
      (21 * (4107 * Real.pi + 23936)) * v ^ 5 * (1 - v) ^ 8 +
      (21 * (63488 - 395 * Real.pi)) * v ^ 6 * (1 - v) ^ 7 +
      (3 * (771712 - 80339 * Real.pi)) * v ^ 7 * (1 - v) ^ 6 +
      (24 * (114656 - 19131 * Real.pi)) * v ^ 8 * (1 - v) ^ 5 +
      (22 * (103144 - 21693 * Real.pi)) * v ^ 9 * (1 - v) ^ 4 +
      (4 * (320752 - 77259 * Real.pi)) * v ^ 10 * (1 - v) ^ 3 +
      (12 * (39656 - 10367 * Real.pi)) * v ^ 11 * (1 - v) ^ 2 +
      (80 * (1300 - 357 * Real.pi)) * v ^ 12 * (1 - v) +
      (8 * (1216 - 357 * Real.pi)) * v ^ 13 =
      903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
        3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
        240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
        1344 * v ^ 5 + 11200 * v ^ 3 := by ring
  linarith

private noncomputable def tangentBase (u : ℝ) : ℝ :=
  let s := 2 * u / (1 + u ^ 2);
  let z := (1 - u ^ 2) / (1 + u ^ 2);
  -s ^ 3 / 4 + z ^ 3 / 4 + z ^ 2 / 4 + 1 / 2 +
    (s ^ 3 - s * z / 2 - s) / Real.pi

private lemma tangent_error_identity {x u : ℝ}
    (hangle : Real.pi * x = Real.arctan u) :
    (13 / 80 : ℝ) + degreeThreePolynomial x - (x - 1 / 2) =
      tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  rw [degreeThreePolynomial_compressed]
  have ht : 2 * Real.pi * x = 2 * Real.arctan u := by linarith
  rw [ht, sin_two_arctan, cos_two_arctan]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show x = Real.arctan u / Real.pi by
    exact (eq_div_iff hpi).mpr (by simpa [mul_comm] using hangle)]
  simp only [tangentBase]
  have hd : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma tangent_error_nonneg_of_le_one {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  let U : ℝ := u - u ^ 3 / 3 + u ^ 5 / 5
  have hatan : Real.arctan u ≤ U := arctan_upper_quintic u hu0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq := lowPolynomial_nonneg hu0 hu1
  have hd : 0 < 1 + u ^ 2 := by positivity
  have hid :
      (tangentBase u - U / Real.pi + 3 / 80) *
          ((1 + u ^ 2) ^ 3 * (240 * Real.pi)) =
        129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
          480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
          48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
          320 * u ^ 3 - 960 * u := by
    simp only [tangentBase, U]
    field_simp
    ring
  have hfactor : 0 < (1 + u ^ 2) ^ 3 * (240 * Real.pi) := by positivity
  have happ : 0 ≤ tangentBase u - U / Real.pi + 3 / 80 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : Real.arctan u / Real.pi ≤ U / Real.pi :=
    div_le_div_of_nonneg_right hatan hpi.le
  linarith

private lemma tangent_error_nonneg_of_one_le {u : ℝ}
    (hu1 : 1 ≤ u) :
    0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  let v : ℝ := u⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.mpr hu0.le
  have hv1 : v ≤ 1 := (inv_le_one₀ hu0).mpr hu1
  have hvpos : 0 < v := inv_pos.mpr hu0
  have hvu : v = u⁻¹ := rfl
  have huv : u = v⁻¹ := by simp [v, hu0.ne']
  let L : ℝ := v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
  have hL : L ≤ Real.arctan v := arctan_lower_septic v hv0
  have hatanv : Real.arctan v = Real.pi / 2 - Real.arctan u := by
    simpa [v] using Real.arctan_inv_of_pos hu0
  have hatan : Real.arctan u ≤ Real.pi / 2 - L := by linarith
  have hq := highPolynomial_nonneg hv0 hv1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd : 0 < 1 + v ^ 2 := by positivity
  have hid :
      (tangentBase (v⁻¹) - (Real.pi / 2 - L) / Real.pi + 3 / 80) *
          ((1 + v ^ 2) ^ 3 * (1680 * Real.pi)) =
        903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
          3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
          240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
          1344 * v ^ 5 + 11200 * v ^ 3 := by
    simp only [tangentBase, L]
    field_simp
    ring
  have hfactor : 0 < (1 + v ^ 2) ^ 3 * (1680 * Real.pi) := by positivity
  have happ : 0 ≤ tangentBase (v⁻¹) -
      (Real.pi / 2 - L) / Real.pi + 3 / 80 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : Real.arctan u / Real.pi ≤
      (Real.pi / 2 - L) / Real.pi := div_le_div_of_nonneg_right hatan hpi.le
  rw [huv] at hdiv ⊢
  linarith

private lemma lowMinusPolynomial_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
      300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
      50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hc0 : 0 ≤ 24 * Real.pi := by positivity
  have hc1 : 0 ≤ 24 * (9 * Real.pi + 100) := by positivity
  have hc2 : 0 ≤ 12 * (1600 - 47 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc3 : 0 ≤ 20 * (3320 - 339 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc4 : 0 ≤ 12 * (10800 - 1691 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc5 : 0 ≤ 12 * (13150 - 2633 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc6 : 0 ≤ 80 * (1570 - 369 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc7 : 0 ≤ 48 * (1375 - 359 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc8 : 0 ≤ 864 * (25 - 7 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc9 : 0 ≤ 16 * (200 - 63 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hB : 0 ≤
      (24 * Real.pi) * (1 - u) ^ 9 +
      (24 * (9 * Real.pi + 100)) * u * (1 - u) ^ 8 +
      (12 * (1600 - 47 * Real.pi)) * u ^ 2 * (1 - u) ^ 7 +
      (20 * (3320 - 339 * Real.pi)) * u ^ 3 * (1 - u) ^ 6 +
      (12 * (10800 - 1691 * Real.pi)) * u ^ 4 * (1 - u) ^ 5 +
      (12 * (13150 - 2633 * Real.pi)) * u ^ 5 * (1 - u) ^ 4 +
      (80 * (1570 - 369 * Real.pi)) * u ^ 6 * (1 - u) ^ 3 +
      (48 * (1375 - 359 * Real.pi)) * u ^ 7 * (1 - u) ^ 2 +
      (864 * (25 - 7 * Real.pi)) * u ^ 8 * (1 - u) +
      (16 * (200 - 63 * Real.pi)) * u ^ 9 := by positivity
  have hid :
      (24 * Real.pi) * (1 - u) ^ 9 +
      (24 * (9 * Real.pi + 100)) * u * (1 - u) ^ 8 +
      (12 * (1600 - 47 * Real.pi)) * u ^ 2 * (1 - u) ^ 7 +
      (20 * (3320 - 339 * Real.pi)) * u ^ 3 * (1 - u) ^ 6 +
      (12 * (10800 - 1691 * Real.pi)) * u ^ 4 * (1 - u) ^ 5 +
      (12 * (13150 - 2633 * Real.pi)) * u ^ 5 * (1 - u) ^ 4 +
      (80 * (1570 - 369 * Real.pi)) * u ^ 6 * (1 - u) ^ 3 +
      (48 * (1375 - 359 * Real.pi)) * u ^ 7 * (1 - u) ^ 2 +
      (864 * (25 - 7 * Real.pi)) * u ^ 8 * (1 - u) +
      (16 * (200 - 63 * Real.pi)) * u ^ 9 =
      -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
        300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
        50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by ring
  linarith

private lemma highMinusPolynomial_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
      300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
      30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
      1000 * v ^ 3) := by
  have hw : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hc0 : 0 ≤ 24 * Real.pi := by positivity
  have hc1 : 0 ≤ 264 * Real.pi := by positivity
  have hc2 : 0 ≤ 1692 * Real.pi := by positivity
  have hc3 : 0 ≤ 4 * (2127 * Real.pi - 1000) := by nlinarith [Real.pi_gt_three]
  have hc4 : 0 ≤ 16 * (1899 * Real.pi - 2000) := by nlinarith [Real.pi_gt_three]
  have hc5 : 0 ≤ 80 * (903 * Real.pi - 1394) := by nlinarith [Real.pi_gt_three]
  have hc6 : 0 ≤ 4 * (28599 * Real.pi - 55280) := by nlinarith [Real.pi_gt_three]
  have hc7 : 0 ≤ 4 * (30483 * Real.pi - 68290) := by nlinarith [Real.pi_gt_three]
  have hc8 : 0 ≤ 32 * (2724 * Real.pi - 6745) := by nlinarith [Real.pi_gt_three]
  have hc9 : 0 ≤ 16 * (2529 * Real.pi - 6695) := by nlinarith [Real.pi_gt_three]
  have hc10 : 0 ≤ 32 * (348 * Real.pi - 965) := by nlinarith [Real.pi_gt_three]
  have hc11 : 0 ≤ 16 * (87 * Real.pi - 260) := by nlinarith [Real.pi_gt_three]
  have hB : 0 ≤
      (24 * Real.pi) * (1 - v) ^ 11 +
      (264 * Real.pi) * v * (1 - v) ^ 10 +
      (1692 * Real.pi) * v ^ 2 * (1 - v) ^ 9 +
      (4 * (2127 * Real.pi - 1000)) * v ^ 3 * (1 - v) ^ 8 +
      (16 * (1899 * Real.pi - 2000)) * v ^ 4 * (1 - v) ^ 7 +
      (80 * (903 * Real.pi - 1394)) * v ^ 5 * (1 - v) ^ 6 +
      (4 * (28599 * Real.pi - 55280)) * v ^ 6 * (1 - v) ^ 5 +
      (4 * (30483 * Real.pi - 68290)) * v ^ 7 * (1 - v) ^ 4 +
      (32 * (2724 * Real.pi - 6745)) * v ^ 8 * (1 - v) ^ 3 +
      (16 * (2529 * Real.pi - 6695)) * v ^ 9 * (1 - v) ^ 2 +
      (32 * (348 * Real.pi - 965)) * v ^ 10 * (1 - v) +
      (16 * (87 * Real.pi - 260)) * v ^ 11 := by positivity
  have hid :
      (24 * Real.pi) * (1 - v) ^ 11 +
      (264 * Real.pi) * v * (1 - v) ^ 10 +
      (1692 * Real.pi) * v ^ 2 * (1 - v) ^ 9 +
      (4 * (2127 * Real.pi - 1000)) * v ^ 3 * (1 - v) ^ 8 +
      (16 * (1899 * Real.pi - 2000)) * v ^ 4 * (1 - v) ^ 7 +
      (80 * (903 * Real.pi - 1394)) * v ^ 5 * (1 - v) ^ 6 +
      (4 * (28599 * Real.pi - 55280)) * v ^ 6 * (1 - v) ^ 5 +
      (4 * (30483 * Real.pi - 68290)) * v ^ 7 * (1 - v) ^ 4 +
      (32 * (2724 * Real.pi - 6745)) * v ^ 8 * (1 - v) ^ 3 +
      (16 * (2529 * Real.pi - 6695)) * v ^ 9 * (1 - v) ^ 2 +
      (32 * (348 * Real.pi - 965)) * v ^ 10 * (1 - v) +
      (16 * (87 * Real.pi - 260)) * v ^ 11 =
      4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
        300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
        30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
        1000 * v ^ 3) := by ring
  linarith

private noncomputable def tangentMinusBase (u : ℝ) : ℝ :=
  let s := 2 * u / (1 + u ^ 2);
  let z := (1 - u ^ 2) / (1 + u ^ 2);
  s ^ 3 / 4 + z ^ 3 / 4 + z ^ 2 / 4 - 1 / 2 +
    (-s ^ 3 + s * z / 2 + s) / Real.pi

private lemma tangent_minus_error_identity {x u : ℝ}
    (hangle : Real.pi * x = Real.arctan u) :
    (33 / 200 : ℝ) + degreeThreePolynomial (-x) + (x - 1 / 2) =
      tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  rw [degreeThreePolynomial_compressed]
  have ht : 2 * Real.pi * (-x) = -(2 * Real.arctan u) := by linarith
  rw [ht, Real.sin_neg, Real.cos_neg, sin_two_arctan, cos_two_arctan]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show x = Real.arctan u / Real.pi by
    exact (eq_div_iff hpi).mpr (by simpa [mul_comm] using hangle)]
  simp only [tangentMinusBase]
  have hd : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma tangent_minus_error_nonneg_of_le_one {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  let L : ℝ := u - u ^ 3 / 3
  have hL : L ≤ Real.arctan u := arctan_lower_cubic u hu0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq := lowMinusPolynomial_nonneg hu0 hu1
  have hid :
      (tangentMinusBase u + L / Real.pi + 1 / 25) *
          ((1 + u ^ 2) ^ 3 * (600 * Real.pi)) =
        -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
          300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
          50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by
    simp only [tangentMinusBase, L]
    field_simp
    ring
  have hfactor : 0 < (1 + u ^ 2) ^ 3 * (600 * Real.pi) := by positivity
  have happ : 0 ≤ tangentMinusBase u + L / Real.pi + 1 / 25 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : L / Real.pi ≤ Real.arctan u / Real.pi :=
    div_le_div_of_nonneg_right hL hpi.le
  linarith

private lemma tangent_minus_error_nonneg_of_one_le {u : ℝ}
    (hu1 : 1 ≤ u) :
    0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  let v : ℝ := u⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.mpr hu0.le
  have hv1 : v ≤ 1 := (inv_le_one₀ hu0).mpr hu1
  have hvpos : 0 < v := inv_pos.mpr hu0
  have huv : u = v⁻¹ := by simp [v]
  let U : ℝ := v - v ^ 3 / 3 + v ^ 5 / 5
  have hU : Real.arctan v ≤ U := arctan_upper_quintic v hv0
  have hatanv : Real.arctan v = Real.pi / 2 - Real.arctan u := by
    simpa [v] using Real.arctan_inv_of_pos hu0
  have hatan : Real.pi / 2 - U ≤ Real.arctan u := by linarith
  have hq := highMinusPolynomial_nonneg hv0 hv1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hid :
      (tangentMinusBase (v⁻¹) + (Real.pi / 2 - U) / Real.pi + 1 / 25) *
          ((1 + v ^ 2) ^ 3 * (600 * Real.pi)) =
        4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
          300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
          30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
          1000 * v ^ 3) := by
    simp only [tangentMinusBase, U]
    field_simp [hvpos.ne']
    ring
  have hfactor : 0 < (1 + v ^ 2) ^ 3 * (600 * Real.pi) := by positivity
  have happ : 0 ≤ tangentMinusBase (v⁻¹) +
      (Real.pi / 2 - U) / Real.pi + 1 / 25 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : (Real.pi / 2 - U) / Real.pi ≤
      Real.arctan u / Real.pi := div_le_div_of_nonneg_right hatan hpi.le
  rw [huv] at hdiv ⊢
  linarith

private lemma degreeThreePlus_on_half (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial x := by
  rcases hx0.eq_or_lt with rfl | hx0
  · norm_num [psi, degreeThreePolynomial]
  rcases hxhalf.eq_or_lt with hx | hxhalf
  · subst x
    rw [psi_eq_sub_half (by norm_num) (by norm_num)]
    rw [degreeThreePolynomial]
    ring_nf
    rw [show Real.pi * 2 = (2 : ℕ) * Real.pi by ring,
      show Real.pi * 3 = (3 : ℕ) * Real.pi by ring,
      Real.sin_nat_mul_pi 2, Real.sin_nat_mul_pi 3,
      Real.cos_nat_mul_pi 2, Real.cos_nat_mul_pi 3]
    norm_num
  · let u := Real.tan (Real.pi * x)
    have hy0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0.le
    have hyhalf : Real.pi * x < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hu0 : 0 ≤ u := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hy0 hyhalf.le
    have hangle : Real.pi * x = Real.arctan u := by
      symm
      exact Real.arctan_tan (by nlinarith [Real.pi_pos]) hyhalf
    have hid := tangent_error_identity hangle
    have herr : 0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
      rcases le_total u 1 with hu1 | h1u
      · exact tangent_error_nonneg_of_le_one hu0 hu1
      · exact tangent_error_nonneg_of_one_le h1u
    rw [psi_eq_sub_half hx0 (by linarith)]
    linarith

private lemma degreeThreeMinus_on_half (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial (-x) := by
  rcases hx0.eq_or_lt with rfl | hx0
  · norm_num [psi, degreeThreePolynomial]
  rcases hxhalf.eq_or_lt with hx | hxhalf
  · subst x
    rw [psi_eq_sub_half (by norm_num) (by norm_num)]
    rw [degreeThreePolynomial]
    ring_nf
    rw [show Real.pi * 2 = (2 : ℕ) * Real.pi by ring,
      show Real.pi * 3 = (3 : ℕ) * Real.pi by ring]
    simp only [Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi,
      Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    norm_num
  · let u := Real.tan (Real.pi * x)
    have hy0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0.le
    have hyhalf : Real.pi * x < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hu0 : 0 ≤ u := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hy0 hyhalf.le
    have hangle : Real.pi * x = Real.arctan u := by
      symm
      exact Real.arctan_tan (by nlinarith [Real.pi_pos]) hyhalf
    have hid := tangent_minus_error_identity hangle
    have herr : 0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
      rcases le_total u 1 with hu1 | h1u
      · exact tangent_minus_error_nonneg_of_le_one hu0 hu1
      · exact tangent_minus_error_nonneg_of_one_le h1u
    rw [psi_eq_sub_half hx0 (by linarith)]
    linarith

private lemma sin_harmonic_fract (k : ℤ) (x : ℝ) :
    Real.sin (2 * (k : ℝ) * Real.pi * x) =
      Real.sin (2 * (k : ℝ) * Real.pi * Int.fract x) := by
  have hx := Int.floor_add_fract x
  have hang : 2 * (k : ℝ) * Real.pi * x =
      2 * (k : ℝ) * Real.pi * Int.fract x +
        (k * ⌊x⌋ : ℤ) * (2 * Real.pi) := by
    calc
      2 * (k : ℝ) * Real.pi * x =
          2 * (k : ℝ) * Real.pi * ((⌊x⌋ : ℤ) + Int.fract x) := by rw [hx]
      _ = _ := by push_cast; ring
  calc
    Real.sin (2 * (k : ℝ) * Real.pi * x) =
        Real.sin (2 * (k : ℝ) * Real.pi * Int.fract x +
          (k * ⌊x⌋ : ℤ) * (2 * Real.pi)) := by
            rw [hang]
    _ = _ := Real.sin_add_int_mul_two_pi _ _

private lemma cos_harmonic_fract (k : ℤ) (x : ℝ) :
    Real.cos (2 * (k : ℝ) * Real.pi * x) =
      Real.cos (2 * (k : ℝ) * Real.pi * Int.fract x) := by
  have hx := Int.floor_add_fract x
  have hang : 2 * (k : ℝ) * Real.pi * x =
      2 * (k : ℝ) * Real.pi * Int.fract x +
        (k * ⌊x⌋ : ℤ) * (2 * Real.pi) := by
    calc
      2 * (k : ℝ) * Real.pi * x =
          2 * (k : ℝ) * Real.pi * ((⌊x⌋ : ℤ) + Int.fract x) := by rw [hx]
      _ = _ := by push_cast; ring
  calc
    Real.cos (2 * (k : ℝ) * Real.pi * x) =
        Real.cos (2 * (k : ℝ) * Real.pi * Int.fract x +
          (k * ⌊x⌋ : ℤ) * (2 * Real.pi)) := by
            rw [hang]
    _ = _ := Real.cos_add_int_mul_two_pi _ _

private lemma degreeThreePolynomial_fract (x : ℝ) :
    degreeThreePolynomial x = degreeThreePolynomial (Int.fract x) := by
  rw [degreeThreePolynomial, degreeThreePolynomial]
  have hs1 := sin_harmonic_fract 1 x
  have hs2 := sin_harmonic_fract 2 x
  have hs3 := sin_harmonic_fract 3 x
  have hc1 := cos_harmonic_fract 1 x
  have hc2 := cos_harmonic_fract 2 x
  have hc3 := cos_harmonic_fract 3 x
  norm_num at hs1 hs2 hs3 hc1 hc2 hc3
  rw [hs1, hs2, hs3, hc1, hc2, hc3]

private lemma psi_eq_fract_sub_half {x : ℝ} (hx : Int.fract x ≠ 0) :
    psi x = Int.fract x - 1 / 2 := by
  rw [psi, if_neg]
  intro h
  apply hx
  calc
    Int.fract x = Int.fract (⌊x⌋ : ℝ) := congrArg Int.fract h
    _ = 0 := Int.fract_floor x

private lemma degreeThreePlus_global (x : ℝ) :
    psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial x := by
  let t := Int.fract x
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  have hperiod := degreeThreePolynomial_fract x
  change degreeThreePolynomial x = degreeThreePolynomial t at hperiod
  by_cases ht : t = 0
  · have hxint : x = (⌊x⌋ : ℝ) := by
      have h := Int.floor_add_fract x
      change (⌊x⌋ : ℝ) + t = x at h
      linarith
    have hzero := degreeThreePlus_on_half 0 (by norm_num) (by norm_num)
    rw [psi, if_pos hxint, hperiod, ht]
    simpa [psi] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hpsi := psi_eq_fract_sub_half ht
    change psi x = t - 1 / 2 at hpsi
    rcases le_total t (1 / 2) with hthalf | hhalft
    · have h := degreeThreePlus_on_half t ht0 hthalf
      rw [psi_eq_sub_half htpos ht1] at h
      rw [hpsi, hperiod]
      exact h
    · let y := 1 - t
      have hy0 : 0 ≤ y := by dsimp [y]; linarith
      have hyhalf : y ≤ 1 / 2 := by dsimp [y]; linarith
      have hypos : 0 < y := by dsimp [y]; linarith
      have hy1 : y < 1 := by dsimp [y]; linarith
      have hfy : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, hy1⟩
      have hfny : Int.fract (-y) = t := by
        have hn := Int.fract_neg (show Int.fract y ≠ 0 by simpa [hfy] using hypos.ne')
        rw [hfy] at hn
        dsimp [y] at hn ⊢
        linarith
      have hpny := degreeThreePolynomial_fract (-y)
      rw [hfny] at hpny
      have h := degreeThreeMinus_on_half y hy0 hyhalf
      rw [psi_eq_sub_half hypos hy1, hpny] at h
      rw [hpsi, hperiod]
      dsimp [y] at h
      linarith

private lemma degreeThreeMinus_global (x : ℝ) :
    -psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial (-x) := by
  let t := Int.fract x
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  have hperiod := degreeThreePolynomial_fract (-x)
  by_cases ht : t = 0
  · have hxint : x = (⌊x⌋ : ℝ) := by
      have h := Int.floor_add_fract x
      change (⌊x⌋ : ℝ) + t = x at h
      linarith
    have hzero := degreeThreeMinus_on_half 0 (by norm_num) (by norm_num)
    have hfx : Int.fract (-x) = 0 := by
      rw [Int.fract_neg_eq_zero]
      exact ht
    rw [hfx] at hperiod
    rw [psi, if_pos hxint, hperiod]
    simpa [psi] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hpsi := psi_eq_fract_sub_half ht
    change psi x = t - 1 / 2 at hpsi
    rcases le_total t (1 / 2) with hthalf | hhalft
    · have hft : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
      have hfnt : Int.fract (-t) = 1 - t := by
        simpa [hft] using Int.fract_neg (show Int.fract t ≠ 0 by simpa [hft])
      have hpx : degreeThreePolynomial (-x) = degreeThreePolynomial (-t) := by
        rw [degreeThreePolynomial_fract (-x), degreeThreePolynomial_fract (-t), hfnt]
        have hfnx : Int.fract (-x) = 1 - t := by
          simpa [t] using Int.fract_neg (show Int.fract x ≠ 0 by simpa [t])
        rw [hfnx]
      have h := degreeThreeMinus_on_half t ht0 hthalf
      rw [psi_eq_sub_half htpos ht1] at h
      rw [hpsi, hpx]
      exact h
    · let y := 1 - t
      have hy0 : 0 ≤ y := by dsimp [y]; linarith
      have hyhalf : y ≤ 1 / 2 := by dsimp [y]; linarith
      have hypos : 0 < y := by dsimp [y]; linarith
      have hy1 : y < 1 := by dsimp [y]; linarith
      have hfnx : Int.fract (-x) = y := by
        have hn := Int.fract_neg (show Int.fract x ≠ 0 by simpa [t])
        change Int.fract (-x) = 1 - t at hn
        exact hn
      rw [degreeThreePolynomial_fract (-x), hfnx]
      have h := degreeThreePlus_on_half y hy0 hyhalf
      rw [psi_eq_sub_half hypos hy1] at h
      rw [hpsi]
      dsimp [y] at h ⊢
      linarith

/-- The unconditional order-three upper Fourier majorant for `psi`. -/
theorem degreeThreePlus_majorant :
    IsUpperMajorant (frequencies 3) psi (33 / 200) degreeThreePlusCoefficient := by
  intro x
  rw [degreeThreePolynomial_eq]
  exact degreeThreePlus_global x

/-- The reflected unconditional order-three upper Fourier majorant for
`-psi`. -/
theorem degreeThreeMinus_majorant :
    IsUpperMajorant (frequencies 3) (fun x ↦ -psi x) (33 / 200)
      degreeThreeMinusCoefficient := by
  intro x
  rw [degreeThreeMinusPolynomial_eq]
  exact degreeThreeMinus_global x

private lemma inverse_eight_pi_bounds :
    (1 / 32 : ℝ) ≤ 1 / (8 * Real.pi) ∧ 1 / (8 * Real.pi) ≤ 1 / 24 := by
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Real.pi_lt_four]
  · apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [Real.pi_gt_three]

private lemma norm_c1_le : ‖c1‖ ≤ (11 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c1‖ ≤ |c1.re| + |c1.im| := Complex.norm_le_abs_re_add_abs_im c1
    _ = 3 / 32 + (3 / 32 + 1 / (8 * Real.pi)) := by
      rw [c1]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by positivity)]
    _ ≤ 11 / 48 := by linarith

private lemma norm_c2_le : ‖c2‖ ≤ (5 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c2‖ ≤ |c2.re| + |c2.im| := Complex.norm_le_abs_re_add_abs_im c2
    _ = 1 / 16 + 1 / (8 * Real.pi) := by
      rw [c2]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by positivity)]
    _ ≤ 5 / 48 := by linarith

private lemma norm_c3_le : ‖c3‖ ≤ (2 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c3‖ ≤ |c3.re| + |c3.im| := Complex.norm_le_abs_re_add_abs_im c3
    _ = 1 / 32 + (1 / (8 * Real.pi) - 1 / 32) := by
      rw [c3]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith [hq.1])]
    _ ≤ 2 / 48 := by linarith

/-- The explicit `ℓ¹` norm bound for the upper coefficients. -/
theorem sum_norm_degreeThreePlusCoefficient_le :
    (∑ r ∈ frequencies 3, ‖degreeThreePlusCoefficient r‖) ≤ (3 / 4 : ℝ) := by
  rw [frequencies_three]
  norm_num [degreeThreePlusCoefficient]
  nlinarith [norm_c1_le, norm_c2_le, norm_c3_le]

/-- The reflected coefficients have the same `ℓ¹` bound. -/
theorem sum_norm_degreeThreeMinusCoefficient_le :
    (∑ r ∈ frequencies 3, ‖degreeThreeMinusCoefficient r‖) ≤ (3 / 4 : ℝ) := by
  rw [frequencies_three]
  norm_num [degreeThreeMinusCoefficient, degreeThreePlusCoefficient]
  nlinarith [norm_c1_le, norm_c2_le, norm_c3_le]

end Erdos175.VaalerDegreeTen
