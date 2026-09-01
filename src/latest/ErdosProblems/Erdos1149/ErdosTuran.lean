/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A finite one-dimensional Erdős--Turán inequality

This file proves the trigonometric-approximation input needed in the proof of
Erdős problem 1149.  Multiplicities are retained: the points are indexed by an
arbitrary finite set rather than stored in a `Finset` of points.

The approximation is obtained from one-sided difference quotients of the
periodic second Bernoulli polynomial.  These difference quotients sandwich the
periodic first Bernoulli function.  Since the Fourier series of `B₂` is
absolutely summable, it can be truncated *uniformly*.  The resulting upper and
lower trigonometric polynomials have zero-frequency errors as small as desired,
and every nonzero coefficient has the usual harmonic `1 / |h|` bound.  This is
a qualitative (finite-frequency) form of the Erdős--Turán inequality; unlike a
Weyl-criterion statement, it records the concrete finite exponential-sum
bound used downstream.
-/

open scoped BigOperators ComplexConjugate Real

open Filter Finset Function Set Topology

namespace Erdos1149.ErdosTuran

noncomputable section

/-- The periodic first Bernoulli function, with the right-continuous convention
at integers. -/
def sawtooth (x : ℝ) : ℝ := Int.fract x - 1 / 2

/-- The periodic second Bernoulli polynomial. -/
def periodicB₂ (x : ℝ) : ℝ := bernoulliFun 2 (Int.fract x)

theorem periodicB₂_eq (x : ℝ) :
    periodicB₂ x = (Int.fract x) ^ 2 - Int.fract x + 6⁻¹ := by
  simp [periodicB₂, bernoulliFun_two]

/-- A forward difference quotient of the periodic second Bernoulli polynomial. -/
def forwardQuotient (δ x : ℝ) : ℝ :=
  (periodicB₂ (x + δ) - periodicB₂ x) / (2 * δ)

/-- A backward difference quotient of the periodic second Bernoulli polynomial. -/
def backwardQuotient (δ x : ℝ) : ℝ :=
  (periodicB₂ x - periodicB₂ (x - δ)) / (2 * δ)

private theorem fract_add_small_cases (x δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Int.fract (x + δ) = Int.fract x + δ ∨
      Int.fract (x + δ) = Int.fract x + δ - 1 := by
  by_cases hδeq : δ = 1
  · subst δ
    right
    simp
  have hδlt : δ < 1 := lt_of_le_of_ne hδ1 hδeq
  have hδfract : Int.fract δ = δ := Int.fract_eq_self.mpr ⟨hδ0, hδlt⟩
  obtain ⟨z, hz⟩ := Int.fract_add x δ
  rw [hδfract] at hz
  have hzlo : (-2 : ℝ) < (z : ℝ) := by
    have hv0 := Int.fract_nonneg (x + δ)
    have hu1 := Int.fract_lt_one x
    linarith
  have hzhi : (z : ℝ) ≤ 0 := by
    have hle := Int.fract_add_le x δ
    rw [hδfract] at hle
    linarith
  have hz' : z = 0 ∨ z = -1 := by
    have hzlo' : (-2 : ℤ) < z := by exact_mod_cast hzlo
    have hzhi' : z ≤ 0 := by exact_mod_cast hzhi
    omega
  rcases hz' with rfl | rfl
  · left
    norm_num at hz ⊢
    linarith
  · right
    norm_num at hz ⊢
    linarith

private theorem fract_sub_small_cases (x δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Int.fract (x - δ) = Int.fract x - δ ∨
      Int.fract (x - δ) = Int.fract x - δ + 1 := by
  have h := fract_add_small_cases (x - δ) δ hδ0 hδ1
  simp only [sub_add_cancel] at h
  rcases h with h | h
  · left
    linarith
  · right
    linarith

/-- A forward quotient lies below the right-continuous first Bernoulli
function, up to `δ / 2`. -/
theorem forwardQuotient_sub_half_le_sawtooth (x δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    forwardQuotient δ x - δ / 2 ≤ sawtooth x := by
  have hcases := fract_add_small_cases x δ hδ.le hδ1
  rcases hcases with h | h
  · rw [forwardQuotient, periodicB₂_eq, periodicB₂_eq, sawtooth, h]
    field_simp
    ring_nf
    exact le_rfl
  · rw [forwardQuotient, periodicB₂_eq, periodicB₂_eq, sawtooth, h]
    have hu1 := Int.fract_lt_one x
    have hv0 := Int.fract_nonneg (x + δ)
    rw [h] at hv0
    field_simp
    nlinarith

/-- A backward quotient lies above the right-continuous first Bernoulli
function, up to `δ / 2`. -/
theorem sawtooth_le_backwardQuotient_add_half (x δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sawtooth x ≤ backwardQuotient δ x + δ / 2 := by
  have hcases := fract_sub_small_cases x δ hδ.le hδ1
  rcases hcases with h | h
  · rw [backwardQuotient, periodicB₂_eq, periodicB₂_eq, sawtooth, h]
    field_simp
    ring_nf
    exact le_rfl
  · rw [backwardQuotient, periodicB₂_eq, periodicB₂_eq, sawtooth, h]
    have hu0 := Int.fract_nonneg x
    have hv1 := Int.fract_lt_one (x - δ)
    rw [h] at hv1
    field_simp
    nlinarith

/-- The interval indicator is the jump of the first periodic Bernoulli
function.  This identity includes both endpoints with the convention
`[0,b)`. -/
theorem intervalIndicator_sub_eq_sawtooth (x b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (if Int.fract x < b then (1 : ℝ) else 0) - b =
      sawtooth (x - b) - sawtooth x := by
  rw [sawtooth, sawtooth]
  have hx0 := Int.fract_nonneg x
  have hx1 := Int.fract_lt_one x
  by_cases hxb : Int.fract x < b
  · rw [if_pos hxb]
    have hfract : Int.fract (x - b) = Int.fract x - b + 1 := by
      have hcases := fract_sub_small_cases x b hb0 hb1
      rcases hcases with h | h
      · have hnonneg := Int.fract_nonneg (x - b)
        rw [h] at hnonneg
        linarith
      · exact h
    rw [hfract]
    ring
  · rw [if_neg hxb]
    have hbx : b ≤ Int.fract x := le_of_not_gt hxb
    have hfract : Int.fract (x - b) = Int.fract x - b := by
      have hcases := fract_sub_small_cases x b hb0 hb1
      rcases hcases with h | h
      · exact h
      · have hlt := Int.fract_lt_one (x - b)
        rw [h] at hlt
        linarith
    rw [hfract]
    ring

/-- The real function appearing above the interval indicator. -/
def upperEnvelope (δ b x : ℝ) : ℝ :=
  b + δ + backwardQuotient δ (x - b) - forwardQuotient δ x

/-- The real function appearing below the interval indicator. -/
def lowerEnvelope (δ b x : ℝ) : ℝ :=
  b - δ + forwardQuotient δ (x - b) - backwardQuotient δ x

theorem intervalIndicator_le_upperEnvelope (x b δ : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (if Int.fract x < b then (1 : ℝ) else 0) ≤ upperEnvelope δ b x := by
  have h₁ := sawtooth_le_backwardQuotient_add_half (x - b) δ hδ hδ1
  have h₂ := forwardQuotient_sub_half_le_sawtooth x δ hδ hδ1
  have hid := intervalIndicator_sub_eq_sawtooth x b hb0 hb1
  rw [upperEnvelope]
  linarith

theorem lowerEnvelope_le_intervalIndicator (x b δ : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    lowerEnvelope δ b x ≤ (if Int.fract x < b then (1 : ℝ) else 0) := by
  have h₁ := forwardQuotient_sub_half_le_sawtooth (x - b) δ hδ hδ1
  have h₂ := sawtooth_le_backwardQuotient_add_half x δ hδ hδ1
  have hid := intervalIndicator_sub_eq_sawtooth x b hb0 hb1
  rw [lowerEnvelope]
  linarith

/-! ## Absolutely convergent Fourier expansions -/

/-- The Fourier coefficient of the periodic second Bernoulli polynomial. -/
def b₂Coeff (h : ℤ) : ℂ :=
  -(2 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * h) ^ 2

/-- Fourier coefficients of the forward Bernoulli difference quotient. -/
def forwardCoeff (δ : ℝ) (h : ℤ) : ℂ :=
  b₂Coeff h * (fourier h (δ : UnitAddCircle) - 1) / (2 * δ)

/-- Fourier coefficients of the backward Bernoulli difference quotient. -/
def backwardCoeff (δ : ℝ) (h : ℤ) : ℂ :=
  b₂Coeff h * (1 - fourier h ((-δ : ℝ) : UnitAddCircle)) / (2 * δ)

theorem hasSum_b₂_fourier (x : ℝ) :
    HasSum (fun h : ℤ => b₂Coeff h * fourier h (x : UnitAddCircle)) (periodicB₂ x) := by
  let B : C(UnitAddCircle, ℂ) :=
    ContinuousMap.mk ((↑) ∘ periodizedBernoulli 2)
      (Complex.continuous_ofReal.comp (periodizedBernoulli.continuous (by norm_num)))
  have hc : ∀ h : ℤ, fourierCoeff B h = b₂Coeff h := by
    intro h
    rw [show B = ContinuousMap.mk ((↑) ∘ periodizedBernoulli 2) _ from rfl,
      ContinuousMap.coe_mk, fourierCoeff_bernoulli_eq (by norm_num)]
    rfl
  have hs := has_pointwise_sum_fourier_series_of_summable
    ((summable_bernoulli_fourier (by norm_num : 2 ≤ 2)).congr fun h => (hc h).symm)
    (x : UnitAddCircle)
  simp_rw [hc, smul_eq_mul] at hs
  convert hs using 1
  dsimp [B]
  norm_cast
  have hxcoe : (x : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change x - Int.fract x ∈ AddSubgroup.zmultiples (1 : ℝ)
    rw [Int.self_sub_fract]
    exact ⟨⌊x⌋, by simp⟩
  rw [periodicB₂, hxcoe]
  unfold periodizedBernoulli
  rw [AddCircle.liftIco_coe_apply]
  refine ⟨Int.fract_nonneg x, ?_⟩
  simpa only [zero_add] using Int.fract_lt_one x

private theorem fourier_coe_add (h : ℤ) (x y : ℝ) :
    fourier h ((x + y : ℝ) : UnitAddCircle) =
      fourier h (y : UnitAddCircle) * fourier h (x : UnitAddCircle) := by
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hasSum_forwardCoeff (δ x : ℝ) :
    HasSum (fun h : ℤ => forwardCoeff δ h * fourier h (x : UnitAddCircle))
      (forwardQuotient δ x) := by
  have hd := ((hasSum_b₂_fourier (x + δ)).sub (hasSum_b₂_fourier x)).div_const
    (2 * δ : ℂ)
  have heq : (fun h : ℤ => forwardCoeff δ h * fourier h (x : UnitAddCircle)) =
      (fun h : ℤ => (b₂Coeff h * fourier h ((x + δ : ℝ) : UnitAddCircle) -
        b₂Coeff h * fourier h (x : UnitAddCircle)) / (2 * δ)) := by
    funext h
    change b₂Coeff h * (fourier h (δ : UnitAddCircle) - 1) / (2 * δ) *
      fourier h (x : UnitAddCircle) = _
    rw [fourier_coe_add]
    ring
  rw [heq]
  exact_mod_cast hd

theorem hasSum_backwardCoeff (δ x : ℝ) :
    HasSum (fun h : ℤ => backwardCoeff δ h * fourier h (x : UnitAddCircle))
      (backwardQuotient δ x) := by
  have hd := ((hasSum_b₂_fourier x).sub (hasSum_b₂_fourier (x - δ))).div_const
    (2 * δ : ℂ)
  have heq : (fun h : ℤ => backwardCoeff δ h * fourier h (x : UnitAddCircle)) =
      (fun h : ℤ => (b₂Coeff h * fourier h (x : UnitAddCircle) -
        b₂Coeff h * fourier h ((x - δ : ℝ) : UnitAddCircle)) / (2 * δ)) := by
    funext h
    change b₂Coeff h * (1 - fourier h ((-δ : ℝ) : UnitAddCircle)) / (2 * δ) *
      fourier h (x : UnitAddCircle) = _
    have hadd : fourier h ((x - δ : ℝ) : UnitAddCircle) =
        fourier h ((-δ : ℝ) : UnitAddCircle) * fourier h (x : UnitAddCircle) := by
      simpa only [sub_eq_add_neg] using fourier_coe_add h x (-δ)
    rw [hadd]
    ring
  rw [heq]
  exact_mod_cast hd

/-- Coefficients of the zero-mean part of the upper envelope. -/
def upperCoeff (δ b : ℝ) (h : ℤ) : ℂ :=
  backwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle) - forwardCoeff δ h

/-- Coefficients of the zero-mean part of the lower envelope. -/
def lowerCoeff (δ b : ℝ) (h : ℤ) : ℂ :=
  forwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle) - backwardCoeff δ h

theorem hasSum_upperCoeff (δ b x : ℝ) :
    HasSum (fun h : ℤ => upperCoeff δ b h * fourier h (x : UnitAddCircle))
      (upperEnvelope δ b x - (b + δ)) := by
  have hb := hasSum_backwardCoeff δ (x - b)
  have hf := hasSum_forwardCoeff δ x
  have heq : (fun h : ℤ => upperCoeff δ b h * fourier h (x : UnitAddCircle)) =
      (fun h : ℤ => backwardCoeff δ h * fourier h ((x - b : ℝ) : UnitAddCircle) -
        forwardCoeff δ h * fourier h (x : UnitAddCircle)) := by
    funext h
    rw [upperCoeff]
    have hadd : fourier h ((x - b : ℝ) : UnitAddCircle) =
        fourier h ((-b : ℝ) : UnitAddCircle) * fourier h (x : UnitAddCircle) := by
      simpa only [sub_eq_add_neg] using fourier_coe_add h x (-b)
    rw [hadd]
    ring
  rw [heq]
  have hval : upperEnvelope δ b x - (b + δ) =
      backwardQuotient δ (x - b) - forwardQuotient δ x := by
    unfold upperEnvelope
    ring
  have hvalc : (upperEnvelope δ b x : ℂ) - ((b : ℂ) + δ) =
      (backwardQuotient δ (x - b) : ℂ) - forwardQuotient δ x := by
    exact_mod_cast hval
  rw [hvalc]
  exact_mod_cast hb.sub hf

theorem hasSum_lowerCoeff (δ b x : ℝ) :
    HasSum (fun h : ℤ => lowerCoeff δ b h * fourier h (x : UnitAddCircle))
      (lowerEnvelope δ b x - (b - δ)) := by
  have hf := hasSum_forwardCoeff δ (x - b)
  have hb := hasSum_backwardCoeff δ x
  have heq : (fun h : ℤ => lowerCoeff δ b h * fourier h (x : UnitAddCircle)) =
      (fun h : ℤ => forwardCoeff δ h * fourier h ((x - b : ℝ) : UnitAddCircle) -
        backwardCoeff δ h * fourier h (x : UnitAddCircle)) := by
    funext h
    rw [lowerCoeff]
    have hadd : fourier h ((x - b : ℝ) : UnitAddCircle) =
        fourier h ((-b : ℝ) : UnitAddCircle) * fourier h (x : UnitAddCircle) := by
      simpa only [sub_eq_add_neg] using fourier_coe_add h x (-b)
    rw [hadd]
    ring
  rw [heq]
  have hval : lowerEnvelope δ b x - (b - δ) =
      forwardQuotient δ (x - b) - backwardQuotient δ x := by
    unfold lowerEnvelope
    ring
  have hvalc : (lowerEnvelope δ b x : ℂ) - ((b : ℂ) - δ) =
      (forwardQuotient δ (x - b) : ℂ) - backwardQuotient δ x := by
    exact_mod_cast hval
  rw [hvalc]
  exact_mod_cast hf.sub hb

/-! ## Coefficient estimates -/

@[simp]
theorem norm_fourier_apply (h : ℤ) (x : UnitAddCircle) : ‖fourier h x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem norm_fourier_sub_one_le (h : ℤ) (x : ℝ) :
    ‖fourier h (x : UnitAddCircle) - 1‖ ≤
      2 * Real.pi * |(h : ℝ)| * |x| := by
  rw [fourier_coe_apply]
  have ht := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (h : ℝ) * x)
  convert ht using 1
  · congr 3
    push_cast
    ring
  · simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem norm_b₂Coeff_le (h : ℤ) (hh : h ≠ 0) :
    ‖b₂Coeff h‖ ≤ ((h : ℝ) ^ 2)⁻¹ := by
  rw [b₂Coeff, norm_div, norm_neg, norm_pow]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  simp only [Real.norm_of_nonneg Real.pi_pos.le]
  norm_num
  have hhabs : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  have hpi : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
  calc
    2 / (2 * Real.pi * |(h : ℝ)|) ^ 2 =
        1 / ((2 * Real.pi * |(h : ℝ)|) ^ 2 / 2) := by field_simp
    _ ≤ 1 / |(h : ℝ)| ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg ((Real.pi - 1) * |(h : ℝ)|)]
    _ = ((h : ℝ) ^ 2)⁻¹ := by rw [one_div, sq_abs]

theorem norm_forwardCoeff_le_harmonic (δ : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖forwardCoeff δ h‖ ≤ 4 / |(h : ℝ)| := by
  rw [forwardCoeff, norm_div, norm_mul]
  norm_num [Real.norm_eq_abs, abs_of_pos hδ]
  have hc := norm_b₂Coeff_le h hh
  have he := norm_fourier_sub_one_le h δ
  have he' : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * h * δ) - 1‖ ≤
      2 * Real.pi * |(h : ℝ)| * δ := by
    simpa [fourier_coe_apply, abs_of_pos hδ] using he
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  calc
    _ ≤ ((h : ℝ) ^ 2)⁻¹ * (2 * Real.pi * |(h : ℝ)| * δ) / (2 * δ) := by
      gcongr
    _ = Real.pi / |(h : ℝ)| := by rw [← sq_abs]; field_simp
    _ ≤ 4 / |(h : ℝ)| := by gcongr

theorem norm_backwardCoeff_le_harmonic (δ : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖backwardCoeff δ h‖ ≤ 4 / |(h : ℝ)| := by
  have he := norm_fourier_sub_one_le h (-δ)
  have heback : ‖1 - fourier h ((-δ : ℝ) : UnitAddCircle)‖ ≤
      2 * Real.pi * |(h : ℝ)| * δ := by
    rw [norm_sub_rev]
    simpa [abs_of_pos hδ] using he
  rw [backwardCoeff, norm_div, norm_mul]
  norm_num [Real.norm_eq_abs, abs_of_pos hδ]
  have hc := norm_b₂Coeff_le h hh
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  calc
    _ ≤ ((h : ℝ) ^ 2)⁻¹ * (2 * Real.pi * |(h : ℝ)| * δ) / (2 * δ) := by
      gcongr
      simpa [fourier_coe_apply] using heback
    _ = Real.pi / |(h : ℝ)| := by rw [← sq_abs]; field_simp
    _ ≤ 4 / |(h : ℝ)| := by gcongr

theorem norm_upperCoeff_le_harmonic (δ b : ℝ) (h : ℤ)
    (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖upperCoeff δ b h‖ ≤ 8 / |(h : ℝ)| := by
  rw [upperCoeff]
  calc
    _ ≤ ‖backwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle)‖ +
        ‖forwardCoeff δ h‖ := norm_sub_le _ _
    _ = ‖backwardCoeff δ h‖ + ‖forwardCoeff δ h‖ := by
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 4 / |(h : ℝ)| + 4 / |(h : ℝ)| :=
      add_le_add (norm_backwardCoeff_le_harmonic δ h hδ hh)
        (norm_forwardCoeff_le_harmonic δ h hδ hh)
    _ = 8 / |(h : ℝ)| := by ring

theorem norm_lowerCoeff_le_harmonic (δ b : ℝ) (h : ℤ)
    (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖lowerCoeff δ b h‖ ≤ 8 / |(h : ℝ)| := by
  rw [lowerCoeff]
  calc
    _ ≤ ‖forwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle)‖ +
        ‖backwardCoeff δ h‖ := norm_sub_le _ _
    _ = ‖forwardCoeff δ h‖ + ‖backwardCoeff δ h‖ := by
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 4 / |(h : ℝ)| + 4 / |(h : ℝ)| :=
      add_le_add (norm_forwardCoeff_le_harmonic δ h hδ hh)
        (norm_backwardCoeff_le_harmonic δ h hδ hh)
    _ = 8 / |(h : ℝ)| := by ring

/-! ## An explicit square-series tail -/

theorem nat_square_tail (H : ℕ) (hH : 1 ≤ H) :
    (∑' n : ℕ, 1 / (((n + H + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 / (H : ℝ) := by
  let b : ℕ → ℝ := fun n ↦ (((n + H : ℕ) : ℝ))⁻¹
  have hb_nonneg (n : ℕ) : 0 ≤ b n - b (n + 1) := by
    apply sub_nonneg.mpr
    dsimp [b]
    have hpos : (0 : ℝ) < (n + H : ℕ) := by positivity
    have hle : ((n + H : ℕ) : ℝ) ≤ (n + 1 + H : ℕ) := by norm_cast; omega
    simpa only [one_div] using one_div_le_one_div_of_le hpos hle
  have hb_lim : Tendsto b atTop (nhds 0) := by
    dsimp [b]
    simpa only using
      ((tendsto_add_atTop_iff_nat H).2 (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have htel : HasSum (fun n : ℕ ↦ b n - b (n + 1)) (1 / (H : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hb_nonneg]
    simpa only [Finset.sum_range_sub', b, Nat.zero_add, one_div, sub_zero] using
      ((tendsto_const_nhds (x := b 0)).sub hb_lim)
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs_tail : Summable (fun n : ℕ ↦ 1 / (((n + H + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      ((summable_nat_add_iff (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) (H + 1)).2 hs)
  rw [← htel.tsum_eq]
  apply Summable.tsum_le_tsum (f := fun n : ℕ ↦ 1 / (((n + H + 1 : ℕ) : ℝ) ^ 2))
    (g := fun n : ℕ ↦ b n - b (n + 1)) _ hs_tail htel.summable
  intro n
  dsimp [b]
  have hm : (0 : ℝ) < (n + H : ℕ) := by positivity
  have hm1 : (0 : ℝ) < (n + H + 1 : ℕ) := by positivity
  push_cast at hm hm1 ⊢
  field_simp
  nlinarith

theorem int_square_tail (H : ℕ) (hH : 1 ≤ H) :
    (∑' h : ℤ, if H < h.natAbs then 1 / ((h : ℝ) ^ 2) else 0) ≤ 2 / (H : ℝ) := by
  let f : ℤ → ℝ := fun h ↦ if H < h.natAbs then 1 / ((h : ℝ) ^ 2) else 0
  let gp : ℕ → ℝ := fun n ↦ if H < n then 1 / ((n : ℝ) ^ 2) else 0
  let gn : ℕ → ℝ := fun n ↦ if H < n + 1 then 1 / (((n + 1 : ℕ) : ℝ) ^ 2) else 0
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs_one : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only using ((summable_nat_add_iff
      (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) 1).2 hs)
  have hgp : Summable gp := by
    apply (hs.indicator {n : ℕ | H < n}).congr
    intro n
    by_cases hn : H < n <;> simp [gp, hn]
  have hgn : Summable gn := by
    apply (hs_one.indicator {n : ℕ | H < n + 1}).congr
    intro n
    simp [Set.indicator_apply, gn]
  have hfp (n : ℕ) : f n = gp n := by simp [f, gp]
  have hfn (n : ℕ) : f (Int.negSucc n) = gn n := by
    by_cases hn : H < n + 1
    · simp only [f, Int.natAbs_negSucc, if_pos hn, gn]
      push_cast
      ring
    · simp only [f, Int.natAbs_negSucc, if_neg hn, gn]
  have hpos : Summable (fun n : ℕ ↦ f n) := hgp.congr (fun n ↦ (hfp n).symm)
  have hneg : Summable (fun n : ℕ ↦ f (-(n + 1))) := by
    simpa only [Int.negSucc_eq] using hgn.congr (fun n ↦ (hfn n).symm)
  have hgp_eq : (∑' n : ℕ, gp n) =
      ∑' n : ℕ, 1 / (((n + H + 1 : ℕ) : ℝ) ^ 2) := by
    have hsplit := hgp.sum_add_tsum_nat_add (H + 1)
    rw [show ∑ i ∈ Finset.range (H + 1), gp i = 0 by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_range] at hi
      have hnot : ¬ H < i := by omega
      rw [show gp i = 0 by simp only [gp, if_neg hnot]]] at hsplit
    have hshift (n : ℕ) : gp (n + (H + 1)) =
        1 / (((n + H + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [gp]
      rw [if_pos (by omega)]
      push_cast
      ring
    rw [tsum_congr hshift] at hsplit
    simpa only [zero_add] using hsplit.symm
  have hgn_eq : (∑' n : ℕ, gn n) =
      ∑' n : ℕ, 1 / (((n + H + 1 : ℕ) : ℝ) ^ 2) := by
    have hsplit := hgn.sum_add_tsum_nat_add H
    rw [show ∑ i ∈ Finset.range H, gn i = 0 by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_range] at hi
      have hnot : ¬ H < i + 1 := by omega
      rw [show gn i = 0 by simp only [gn, if_neg hnot]]] at hsplit
    have hshift (n : ℕ) : gn (n + H) =
        1 / (((n + H + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [gn]
      rw [if_pos (by omega)]
    rw [tsum_congr hshift] at hsplit
    simpa only [zero_add] using hsplit.symm
  rw [show (∑' h : ℤ, if H < h.natAbs then 1 / ((h : ℝ) ^ 2) else 0) =
      ∑' h : ℤ, f h by rfl]
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  rw [tsum_congr hfp]
  rw [show (∑' n : ℕ, f (-(n + 1))) = ∑' n : ℕ, gn n by
    apply tsum_congr
    intro n
    simpa only [Int.negSucc_eq] using hfn n]
  rw [hgp_eq, hgn_eq]
  have htail := nat_square_tail H hH
  calc
    _ ≤ 1 / (H : ℝ) + 1 / (H : ℝ) := add_le_add htail htail
    _ = 2 / (H : ℝ) := by ring

theorem int_square_tail_subtype (H : ℕ) (hH : 1 ≤ H) :
    (∑' h : {h : ℤ // H < h.natAbs}, 1 / (((h : ℤ) : ℝ) ^ 2)) ≤ 2 / (H : ℝ) := by
  calc
    _ = ∑' h : ℤ, ({h : ℤ | H < h.natAbs}.indicator
        (fun h : ℤ ↦ 1 / ((h : ℝ) ^ 2))) h := tsum_subtype _ _
    _ ≤ 2 / (H : ℝ) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using int_square_tail H hH

theorem norm_forwardCoeff_le_square (δ : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖forwardCoeff δ h‖ ≤ 1 / (δ * (h : ℝ) ^ 2) := by
  have hc := norm_b₂Coeff_le h hh
  have he : ‖fourier h (δ : UnitAddCircle) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier h (δ : UnitAddCircle)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_fourier_apply]; norm_num
  have he' : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * h * δ) - 1‖ ≤ 2 := by
    simpa [fourier_coe_apply] using he
  rw [forwardCoeff, norm_div, norm_mul]
  norm_num [Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ ((h : ℝ) ^ 2)⁻¹ * 2 / (2 * δ) := by gcongr
    _ = ((h : ℝ) ^ 2)⁻¹ * δ⁻¹ := by
      field_simp [hδ.ne', (by exact_mod_cast hh : (h : ℝ) ≠ 0)]

theorem norm_backwardCoeff_le_square (δ : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖backwardCoeff δ h‖ ≤ 1 / (δ * (h : ℝ) ^ 2) := by
  have hc := norm_b₂Coeff_le h hh
  have he : ‖1 - fourier h ((-δ : ℝ) : UnitAddCircle)‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖fourier h ((-δ : ℝ) : UnitAddCircle)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_fourier_apply]; norm_num
  have he' : ‖1 - (starRingEnd ℂ) (Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * h * δ))‖ ≤ 2 := by
    simpa [fourier_coe_apply] using he
  rw [backwardCoeff, norm_div, norm_mul]
  norm_num [Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ ((h : ℝ) ^ 2)⁻¹ * 2 / (2 * δ) := by gcongr
    _ = ((h : ℝ) ^ 2)⁻¹ * δ⁻¹ := by
      field_simp [hδ.ne', (by exact_mod_cast hh : (h : ℝ) ≠ 0)]

theorem norm_upperCoeff_le_square (δ b : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖upperCoeff δ b h‖ ≤ 2 / (δ * (h : ℝ) ^ 2) := by
  rw [upperCoeff]
  calc
    _ ≤ ‖backwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle)‖ +
        ‖forwardCoeff δ h‖ := norm_sub_le _ _
    _ = ‖backwardCoeff δ h‖ + ‖forwardCoeff δ h‖ := by
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 1 / (δ * (h : ℝ) ^ 2) + 1 / (δ * (h : ℝ) ^ 2) :=
      add_le_add (norm_backwardCoeff_le_square δ h hδ hh)
        (norm_forwardCoeff_le_square δ h hδ hh)
    _ = 2 / (δ * (h : ℝ) ^ 2) := by ring

theorem norm_lowerCoeff_le_square (δ b : ℝ) (h : ℤ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ‖lowerCoeff δ b h‖ ≤ 2 / (δ * (h : ℝ) ^ 2) := by
  rw [lowerCoeff]
  calc
    _ ≤ ‖forwardCoeff δ h * fourier h ((-b : ℝ) : UnitAddCircle)‖ +
        ‖backwardCoeff δ h‖ := norm_sub_le _ _
    _ = ‖forwardCoeff δ h‖ + ‖backwardCoeff δ h‖ := by
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 1 / (δ * (h : ℝ) ^ 2) + 1 / (δ * (h : ℝ) ^ 2) :=
      add_le_add (norm_forwardCoeff_le_square δ h hδ hh)
        (norm_backwardCoeff_le_square δ h hδ hh)
    _ = 2 / (δ * (h : ℝ) ^ 2) := by ring

/-- The symmetric frequency window `|h| ≤ H`. -/
def frequencyWindow (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ)

theorem mem_frequencyWindow_iff (H : ℕ) (h : ℤ) :
    h ∈ frequencyWindow H ↔ h.natAbs ≤ H := by
  simp only [frequencyWindow, Finset.mem_Icc]
  rcases Int.natAbs_eq h with hh | hh
  · constructor
    · intro hb
      have hc : (h.natAbs : ℤ) ≤ (H : ℤ) := hh.symm.le.trans hb.2
      exact_mod_cast hc
    · intro ha
      have hc : (h.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast ha
      constructor
      · rw [hh]; omega
      · exact hh.le.trans hc
  · constructor
    · intro hb
      have hc : (h.natAbs : ℤ) ≤ (H : ℤ) := by
        have ht := hb.1
        rw [hh] at ht
        omega
      exact_mod_cast hc
    · intro ha
      have hc : (h.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast ha
      constructor <;> rw [hh] <;> omega

private def outsideWindowEquiv (H : ℕ) :
    {h : ℤ // h ∉ frequencyWindow H} ≃ {h : ℤ // H < h.natAbs} :=
  Equiv.subtypeEquivRight fun h => by
    rw [mem_frequencyWindow_iff]
    omega

theorem upperCoeff_tail (H : ℕ) (δ b : ℝ) (hH : 1 ≤ H) (hδ : 0 < δ) :
    (∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖upperCoeff δ b h‖) ≤
      4 / (δ * H) := by
  let e := outsideWindowEquiv H
  have hsbase : Summable (fun h : ℤ => 1 / ((h : ℝ) ^ 2)) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hsrhs : Summable (fun h : {h : ℤ // h ∉ frequencyWindow H} =>
      2 / (δ * ((h : ℤ) : ℝ) ^ 2)) := by
    have hs0 := hsbase.subtype (fun h => h ∉ frequencyWindow H)
    apply (Summable.mul_left (2 / δ) hs0).congr
    intro h
    dsimp only [Function.comp_apply]
    field_simp [hδ.ne']
  have hcoeff : Summable (fun h : {h : ℤ // h ∉ frequencyWindow H} =>
      ‖upperCoeff δ b h‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsrhs
    intro h
    exact norm_upperCoeff_le_square δ b h hδ (by
      intro hz
      apply h.property
      rw [show (h : ℤ) = 0 from hz]
      simp [frequencyWindow])
  calc
    _ ≤ ∑' h : {h : ℤ // h ∉ frequencyWindow H},
        2 / (δ * (((h : ℤ) : ℝ) ^ 2)) :=
      hcoeff.tsum_le_tsum (fun h => norm_upperCoeff_le_square δ b h hδ (by
        intro hz
        apply h.property
        rw [show (h : ℤ) = 0 from hz]
        simp [frequencyWindow])) hsrhs
    _ = (2 / δ) * ∑' h : {h : ℤ // h ∉ frequencyWindow H},
        1 / ((((h : ℤ) : ℝ) ^ 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      field_simp [hδ.ne']
    _ = (2 / δ) * ∑' h : {h : ℤ // H < h.natAbs},
        1 / ((((h : ℤ) : ℝ) ^ 2)) := by
      congr 1
      calc
        _ = ∑' h : {h : ℤ // h ∉ frequencyWindow H},
            1 / ((((e h : {h : ℤ // H < h.natAbs}) : ℤ) : ℝ) ^ 2) := by
          apply tsum_congr
          intro h
          rfl
        _ = _ := e.tsum_eq (fun h : {h : ℤ // H < h.natAbs} =>
          1 / ((((h : ℤ) : ℝ) ^ 2)))
    _ ≤ (2 / δ) * (2 / (H : ℝ)) := by
      gcongr
      exact int_square_tail_subtype H hH
    _ = 4 / (δ * H) := by field_simp [hδ.ne']; ring

theorem lowerCoeff_tail (H : ℕ) (δ b : ℝ) (hH : 1 ≤ H) (hδ : 0 < δ) :
    (∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖lowerCoeff δ b h‖) ≤
      4 / (δ * H) := by
  let e := outsideWindowEquiv H
  have hsbase : Summable (fun h : ℤ => 1 / ((h : ℝ) ^ 2)) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hsrhs : Summable (fun h : {h : ℤ // h ∉ frequencyWindow H} =>
      2 / (δ * ((h : ℤ) : ℝ) ^ 2)) := by
    have hs0 := hsbase.subtype (fun h => h ∉ frequencyWindow H)
    apply (Summable.mul_left (2 / δ) hs0).congr
    intro h
    dsimp only [Function.comp_apply]
    field_simp [hδ.ne']
  have hcoeff : Summable (fun h : {h : ℤ // h ∉ frequencyWindow H} =>
      ‖lowerCoeff δ b h‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsrhs
    intro h
    exact norm_lowerCoeff_le_square δ b h hδ (by
      intro hz
      apply h.property
      rw [show (h : ℤ) = 0 from hz]
      simp [frequencyWindow])
  calc
    _ ≤ ∑' h : {h : ℤ // h ∉ frequencyWindow H},
        2 / (δ * (((h : ℤ) : ℝ) ^ 2)) :=
      hcoeff.tsum_le_tsum (fun h => norm_lowerCoeff_le_square δ b h hδ (by
        intro hz
        apply h.property
        rw [show (h : ℤ) = 0 from hz]
        simp [frequencyWindow])) hsrhs
    _ = (2 / δ) * ∑' h : {h : ℤ // h ∉ frequencyWindow H},
        1 / ((((h : ℤ) : ℝ) ^ 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      field_simp [hδ.ne']
    _ = (2 / δ) * ∑' h : {h : ℤ // H < h.natAbs},
        1 / ((((h : ℤ) : ℝ) ^ 2)) := by
      congr 1
      calc
        _ = ∑' h : {h : ℤ // h ∉ frequencyWindow H},
            1 / ((((e h : {h : ℤ // H < h.natAbs}) : ℤ) : ℝ) ^ 2) := by
          apply tsum_congr
          intro h
          rfl
        _ = _ := e.tsum_eq (fun h : {h : ℤ // H < h.natAbs} =>
          1 / ((((h : ℤ) : ℝ) ^ 2)))
    _ ≤ (2 / δ) * (2 / (H : ℝ)) := by
      gcongr
      exact int_square_tail_subtype H hH
    _ = 4 / (δ * H) := by field_simp [hδ.ne']; ring

/-- The finite upper trigonometric polynomial. -/
def upperPolynomial (H : ℕ) (δ b x : ℝ) : ℝ :=
  (∑ h ∈ frequencyWindow H,
    upperCoeff δ b h * fourier h (x : UnitAddCircle)).re

/-- The finite lower trigonometric polynomial. -/
def lowerPolynomial (H : ℕ) (δ b x : ℝ) : ℝ :=
  (∑ h ∈ frequencyWindow H,
    lowerCoeff δ b h * fourier h (x : UnitAddCircle)).re

theorem norm_upperEnvelope_sub_sum_le (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) :
    ‖(upperEnvelope δ b x : ℂ) - ((b : ℂ) + δ) -
        ∑ h ∈ frequencyWindow H,
          upperCoeff δ b h * fourier h (x : UnitAddCircle)‖ ≤
      4 / (δ * H) := by
  let term : ℤ → ℂ := fun h => upperCoeff δ b h * fourier h (x : UnitAddCircle)
  have hs := hasSum_upperCoeff δ b x
  have hsum : Summable term := hs.summable
  have hdecomp := hsum.sum_add_tsum_subtype_compl (frequencyWindow H)
  have htotal : (∑' h : ℤ, term h) =
      (upperEnvelope δ b x : ℂ) - ((b : ℂ) + δ) := hs.tsum_eq
  have hremainder :
      (upperEnvelope δ b x : ℂ) - ((b : ℂ) + δ) -
          ∑ h ∈ frequencyWindow H, term h =
        ∑' h : {h : ℤ // h ∉ frequencyWindow H}, term h := by
    rw [← htotal, ← hdecomp]
    ring
  rw [hremainder]
  calc
    _ ≤ ∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖term h‖ :=
      norm_tsum_le_tsum_norm ((hsum.norm.subtype fun h => h ∉ frequencyWindow H))
    _ = ∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖upperCoeff δ b h‖ := by
      apply tsum_congr
      intro h
      change ‖upperCoeff δ b h * fourier h (x : UnitAddCircle)‖ = ‖upperCoeff δ b h‖
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 4 / (δ * H) := upperCoeff_tail H δ b hH hδ

theorem norm_lowerEnvelope_sub_sum_le (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) :
    ‖(lowerEnvelope δ b x : ℂ) - ((b : ℂ) - δ) -
        ∑ h ∈ frequencyWindow H,
          lowerCoeff δ b h * fourier h (x : UnitAddCircle)‖ ≤
      4 / (δ * H) := by
  let term : ℤ → ℂ := fun h => lowerCoeff δ b h * fourier h (x : UnitAddCircle)
  have hs := hasSum_lowerCoeff δ b x
  have hsum : Summable term := hs.summable
  have hdecomp := hsum.sum_add_tsum_subtype_compl (frequencyWindow H)
  have htotal : (∑' h : ℤ, term h) =
      (lowerEnvelope δ b x : ℂ) - ((b : ℂ) - δ) := hs.tsum_eq
  have hremainder :
      (lowerEnvelope δ b x : ℂ) - ((b : ℂ) - δ) -
          ∑ h ∈ frequencyWindow H, term h =
        ∑' h : {h : ℤ // h ∉ frequencyWindow H}, term h := by
    rw [← htotal, ← hdecomp]
    ring
  rw [hremainder]
  calc
    _ ≤ ∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖term h‖ :=
      norm_tsum_le_tsum_norm ((hsum.norm.subtype fun h => h ∉ frequencyWindow H))
    _ = ∑' h : {h : ℤ // h ∉ frequencyWindow H}, ‖lowerCoeff δ b h‖ := by
      apply tsum_congr
      intro h
      change ‖lowerCoeff δ b h * fourier h (x : UnitAddCircle)‖ = ‖lowerCoeff δ b h‖
      rw [norm_mul, norm_fourier_apply, mul_one]
    _ ≤ 4 / (δ * H) := lowerCoeff_tail H δ b hH hδ

theorem abs_upperEnvelope_sub_polynomial_le (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) :
    |upperEnvelope δ b x - (b + δ) - upperPolynomial H δ b x| ≤
      4 / (δ * H) := by
  let z : ℂ := (upperEnvelope δ b x : ℂ) - ((b : ℂ) + δ) -
    ∑ h ∈ frequencyWindow H, upperCoeff δ b h * fourier h (x : UnitAddCircle)
  have hz := norm_upperEnvelope_sub_sum_le H δ b x hH hδ
  have hre : z.re = upperEnvelope δ b x - (b + δ) - upperPolynomial H δ b x := by
    simp [z, upperPolynomial]
  rw [← hre]
  exact (Complex.abs_re_le_norm z).trans hz

theorem abs_lowerEnvelope_sub_polynomial_le (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) :
    |lowerEnvelope δ b x - (b - δ) - lowerPolynomial H δ b x| ≤
      4 / (δ * H) := by
  let z : ℂ := (lowerEnvelope δ b x : ℂ) - ((b : ℂ) - δ) -
    ∑ h ∈ frequencyWindow H, lowerCoeff δ b h * fourier h (x : UnitAddCircle)
  have hz := norm_lowerEnvelope_sub_sum_le H δ b x hH hδ
  have hre : z.re = lowerEnvelope δ b x - (b - δ) - lowerPolynomial H δ b x := by
    simp [z, lowerPolynomial]
  rw [← hre]
  exact (Complex.abs_re_le_norm z).trans hz

theorem intervalIndicator_le_upperPolynomial (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (if Int.fract x < b then (1 : ℝ) else 0) ≤
      b + δ + 4 / (δ * H) + upperPolynomial H δ b x := by
  have hi := intervalIndicator_le_upperEnvelope x b δ hb0 hb1 hδ hδ1
  have ha := abs_upperEnvelope_sub_polynomial_le H δ b x hH hδ
  rw [abs_le] at ha
  linarith

theorem lowerPolynomial_le_intervalIndicator (H : ℕ) (δ b x : ℝ)
    (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b - δ - 4 / (δ * H) + lowerPolynomial H δ b x ≤
      (if Int.fract x < b then (1 : ℝ) else 0) := by
  have hi := lowerEnvelope_le_intervalIndicator x b δ hb0 hb1 hδ hδ1
  have ha := abs_lowerEnvelope_sub_polynomial_le H δ b x hH hδ
  rw [abs_le] at ha
  linarith

/-- Exponential sum over an arbitrary finite family of real phases. -/
def exponentialSum {ι : Type*} (s : Finset ι) (phase : ι → ℝ) (h : ℤ) : ℂ :=
  ∑ i ∈ s, fourier h (phase i : UnitAddCircle)

@[simp]
theorem upperCoeff_zero (δ b : ℝ) : upperCoeff δ b 0 = 0 := by
  simp [upperCoeff, backwardCoeff, forwardCoeff, b₂Coeff]

@[simp]
theorem lowerCoeff_zero (δ b : ℝ) : lowerCoeff δ b 0 = 0 := by
  simp [lowerCoeff, backwardCoeff, forwardCoeff, b₂Coeff]

/-- The nonzero modes in the symmetric frequency window. -/
def nonzeroFrequencyWindow (H : ℕ) : Finset ℤ := (frequencyWindow H).erase 0

theorem sum_upperPolynomial {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) :
    ∑ i ∈ s, upperPolynomial H δ b (phase i) =
      (∑ h ∈ nonzeroFrequencyWindow H,
        upperCoeff δ b h * exponentialSum s phase h).re := by
  classical
  rw [nonzeroFrequencyWindow, Finset.sum_erase (frequencyWindow H)
    (show upperCoeff δ b 0 * exponentialSum s phase 0 = 0 by simp)]
  simp_rw [upperPolynomial, exponentialSum, Complex.re_sum, mul_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]

theorem sum_lowerPolynomial {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) :
    ∑ i ∈ s, lowerPolynomial H δ b (phase i) =
      (∑ h ∈ nonzeroFrequencyWindow H,
        lowerCoeff δ b h * exponentialSum s phase h).re := by
  classical
  rw [nonzeroFrequencyWindow, Finset.sum_erase (frequencyWindow H)
    (show lowerCoeff δ b 0 * exponentialSum s phase 0 = 0 by simp)]
  simp_rw [lowerPolynomial, exponentialSum, Complex.re_sum, mul_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]

theorem abs_sum_upperPolynomial_le {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) (hδ : 0 < δ) :
    |∑ i ∈ s, upperPolynomial H δ b (phase i)| ≤
      ∑ h ∈ nonzeroFrequencyWindow H,
        8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
  classical
  rw [sum_upperPolynomial]
  calc
    _ ≤ ‖∑ h ∈ nonzeroFrequencyWindow H,
        upperCoeff δ b h * exponentialSum s phase h‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ h ∈ nonzeroFrequencyWindow H,
        ‖upperCoeff δ b h * exponentialSum s phase h‖ := norm_sum_le _ _
    _ = ∑ h ∈ nonzeroFrequencyWindow H,
        ‖upperCoeff δ b h‖ * ‖exponentialSum s phase h‖ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul]
    _ ≤ ∑ h ∈ nonzeroFrequencyWindow H,
        8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
      gcongr with h hh
      exact norm_upperCoeff_le_harmonic δ b h hδ (by
        exact Finset.ne_of_mem_erase hh)

theorem abs_sum_lowerPolynomial_le {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) (hδ : 0 < δ) :
    |∑ i ∈ s, lowerPolynomial H δ b (phase i)| ≤
      ∑ h ∈ nonzeroFrequencyWindow H,
        8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
  classical
  rw [sum_lowerPolynomial]
  calc
    _ ≤ ‖∑ h ∈ nonzeroFrequencyWindow H,
        lowerCoeff δ b h * exponentialSum s phase h‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ h ∈ nonzeroFrequencyWindow H,
        ‖lowerCoeff δ b h * exponentialSum s phase h‖ := norm_sum_le _ _
    _ = ∑ h ∈ nonzeroFrequencyWindow H,
        ‖lowerCoeff δ b h‖ * ‖exponentialSum s phase h‖ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul]
    _ ≤ ∑ h ∈ nonzeroFrequencyWindow H,
        8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
      gcongr with h hh
      exact norm_lowerCoeff_le_harmonic δ b h hδ (by
        exact Finset.ne_of_mem_erase hh)

/-- A quantitative Erdős--Turán inequality for the anchored half-open interval
`[0,b)`.  The smoothing width `δ` is left explicit; taking `δ = H⁻¹/²`
gives an error of order `H⁻¹/²`, while the Fourier weights are the standard
harmonic weights and are independent of `δ`. -/
theorem erdosTuran_fract_count {ι : Type*} (s : Finset ι) (phase : ι → ℝ)
    (H : ℕ) (δ b : ℝ) (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |((s.filter fun i => Int.fract (phase i) < b).card : ℝ) - b * s.card| ≤
      (δ + 4 / (δ * H)) * s.card +
        ∑ h ∈ nonzeroFrequencyWindow H,
          8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
  classical
  let E : ℝ := ∑ h ∈ nonzeroFrequencyWindow H,
    8 / |(h : ℝ)| * ‖exponentialSum s phase h‖
  have hE0 : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro h hh
    have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
    positivity
  have hcount : ∑ i ∈ s, (if Int.fract (phase i) < b then (1 : ℝ) else 0) =
      ((s.filter fun i => Int.fract (phase i) < b).card : ℝ) := by
    simp
  have hu0 : ∑ i ∈ s, (if Int.fract (phase i) < b then (1 : ℝ) else 0) ≤
      ∑ i ∈ s, (b + δ + 4 / (δ * H) + upperPolynomial H δ b (phase i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact intervalIndicator_le_upperPolynomial H δ b (phase i) hH hδ hδ1 hb0 hb1
  have hl0 : ∑ i ∈ s, (b - δ - 4 / (δ * H) + lowerPolynomial H δ b (phase i)) ≤
      ∑ i ∈ s, (if Int.fract (phase i) < b then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro i hi
    exact lowerPolynomial_le_intervalIndicator H δ b (phase i) hH hδ hδ1 hb0 hb1
  rw [hcount] at hu0 hl0
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hu0 hl0
  have hup := abs_sum_upperPolynomial_le s phase H δ b hδ
  have hlp := abs_sum_lowerPolynomial_le s phase H δ b hδ
  change |∑ i ∈ s, upperPolynomial H δ b (phase i)| ≤ E at hup
  change |∑ i ∈ s, lowerPolynomial H δ b (phase i)| ≤ E at hlp
  rw [abs_le] at hup hlp ⊢
  constructor <;> nlinarith

end

end Erdos1149.ErdosTuran
