/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos88.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 88: Esseen smoothing inequalities

This file formalizes Theorem 4.7 and Lemmas 6.1--6.3 of
Kwan--Sah--Sauermann--Sawhney.  We use the same explicit smoothing kernel as
the paper.  Its frequency-side form is the triangle

`1_[−1,1] * 1_[−1,1]`,

and its physical-side form is `4 * sinc x ^ 2`.  The former is supported on
`[−2,2]`; the latter is nonnegative, is at least one on `[−1,1]`, and is
bounded by `min 4 (4/x²)`, hence by `8/(1+x²)`.

The statements are made for probability measures on `ℝ`.  A random
variable is used by applying them to its push-forward law.  Thus the results
cover both the finite Boolean-cube variables occurring in the graph proof and
the continuous Gaussian comparison variables.
-/

open Complex MeasureTheory Set
open scoped FourierTransform Interval

namespace Erdos88
namespace Esseen

noncomputable section

/-! ## Finite uniform laws -/

/-- The push-forward to `ℝ` of the uniform probability law on a nonempty
finite type.  This is the measure-theoretic realization of the normalized
finite expectations used throughout the discrete parts of the development. -/
noncomputable def finiteUniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : Measure ℝ := by
  letI : MeasurableSpace Ω := ⊤
  exact Measure.map X (PMF.uniformOfFintype Ω).toMeasure

noncomputable instance finiteUniformLaw_isProbabilityMeasure
    (Ω : Type*) [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    IsProbabilityMeasure (finiteUniformLaw Ω X) := by
  unfold finiteUniformLaw
  let _ : MeasurableSpace Ω := ⊤
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The characteristic function of `finiteUniformLaw` is exactly the
normalized finite characteristic function. -/
lemma charFun_finiteUniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) :
    charFun (finiteUniformLaw Ω X) t = Fourier.finCharFun Ω X t := by
  rw [charFun_apply_real]
  unfold finiteUniformLaw Fourier.finCharFun Fourier.finExpectation
  let _ : MeasurableSpace Ω := ⊤
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  simp_rw [Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  change (∑ ω, ((Fintype.card Ω : ℝ)⁻¹ : ℂ) *
      Complex.exp (((t : ℂ) * (X ω : ℂ)) * Complex.I)) = _
  have hsum :
      (∑ ω, Complex.exp (((t : ℂ) * (X ω : ℂ)) * Complex.I)) =
        ∑ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro ω _hω
    congr 1
    push_cast
    ring
  rw [← Finset.mul_sum, hsum, div_eq_mul_inv]
  have hexp :
      (∑ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I)) =
        ∑ ω, Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro ω _hω
    rw [mul_comm]
  rw [hexp]
  have hcast : (((Fintype.card Ω : ℝ) : ℂ)) =
      (Fintype.card Ω : ℂ) := by norm_cast
  rw [hcast]
  ring

/-- The probability of a closed interval of radius `eps` about `x`. -/
def smallBall (mu : Measure ℝ) (eps x : ℝ) : ℝ :=
  mu.real (Icc (x - eps) (x + eps))

/-- Closed-interval probabilities under `finiteUniformLaw` are exactly the
corresponding normalized finite counts. -/
lemma smallBall_finiteUniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps x : ℝ) :
    smallBall (finiteUniformLaw Ω X) eps x =
      Fourier.finProbability Ω (fun ω ↦ |X ω - x| ≤ eps) := by
  classical
  unfold smallBall finiteUniformLaw Fourier.finProbability
  let _ : MeasurableSpace Ω := ⊤
  rw [measureReal_def]
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 1
  have hset : X ⁻¹' Icc (x - eps) (x + eps) =
      (↑((Finset.univ : Finset Ω).filter fun ω ↦
        |X ω - x| ≤ eps) : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Icc, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [abs_le]
    constructor
    · intro h
      constructor <;> linarith
    · intro h
      constructor <;> linarith
  exact_mod_cast (calc
    Fintype.card ↑(X ⁻¹' Icc (x - eps) (x + eps)) =
        Fintype.card
          ↑((Finset.univ : Finset Ω).filter fun ω ↦ |X ω - x| ≤ eps) :=
      Fintype.card_congr (Equiv.setCongr hset)
    _ = ((Finset.univ : Finset Ω).filter fun ω ↦
        |X ω - x| ≤ eps).card := Fintype.card_coe _)

/-- Centering a finite random variable produces the expected unit-modulus
phase in its characteristic function. -/
lemma charFun_finiteUniformLaw_sub_const
    (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (c t : ℝ) :
    charFun (finiteUniformLaw Ω (fun ω ↦ X ω - c)) t =
      Complex.exp (-(((t * c : ℝ) : ℂ) * Complex.I)) *
        Fourier.finCharFun Ω X t := by
  rw [charFun_finiteUniformLaw]
  have hfun : (fun ω ↦ X ω - c) = fun ω ↦ X ω + (-c) := by
    funext ω
    ring
  rw [hfun, Fourier.finCharFun_add_const]
  congr 1
  push_cast
  ring_nf

/-- Translating both a finite random variable and the center of its window
does not change its small-ball probability. -/
lemma smallBall_finiteUniformLaw_sub_const
    (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (c eps x : ℝ) :
    smallBall (finiteUniformLaw Ω (fun ω ↦ X ω - c)) eps (x - c) =
      Fourier.finProbability Ω (fun ω ↦ |X ω - x| ≤ eps) := by
  rw [smallBall_finiteUniformLaw]
  congr 1
  funext ω
  ring_nf

/-- Lévy's concentration function.  We use a supremum over all real centers,
exactly as in KSSS Definition 4.6. -/
def concentration (mu : Measure ℝ) (eps : ℝ) : ℝ :=
  sSup (range fun x : ℝ ↦ smallBall mu eps x)

lemma smallBall_nonneg (mu : Measure ℝ) (eps x : ℝ) :
    0 ≤ smallBall mu eps x := by
  exact measureReal_nonneg

lemma smallBall_le_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps x : ℝ) : smallBall mu eps x ≤ 1 := by
  exact measureReal_le_one

lemma smallBall_mono_radius (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps eps' : ℝ} (heps : eps ≤ eps') (x : ℝ) :
    smallBall mu eps x ≤ smallBall mu eps' x := by
  apply measureReal_mono
  intro y hy
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  finiteness

lemma smallBall_le_concentration (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps x : ℝ) : smallBall mu eps x ≤ concentration mu eps := by
  apply le_csSup
  · exact ⟨1, Set.forall_mem_range.2 (smallBall_le_one mu eps)⟩
  · exact mem_range_self x

lemma concentration_nonneg (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps : ℝ) : 0 ≤ concentration mu eps :=
  (smallBall_nonneg mu eps 0).trans (smallBall_le_concentration mu eps 0)

lemma concentration_le_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps : ℝ) : concentration mu eps ≤ 1 := by
  apply csSup_le (range_nonempty _)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact smallBall_le_one mu eps x

lemma concentration_mono_radius (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps eps' : ℝ} (heps : eps ≤ eps') :
    concentration mu eps ≤ concentration mu eps' := by
  apply csSup_le (range_nonempty _)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact (smallBall_mono_radius mu heps x).trans
    (smallBall_le_concentration mu eps' x)

/-- The Fourier error on the precise interval used by KSSS. -/
def fourierError (mu nu : Measure ℝ) (eps : ℝ) : ℝ :=
  ∫ t in -(2 / eps)..(2 / eps), ‖charFun mu t - charFun nu t‖

/-- The triangular compactly supported frequency kernel. -/
def frequencyKernel (t : ℝ) : ℝ := max 0 (2 - |t|)

/-- The corresponding physical smoothing kernel.  Mathlib's `Real.sinc` is
the unnormalised sinc, with value one at the origin. -/
def smoothingKernel (x : ℝ) : ℝ := 4 * Real.sinc x ^ 2

lemma frequencyKernel_nonneg (t : ℝ) : 0 ≤ frequencyKernel t := by
  simp [frequencyKernel]

lemma frequencyKernel_le_two (t : ℝ) : frequencyKernel t ≤ 2 := by
  rw [frequencyKernel]
  exact max_le (by norm_num) (by linarith [abs_nonneg t])

lemma frequencyKernel_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    frequencyKernel t = 0 := by
  simp [frequencyKernel, ht]

lemma frequencyKernel_eq_two_sub_abs {t : ℝ} (ht : |t| ≤ 2) :
    frequencyKernel t = 2 - |t| := by
  rw [frequencyKernel, max_eq_right]
  linarith

lemma continuous_frequencyKernel : Continuous frequencyKernel := by
  exact continuous_const.max (continuous_const.sub continuous_abs)

lemma intervalIntegrable_frequencyKernel {a b : ℝ} :
    IntervalIntegrable frequencyKernel volume a b :=
  continuous_frequencyKernel.intervalIntegrable _ _

lemma smoothingKernel_nonneg (x : ℝ) : 0 ≤ smoothingKernel x := by
  exact mul_nonneg (by norm_num) (sq_nonneg (Real.sinc x))

lemma continuous_smoothingKernel : Continuous smoothingKernel := by
  exact continuous_const.mul (Real.continuous_sinc.pow 2)

lemma smoothingKernel_le_four (x : ℝ) : smoothingKernel x ≤ 4 := by
  have hs : Real.sinc x ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one (Real.sinc x)).2 (Real.abs_sinc_le_one x)
  rw [smoothingKernel]
  nlinarith

/-- The lower bound used to majorize the indicator of `[-1,1]`. -/
lemma one_le_smoothingKernel {x : ℝ} (hx : |x| ≤ 1) :
    1 ≤ smoothingKernel x := by
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
    linarith [Real.two_le_pi]
  have hsin : (2 / Real.pi : ℝ) * |x| ≤ |Real.sin x| :=
    Real.mul_abs_le_abs_sin (hx.trans hpi)
  have hhalf : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [one_div, div_eq_mul_inv]
    have hp : 0 < Real.pi := Real.pi_pos
    apply (le_div_iff₀ hp).2
    nlinarith [Real.pi_le_four]
  by_cases hx0 : x = 0
  · simp [hx0, smoothingKernel]
  · rw [smoothingKernel, Real.sinc_of_ne_zero hx0]
    have habsx : 0 < |x| := abs_pos.mpr hx0
    have hsinc : (1 / 2 : ℝ) ≤ |Real.sin x / x| := by
      rw [abs_div]
      apply (le_div_iff₀ habsx).2
      calc
        (1 / 2 : ℝ) * |x| ≤ (2 / Real.pi) * |x| :=
          mul_le_mul_of_nonneg_right hhalf (abs_nonneg x)
        _ ≤ |Real.sin x| := hsin
    nlinarith [sq_nonneg (Real.sin x / x), sq_abs (Real.sin x / x)]

lemma smoothingKernel_le_four_div_sq {x : ℝ} (hx : x ≠ 0) :
    smoothingKernel x ≤ 4 / x ^ 2 := by
  rw [smoothingKernel, Real.sinc_of_ne_zero hx]
  have hsin : Real.sin x ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one (Real.sin x)).2 (Real.abs_sin_le_one x)
  have hinv : 0 ≤ (x ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg x)
  rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
  calc
    4 * (Real.sin x ^ 2 * (x ^ 2)⁻¹) ≤ 4 * (1 * (x ^ 2)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsin hinv) (by norm_num)
    _ = 4 * (x ^ 2)⁻¹ := by ring

/-- The summable envelope used in the cell decomposition in Section 6. -/
lemma smoothingKernel_le_eight_div (x : ℝ) :
    smoothingKernel x ≤ 8 / (x ^ 2 + 1) := by
  by_cases hx : |x| ≤ 1
  · have hden : x ^ 2 + 1 ≤ 2 := by
      nlinarith [(sq_le_one_iff_abs_le_one x).2 hx]
    have hpos : 0 < x ^ 2 + 1 := by positivity
    calc
      smoothingKernel x ≤ 4 := smoothingKernel_le_four x
      _ ≤ 8 / (x ^ 2 + 1) := by
        apply (le_div_iff₀ hpos).2
        nlinarith
  · have hx1 : 1 ≤ x ^ 2 := by
      have : 1 < |x| := lt_of_not_ge hx
      nlinarith [sq_abs x]
    have hx0 : x ≠ 0 := by
      intro h
      simp [h] at hx
    have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    calc
      smoothingKernel x ≤ 4 / x ^ 2 := smoothingKernel_le_four_div_sq hx0
      _ ≤ 8 / (x ^ 2 + 1) := by
        apply (div_le_div_iff₀ hxsq (by positivity : 0 < x ^ 2 + 1)).2
        nlinarith


/-- The exact Fourier representation of the KSSS kernel.  This is the
elementary transform identity

`4 sinc(x)^2 = ∫_[-2,2] (2-|t|) exp(-itx) dt`.

Keeping this identity in interval-integral form avoids any convention about
the `2π` normalization of a bundled Fourier transform. -/
lemma smoothingKernel_fourier (x : ℝ) :
    (smoothingKernel x : ℂ) =
      ∫ t in (-2 : ℝ)..2,
        (frequencyKernel t : ℂ) * Complex.exp (-(t * x) * Complex.I) := by
  by_cases hx : x = 0
  · subst x
    simp only [smoothingKernel, Real.sinc_zero, one_pow, mul_one, ofReal_ofNat,
      mul_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    have hleft : (∫ t in (-2 : ℝ)..0, (frequencyKernel t : ℂ)) = 2 := by
      rw [show (∫ t in (-2 : ℝ)..0, (frequencyKernel t : ℂ)) =
          ∫ t in (-2 : ℝ)..0, ((2 + t : ℝ) : ℂ) by
        apply intervalIntegral.integral_congr
        intro t ht
        norm_num [Set.uIcc_of_le] at ht
        change (frequencyKernel t : ℂ) = ((2 + t : ℝ) : ℂ)
        norm_cast
        rw [frequencyKernel_eq_two_sub_abs]
        · simp [abs_of_nonpos ht.2]
        · exact (abs_le).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      rw [intervalIntegral.integral_ofReal]
      have hreal : (∫ t in (-2 : ℝ)..0, (2 + t : ℝ)) = 2 := by
        calc
          (∫ t in (-2 : ℝ)..0, (2 + t : ℝ)) =
              (∫ _t in (-2 : ℝ)..0, (2 : ℝ)) + ∫ t in (-2 : ℝ)..0, t := by
            exact intervalIntegral.integral_add intervalIntegrable_const
              (continuous_id.intervalIntegrable (-2) 0)
          _ = 2 := by norm_num [intervalIntegral.integral_const, integral_id]
      exact_mod_cast hreal
    have hright : (∫ t in (0 : ℝ)..2, (frequencyKernel t : ℂ)) = 2 := by
      rw [show (∫ t in (0 : ℝ)..2, (frequencyKernel t : ℂ)) =
          ∫ t in (0 : ℝ)..2, ((2 - t : ℝ) : ℂ) by
        apply intervalIntegral.integral_congr
        intro t ht
        norm_num [Set.uIcc_of_le] at ht
        change (frequencyKernel t : ℂ) = ((2 - t : ℝ) : ℂ)
        norm_cast
        rw [frequencyKernel_eq_two_sub_abs]
        · simp [abs_of_nonneg ht.1]
        · exact (abs_le).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      rw [intervalIntegral.integral_ofReal]
      have hreal : (∫ t in (0 : ℝ)..2, (2 - t : ℝ)) = 2 := by
        calc
          (∫ t in (0 : ℝ)..2, (2 - t : ℝ)) =
              (∫ _t in (0 : ℝ)..2, (2 : ℝ)) - ∫ t in (0 : ℝ)..2, t := by
            exact intervalIntegral.integral_sub intervalIntegrable_const
              (continuous_id.intervalIntegrable 0 2)
          _ = 2 := by norm_num [intervalIntegral.integral_const, integral_id]
      exact_mod_cast hreal
    have htotal : (4 : ℂ) = ∫ t in (-2 : ℝ)..2, (frequencyKernel t : ℂ) := by
      calc
        (4 : ℂ) = 2 + 2 := by norm_num
        _ = (∫ t in (-2 : ℝ)..0, (frequencyKernel t : ℂ)) +
            ∫ t in (0 : ℝ)..2, (frequencyKernel t : ℂ) := by rw [hleft, hright]
        _ = ∫ t in (-2 : ℝ)..2, (frequencyKernel t : ℂ) :=
          intervalIntegral.integral_add_adjacent_intervals
            ((Complex.continuous_ofReal.comp continuous_frequencyKernel).intervalIntegrable (-2) 0)
            ((Complex.continuous_ofReal.comp continuous_frequencyKernel).intervalIntegrable 0 2)
    convert htotal using 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp
  · have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
    have hleft :
        (∫ t in (-2 : ℝ)..0,
          ((2 + t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)) =
          (2 : ℂ) * Complex.I / x +
            (1 - Complex.exp ((2 * x : ℝ) * Complex.I)) / (x : ℂ) ^ 2 := by
      have hprimitive : ∀ t : ℝ,
          HasDerivAt
            (fun u : ℝ ↦
              Complex.exp (-(u * x) * Complex.I) *
                (((2 + u : ℝ) : ℂ) * Complex.I / x + 1 / (x : ℂ) ^ 2))
            (((2 + t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)) t := by
        intro t
        have hphase : HasDerivAt
            (fun u : ℝ ↦ -((u : ℂ) * (x : ℂ)) * Complex.I)
            (-((x : ℂ)) * Complex.I) t := by
          have hcast : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t :=
            Complex.ofRealCLM.hasDerivAt
          simpa only [Pi.neg_apply, one_mul] using
            (hcast.mul_const (x : ℂ)).neg.mul_const Complex.I
        have hlinear : HasDerivAt (fun u : ℝ ↦ ((2 + u : ℝ) : ℂ)) 1 t :=
          by
            have hcast : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t :=
              Complex.ofRealCLM.hasDerivAt
            simpa only [ofReal_add, ofReal_ofNat] using hcast.const_add (2 : ℂ)
        have hraw := hphase.cexp.mul
          (((hlinear.mul_const Complex.I).div_const (x : ℂ)).add_const
            (1 / (x : ℂ) ^ 2))
        convert hraw using 1 <;> try rfl
        all_goals field_simp [hxC]
        all_goals ring_nf
        all_goals rw [Complex.I_sq]
        all_goals ring
      have hIntegrable : IntervalIntegrable
          (fun t : ℝ ↦ ((2 + t : ℝ) : ℂ) *
            Complex.exp (-(t * x) * Complex.I)) volume (-2) 0 :=
        (((Complex.continuous_ofReal.comp
          (continuous_const.add continuous_id)).mul
            (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)
      have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (-2 : ℝ)) (b := 0) (fun t _ ↦ hprimitive t) hIntegrable
      rw [hInt]
      simp [hxC]
      field_simp [hxC]
      ring
    have hright :
        (∫ t in (0 : ℝ)..2,
          ((2 - t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)) =
          -(2 : ℂ) * Complex.I / x +
            (1 - Complex.exp (-(2 * x : ℝ) * Complex.I)) / (x : ℂ) ^ 2 := by
      have hprimitive : ∀ t : ℝ,
          HasDerivAt
            (fun u : ℝ ↦
              Complex.exp (-(u * x) * Complex.I) *
                (((2 - u : ℝ) : ℂ) * Complex.I / x - 1 / (x : ℂ) ^ 2))
            (((2 - t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)) t := by
        intro t
        have hphase : HasDerivAt
            (fun u : ℝ ↦ -((u : ℂ) * (x : ℂ)) * Complex.I)
            (-((x : ℂ)) * Complex.I) t := by
          have hcast : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t :=
            Complex.ofRealCLM.hasDerivAt
          simpa only [Pi.neg_apply, one_mul] using
            (hcast.mul_const (x : ℂ)).neg.mul_const Complex.I
        have hlinear : HasDerivAt (fun u : ℝ ↦ ((2 - u : ℝ) : ℂ)) (-1) t :=
          by
            have hcast : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t :=
              Complex.ofRealCLM.hasDerivAt
            have hfun : (fun u : ℝ ↦ ((2 - u : ℝ) : ℂ)) =
                fun u : ℝ ↦ (2 : ℂ) + -(u : ℂ) := by
              funext u
              push_cast
              ring
            rw [hfun]
            simpa only [Pi.neg_apply] using hcast.neg.const_add (2 : ℂ)
        have hraw := hphase.cexp.mul
          (((hlinear.mul_const Complex.I).div_const (x : ℂ)).sub_const
            (1 / (x : ℂ) ^ 2))
        convert hraw using 1 <;> try rfl
        all_goals field_simp [hxC]
        all_goals ring_nf
        all_goals rw [Complex.I_sq]
        all_goals ring
      have hIntegrable : IntervalIntegrable
          (fun t : ℝ ↦ ((2 - t : ℝ) : ℂ) *
            Complex.exp (-(t * x) * Complex.I)) volume 0 2 :=
        (((Complex.continuous_ofReal.comp
          (continuous_const.sub continuous_id)).mul
            (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)
      have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 2) (fun t _ ↦ hprimitive t) hIntegrable
      rw [hInt]
      simp [hxC]
      field_simp [hxC]
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := (-2 : ℝ)) (b := 0) (c := 2)]
    · rw [show (∫ t in (-2 : ℝ)..0,
          (frequencyKernel t : ℂ) * Complex.exp (-(t * x) * Complex.I)) =
          ∫ t in (-2 : ℝ)..0,
            ((2 + t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I) by
          apply intervalIntegral.integral_congr
          intro t ht
          norm_num [Set.uIcc_of_le] at ht
          change (frequencyKernel t : ℂ) * Complex.exp (-(t * x) * Complex.I) =
            ((2 + t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)
          congr 1
          change (frequencyKernel t : ℂ) = ((2 + t : ℝ) : ℂ)
          norm_cast
          rw [frequencyKernel_eq_two_sub_abs]
          · simp [abs_of_nonpos ht.2]
          · exact (abs_le).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        show (∫ t in (0 : ℝ)..2,
          (frequencyKernel t : ℂ) * Complex.exp (-(t * x) * Complex.I)) =
          ∫ t in (0 : ℝ)..2,
            ((2 - t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I) by
          apply intervalIntegral.integral_congr
          intro t ht
          norm_num [Set.uIcc_of_le] at ht
          change (frequencyKernel t : ℂ) * Complex.exp (-(t * x) * Complex.I) =
            ((2 - t : ℝ) : ℂ) * Complex.exp (-(t * x) * Complex.I)
          congr 1
          change (frequencyKernel t : ℂ) = ((2 - t : ℝ) : ℂ)
          norm_cast
          rw [frequencyKernel_eq_two_sub_abs]
          · simp [abs_of_nonneg ht.1]
          · exact (abs_le).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        hleft, hright]
      rw [smoothingKernel, Real.sinc_of_ne_zero hx]
      have hneg : Complex.exp (-(2 * x : ℝ) * Complex.I) =
          (Real.cos (2 * x) : ℂ) - (Real.sin (2 * x) : ℂ) * Complex.I := by
        rw [show -((2 * x : ℝ) : ℂ) * Complex.I =
            ((-(2 * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_ofReal_mul_I]
        simp [Real.cos_neg, Real.sin_neg]
        ring
      rw [hneg, Complex.exp_ofReal_mul_I]
      push_cast
      field_simp [hxC]
      ring_nf
      rw [show (x : ℂ) * 2 = 2 * (x : ℂ) by ring]
      rw [Complex.cos_two_mul_eq_one_sub]
      ring
    · exact (((Complex.continuous_ofReal.comp continuous_frequencyKernel).mul
        (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)
    · exact (((Complex.continuous_ofReal.comp continuous_frequencyKernel).mul
        (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)

/-- The expectation of the spatial smoothing kernel at scale `eps`. -/
def kernelAverage (mu : Measure ℝ) (eps x : ℝ) : ℝ :=
  ∫ y, smoothingKernel ((y - x) / eps) ∂mu

lemma integrable_kernelAverage (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps : ℝ} (_heps : eps ≠ 0) (x : ℝ) :
    Integrable (fun y ↦ smoothingKernel ((y - x) / eps)) mu := by
  refine Integrable.mono' (integrable_const (4 : ℝ))
    ((continuous_smoothingKernel.comp (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with y
  simpa only [Real.norm_eq_abs, abs_of_nonneg (smoothingKernel_nonneg _), norm_ofNat] using
    smoothingKernel_le_four ((y - x) / eps)

/-- The spatial kernel majorizes a radius-`eps` interval. -/
lemma smallBall_le_kernelAverage (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    smallBall mu eps x ≤ kernelAverage mu eps x := by
  rw [smallBall, kernelAverage, ← integral_indicator_one measurableSet_Icc]
  apply integral_mono (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc)
    (integrable_kernelAverage mu heps.ne' x)
  intro y
  by_cases hy : y ∈ Icc (x - eps) (x + eps)
  · rw [Set.indicator_of_mem hy]
    apply one_le_smoothingKernel
    rw [abs_div, abs_of_pos heps]
    apply (div_le_one heps).2
    rw [abs_sub_comm]
    rcases hy with ⟨hyL, hyU⟩
    exact (abs_le).2 ⟨by nlinarith, by nlinarith⟩
  · rw [Set.indicator_of_notMem hy]
    exact smoothingKernel_nonneg _

/-- Frequency-side expression for `kernelAverage`. -/
def kernelFourierAverage (mu : Measure ℝ) (eps x : ℝ) : ℂ :=
  ∫ t in (-2 : ℝ)..2,
    (frequencyKernel t : ℂ) *
      Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun mu (-t / eps)

/-- Fubini's theorem applied to the compactly supported smoothing kernel. -/
lemma ofReal_kernelAverage_eq_kernelFourierAverage
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps : ℝ} (heps : eps ≠ 0) (x : ℝ) :
    (kernelAverage mu eps x : ℂ) = kernelFourierAverage mu eps x := by
  rw [kernelAverage, kernelFourierAverage, ← integral_complex_ofReal]
  let : IsFiniteMeasure (volume.restrict (uIoc (-2 : ℝ) 2)) := by
    rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    infer_instance
  let f : ℝ → ℝ → ℂ := fun t y ↦
    (frequencyKernel t : ℂ) *
      Complex.exp (-((t * ((y - x) / eps) : ℝ) : ℂ) * Complex.I)
  have hcont : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry_apply_pair]
    exact
      (Complex.continuous_ofReal.comp (continuous_frequencyKernel.comp continuous_fst)).mul
        (Complex.continuous_exp.comp (by fun_prop))
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := by
    rw [← integrable_norm_iff hcont.aestronglyMeasurable]
    refine Integrable.mono' (integrable_const (2 : ℝ))
      hcont.norm.aestronglyMeasurable ?_
    filter_upwards with p
    change ‖‖f p.1 p.2‖‖ ≤ 2
    dsimp only [f]
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_exp]
    norm_num
    rw [abs_of_nonneg (frequencyKernel_nonneg _)]
    exact frequencyKernel_le_two p.1
  calc
    (∫ (y : ℝ), (smoothingKernel ((y - x) / eps) : ℂ) ∂mu) =
        ∫ (y : ℝ), (∫ (t : ℝ) in (-2 : ℝ)..2, f t y) ∂mu := by
      have hpoint : ∀ y : ℝ,
          (smoothingKernel ((y - x) / eps) : ℂ) =
            ∫ (t : ℝ) in (-2 : ℝ)..2, f t y := by
        intro y
        dsimp only [f]
        convert smoothingKernel_fourier ((y - x) / eps) using 1 <;> norm_cast
      have hint := integral_congr_ae (μ := mu) (Filter.Eventually.of_forall hpoint)
      convert hint using 1 <;> rfl
    _ = ∫ (t : ℝ) in (-2 : ℝ)..2, ∫ (y : ℝ), f t y ∂mu :=
      by
        have hswap := (intervalIntegral_integral_swap (μ := mu) hprod).symm
        convert hswap using 1 <;> rfl
    _ = ∫ (t : ℝ) in (-2 : ℝ)..2,
          (frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun mu (-t / eps) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [f]
      calc
        (∫ (y : ℝ), (frequencyKernel t : ℂ) *
            Complex.exp (-((t * ((y - x) / eps) : ℝ) : ℂ) * Complex.I) ∂mu) =
            (frequencyKernel t : ℂ) *
              ∫ (y : ℝ),
                Complex.exp (-((t * ((y - x) / eps) : ℝ) : ℂ) * Complex.I) ∂mu := by
          rw [integral_const_mul]
        _ = (frequencyKernel t : ℂ) *
            ∫ (y : ℝ),
              Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
                Complex.exp (((-t / eps) * y : ℝ) * Complex.I) ∂mu := by
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          rw [← Complex.exp_add]
          congr 2
          push_cast
          field_simp [heps]
          ring
        _ = (frequencyKernel t : ℂ) *
            (Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
              ∫ (y : ℝ),
                Complex.exp (((-t / eps) * y : ℝ) * Complex.I) ∂mu) := by
          rw [integral_const_mul]
        _ = (frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
              charFun mu (-t / eps) := by
          rw [← mul_assoc, charFun_apply_real]
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          congr 1
          push_cast
          ring

lemma kernelAverage_nonneg (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps : ℝ} (_heps : eps ≠ 0) (x : ℝ) :
    0 ≤ kernelAverage mu eps x := by
  rw [kernelAverage]
  exact integral_nonneg fun _ ↦ smoothingKernel_nonneg _

lemma integral_norm_comp_neg_div {g : ℝ → ℝ} (_hg : Continuous g)
    {eps : ℝ} (heps : 0 < eps) :
    (∫ t in (-2 : ℝ)..2, g (-t / eps)) =
      eps * ∫ t in -(2 / eps)..(2 / eps), g t := by
  have hsub := intervalIntegral.integral_comp_div
    (f := g) (a := (-2 : ℝ)) (b := 2) (c := -eps) (neg_ne_zero.mpr heps.ne')
  calc
    (∫ t in (-2 : ℝ)..2, g (-t / eps)) =
        ∫ t in (-2 : ℝ)..2, g (t / (-eps)) := by
      apply intervalIntegral.integral_congr
      intro t _
      congr 1
      field_simp [heps.ne']
    _ = (-eps) * ∫ t in (-2 : ℝ) / (-eps)..2 / (-eps), g t := by
      simpa only [smul_eq_mul] using hsub
    _ = eps * ∫ t in -(2 / eps)..(2 / eps), g t := by
      rw [intervalIntegral.integral_symm]
      have hleft : 2 / (-eps) = -(2 / eps) := by
        field_simp [heps.ne']
      have hright : (-2 : ℝ) / (-eps) = 2 / eps := by
        field_simp [heps.ne']
      rw [hleft, hright]
      ring

lemma kernelAverage_le_charFunIntegral
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu eps x ≤
      2 * eps * (∫ t in -(2 / eps)..(2 / eps), ‖charFun mu t‖) := by
  have hEq := ofReal_kernelAverage_eq_kernelFourierAverage mu heps.ne' x
  have hnorm : kernelAverage mu eps x = ‖kernelFourierAverage mu eps x‖ := by
    have h := congrArg norm hEq
    simpa [abs_of_nonneg (kernelAverage_nonneg mu heps.ne' x)] using h
  rw [hnorm, kernelFourierAverage]
  calc
    ‖∫ t in (-2 : ℝ)..2,
        (frequencyKernel t : ℂ) *
          Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun mu (-t / eps)‖
        ≤ ∫ t in (-2 : ℝ)..2,
          ‖(frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun mu (-t / eps)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (-2 : ℝ)..2, 2 * ‖charFun mu (-t / eps)‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_norm.comp
          (((Complex.continuous_ofReal.comp continuous_frequencyKernel).mul
            (Complex.continuous_exp.comp (by fun_prop))).mul
              (continuous_charFun.comp (by fun_prop)))).intervalIntegrable _ _)
        ((continuous_const.mul
          (continuous_norm.comp (continuous_charFun.comp (by fun_prop)))).intervalIntegrable _ _)
      intro t ht
      change ‖(frequencyKernel t : ℂ) *
        Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun mu (-t / eps)‖ ≤
          2 * ‖charFun mu (-t / eps)‖
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      have hfreq : ‖(frequencyKernel t : ℂ)‖ ≤ 2 := by
        simpa [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (frequencyKernel_nonneg t)] using frequencyKernel_le_two t
      exact mul_le_mul_of_nonneg_right hfreq (norm_nonneg _)
    _ = 2 * eps * (∫ t in -(2 / eps)..(2 / eps), ‖charFun mu t‖) := by
      rw [intervalIntegral.integral_const_mul,
        integral_norm_comp_neg_div
          (g := fun t ↦ ‖charFun mu t‖) (continuous_norm.comp continuous_charFun) heps]
      ring

/-- **KSSS Theorem 4.7 (Esseen)** with explicit constant `2`. -/
theorem esseen_4_7 (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    smallBall mu eps x ≤
      2 * eps * (∫ t in -(2 / eps)..(2 / eps), ‖charFun mu t‖) :=
  (smallBall_le_kernelAverage mu heps x).trans
    (kernelAverage_le_charFunIntegral mu heps x)

/-! ### The cell summation behind the relative Esseen inequalities -/

/-- The length-`2 eps` cells centered at the odd multiples of `eps` from
`x`.  They form a disjoint half-open partition of the real line. -/
def kernelCell (x eps : ℝ) (k : ℤ) : Set ℝ :=
  Ico (x + k • (2 * eps)) (x + (k + 1) • (2 * eps))

/-- A summable envelope for the smoothing kernel on `kernelCell`. -/
def kernelCellWeight (k : ℤ) : ℝ :=
  16 / ((k : ℝ) ^ 2 + 1)

lemma kernelCellWeight_nonneg (k : ℤ) : 0 ≤ kernelCellWeight k := by
  rw [kernelCellWeight]
  positivity

lemma iUnion_kernelCell (x : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ⋃ k : ℤ, kernelCell x eps k = univ := by
  exact iUnion_Ico_add_zsmul (mul_pos (by norm_num) heps) x

lemma kernelCell_subset_smallBall (x : ℝ) {eps : ℝ} (heps : 0 < eps) (k : ℤ) :
    kernelCell x eps k ⊆
      Icc (x + ((2 * (k : ℝ) + 1) * eps) - eps)
        (x + ((2 * (k : ℝ) + 1) * eps) + eps) := by
  intro y hy
  rw [kernelCell] at hy
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hy
  constructor <;> nlinarith [hy.1, hy.2]

lemma measureReal_kernelCell_le_concentration
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (x : ℝ) {eps : ℝ} (heps : 0 < eps) (k : ℤ) :
    mu.real (kernelCell x eps k) ≤ concentration mu eps := by
  calc
    mu.real (kernelCell x eps k) ≤
        smallBall mu eps (x + ((2 * (k : ℝ) + 1) * eps)) := by
      exact measureReal_mono (kernelCell_subset_smallBall x heps k)
    _ ≤ concentration mu eps := smallBall_le_concentration _ _ _

lemma smoothingKernel_on_kernelCell_le
    {x y eps : ℝ} (heps : 0 < eps) {k : ℤ}
    (hy : y ∈ kernelCell x eps k) :
    smoothingKernel ((y - x) / eps) ≤ kernelCellWeight k := by
  have hy' := hy
  rw [kernelCell] at hy'
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hy'
  have hzlow : 2 * (k : ℝ) ≤ (y - x) / eps := by
    apply (le_div_iff₀ heps).2
    nlinarith [hy'.1]
  have hzup : (y - x) / eps < 2 * ((k : ℝ) + 1) := by
    apply (div_lt_iff₀ heps).2
    nlinarith [hy'.2]
  by_cases hk0 : k = 0
  · subst k
    rw [kernelCellWeight]
    norm_num
    exact (smoothingKernel_le_four _).trans (by norm_num)
  by_cases hkm1 : k = -1
  · subst k
    rw [kernelCellWeight]
    norm_num
    exact (smoothingKernel_le_four _).trans (by norm_num)
  have hkCases : (1 : ℤ) ≤ k ∨ k ≤ -2 := by omega
  have hsq : (k : ℝ) ^ 2 ≤ ((y - x) / eps) ^ 2 := by
    rcases hkCases with hk | hk
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    · have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast hk
      nlinarith
  calc
    smoothingKernel ((y - x) / eps) ≤
        8 / (((y - x) / eps) ^ 2 + 1) := smoothingKernel_le_eight_div _
    _ ≤ 16 / ((k : ℝ) ^ 2 + 1) := by
      apply (div_le_div_iff₀ (by positivity : 0 < ((y - x) / eps) ^ 2 + 1)
        (by positivity : 0 < (k : ℝ) ^ 2 + 1)).2
      nlinarith
    _ = kernelCellWeight k := by rfl

lemma summable_kernelCellWeight : Summable kernelCellWeight := by
  have hinv : Summable (fun k : ℤ ↦ 1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hsingle : Summable (fun k : ℤ ↦ if k = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hmajor : Summable
      (fun k : ℤ ↦ 16 * ((if k = 0 then (1 : ℝ) else 0) + 1 / (k : ℝ) ^ 2)) :=
    (hsingle.add hinv).mul_left 16
  refine hmajor.of_norm_bounded (fun k ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellWeight_nonneg k)]
  by_cases hk : k = 0
  · subst k
    norm_num [kernelCellWeight]
  · rw [if_neg hk]
    have hkR : (0 : ℝ) < (k : ℝ) ^ 2 := by
      exact sq_pos_of_ne_zero (by exact_mod_cast hk)
    have hdiv : 1 / ((k : ℝ) ^ 2 + 1) ≤ 1 / (k : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ) ^ 2 + 1) hkR).2
      nlinarith
    rw [kernelCellWeight, zero_add]
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 16)

/-- The constant function with value `kernelCellWeight k`, restricted to
the `k`-th cell. -/
def kernelCellTerm (x eps : ℝ) (k : ℤ) : ℝ → ℝ :=
  (kernelCell x eps k).indicator (fun _ ↦ kernelCellWeight k)

lemma kernelCellTerm_nonneg (x eps : ℝ) (k : ℤ) (y : ℝ) :
    0 ≤ kernelCellTerm x eps k y := by
  by_cases hy : y ∈ kernelCell x eps k
  · simp [kernelCellTerm, hy, kernelCellWeight_nonneg]
  · simp [kernelCellTerm, hy]

lemma kernelCellTerm_measurable (x eps : ℝ) (k : ℤ) :
    Measurable (kernelCellTerm x eps k) := by
  exact measurable_const.indicator measurableSet_Ico

lemma kernelCellTerm_integrable (mu : Measure ℝ) [IsFiniteMeasure mu]
    (x eps : ℝ) (k : ℤ) : Integrable (kernelCellTerm x eps k) mu := by
  exact (integrable_const (kernelCellWeight k)).indicator measurableSet_Ico

lemma integral_kernelCellTerm (mu : Measure ℝ) [IsFiniteMeasure mu]
    (x eps : ℝ) (k : ℤ) :
    (∫ y, kernelCellTerm x eps k y ∂mu) =
      mu.real (kernelCell x eps k) * kernelCellWeight k := by
  have hcell : MeasurableSet (kernelCell x eps k) := measurableSet_Ico
  rw [kernelCellTerm, integral_indicator_const (kernelCellWeight k) hcell,
    smul_eq_mul]

lemma integral_norm_kernelCellTerm (mu : Measure ℝ) [IsFiniteMeasure mu]
    (x eps : ℝ) (k : ℤ) :
    (∫ y, ‖kernelCellTerm x eps k y‖ ∂mu) =
      mu.real (kernelCell x eps k) * kernelCellWeight k := by
  have hfun : (fun y ↦ ‖kernelCellTerm x eps k y‖) = kernelCellTerm x eps k := by
    funext y
    rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellTerm_nonneg x eps k y)]
  rw [hfun, integral_kernelCellTerm]

lemma summable_kernelCellTerm (x eps y : ℝ) :
    Summable (fun k : ℤ ↦ kernelCellTerm x eps k y) := by
  refine summable_kernelCellWeight.of_norm_bounded (fun k ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellTerm_nonneg x eps k y)]
  by_cases hy : y ∈ kernelCell x eps k
  · simp [kernelCellTerm, hy]
  · simp [kernelCellTerm, hy, kernelCellWeight_nonneg]

lemma smoothingKernel_le_tsum_kernelCellTerm
    {x y eps : ℝ} (heps : 0 < eps) :
    smoothingKernel ((y - x) / eps) ≤
      ∑' k : ℤ, kernelCellTerm x eps k y := by
  have hyuniv : y ∈ ⋃ k : ℤ, kernelCell x eps k := by
    rw [iUnion_kernelCell x heps]
    exact mem_univ y
  rcases mem_iUnion.1 hyuniv with ⟨k, hyk⟩
  calc
    smoothingKernel ((y - x) / eps) ≤ kernelCellWeight k :=
      smoothingKernel_on_kernelCell_le heps hyk
    _ = kernelCellTerm x eps k y := by
      simp [kernelCellTerm, hyk]
    _ ≤ ∑' j : ℤ, kernelCellTerm x eps j y := by
      have hsum := (summable_kernelCellTerm x eps y).sum_le_tsum {k}
        (fun j _ ↦ kernelCellTerm_nonneg x eps j y)
      simpa using hsum

lemma integrable_tsum_kernelCellTerm
    (mu : Measure ℝ) [IsFiniteMeasure mu] (x eps : ℝ) :
    Integrable (fun y ↦ ∑' k : ℤ, kernelCellTerm x eps k y) mu := by
  refine Integrable.mono' (integrable_const (∑' k : ℤ, kernelCellWeight k))
    ((Measurable.tsum fun k ↦ kernelCellTerm_measurable x eps k).aestronglyMeasurable) ?_
  filter_upwards with y
  calc
    ‖∑' k : ℤ, kernelCellTerm x eps k y‖ ≤
        ∑' k : ℤ, ‖kernelCellTerm x eps k y‖ :=
      norm_tsum_le_tsum_norm (summable_kernelCellTerm x eps y).norm
    _ ≤ ∑' k : ℤ, kernelCellWeight k := by
      apply Summable.tsum_le_tsum
      · intro k
        rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellTerm_nonneg x eps k y)]
        by_cases hy : y ∈ kernelCell x eps k
        · simp [kernelCellTerm, hy]
        · simp [kernelCellTerm, hy, kernelCellWeight_nonneg]
      · exact (summable_kernelCellTerm x eps y).norm
      · exact summable_kernelCellWeight

/-- The smoothing-kernel expectation is controlled by the concentration
function, with an explicit absolute summable constant. -/
lemma kernelAverage_le_cellMass_mul_concentration
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu eps x ≤
      concentration mu eps * (∑' k : ℤ, kernelCellWeight k) := by
  have htermInt : ∀ k : ℤ, Integrable (kernelCellTerm x eps k) mu :=
    kernelCellTerm_integrable mu x eps
  have htermLe : ∀ k : ℤ,
      (∫ y, ‖kernelCellTerm x eps k y‖ ∂mu) ≤
        concentration mu eps * kernelCellWeight k := by
    intro k
    rw [integral_norm_kernelCellTerm]
    exact mul_le_mul_of_nonneg_right
      (measureReal_kernelCell_le_concentration mu x heps k)
      (kernelCellWeight_nonneg k)
  have hnormSum : Summable
      (fun k : ℤ ↦ ∫ y, ‖kernelCellTerm x eps k y‖ ∂mu) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact integral_nonneg fun y ↦ norm_nonneg _
    · exact htermLe
    · exact summable_kernelCellWeight.mul_left (concentration mu eps)
  rw [kernelAverage]
  calc
    (∫ y, smoothingKernel ((y - x) / eps) ∂mu) ≤
        ∫ y, (∑' k : ℤ, kernelCellTerm x eps k y) ∂mu := by
      apply integral_mono (integrable_kernelAverage mu heps.ne' x)
        (integrable_tsum_kernelCellTerm mu x eps)
      intro y
      exact smoothingKernel_le_tsum_kernelCellTerm heps
    _ = ∑' k : ℤ, ∫ y, kernelCellTerm x eps k y ∂mu := by
      exact (integral_tsum_of_summable_integral_norm htermInt hnormSum).symm
    _ ≤ ∑' k : ℤ, concentration mu eps * kernelCellWeight k := by
      apply Summable.tsum_le_tsum
      · intro k
        calc
          (∫ y, kernelCellTerm x eps k y ∂mu) ≤
              ∫ y, ‖kernelCellTerm x eps k y‖ ∂mu :=
            integral_mono (kernelCellTerm_integrable mu x eps k)
              (kernelCellTerm_integrable mu x eps k).norm
              (fun y ↦ by
                rw [Real.norm_eq_abs]
                exact le_abs_self _)
          _ ≤ concentration mu eps * kernelCellWeight k := htermLe k
      · exact (hnormSum.of_norm_bounded fun k ↦ norm_integral_le_integral_norm _)
      · exact summable_kernelCellWeight.mul_left (concentration mu eps)
    _ = concentration mu eps * (∑' k : ℤ, kernelCellWeight k) := by
      rw [tsum_mul_left]

lemma two_le_kernelCellWeightSum :
    (2 : ℝ) ≤ ∑' k : ℤ, kernelCellWeight k := by
  have h := summable_kernelCellWeight.sum_le_tsum ({0} : Finset ℤ)
    (fun k _ ↦ kernelCellWeight_nonneg k)
  norm_num [kernelCellWeight] at h ⊢
  linarith

lemma fourierError_nonneg (mu nu : Measure ℝ)
    {eps : ℝ} (heps : 0 < eps) : 0 ≤ fourierError mu nu eps := by
  rw [fourierError]
  apply intervalIntegral.integral_nonneg
  · have h : 0 < 2 / eps := div_pos (by norm_num) heps
    linarith
  · intro t _
    exact norm_nonneg _

/-- Comparison of the two frequency-side kernel averages. -/
lemma norm_kernelFourierAverage_sub_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    ‖kernelFourierAverage mu eps x - kernelFourierAverage nu eps x‖ ≤
      2 * eps * fourierError mu nu eps := by
  let F : Measure ℝ → ℝ → ℂ := fun ρ t ↦
    (frequencyKernel t : ℂ) *
      Complex.exp (((t * x) / eps : ℝ) * Complex.I) * charFun ρ (-t / eps)
  have hcont (ρ : Measure ℝ) [IsFiniteMeasure ρ] : Continuous (F ρ) := by
    dsimp only [F]
    exact
      ((Complex.continuous_ofReal.comp continuous_frequencyKernel).mul
        (Complex.continuous_exp.comp (by fun_prop))).mul
          (continuous_charFun.comp (by fun_prop))
  have hInt (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
      IntervalIntegrable (F ρ) volume (-2) 2 :=
    (hcont ρ).intervalIntegrable _ _
  have hrewrite :
      kernelFourierAverage mu eps x - kernelFourierAverage nu eps x =
        ∫ t in (-2 : ℝ)..2,
          (frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
              (charFun mu (-t / eps) - charFun nu (-t / eps)) := by
    rw [kernelFourierAverage, kernelFourierAverage,
      ← intervalIntegral.integral_sub (hInt mu) (hInt nu)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [F]
    ring
  rw [hrewrite]
  calc
    ‖∫ t in (-2 : ℝ)..2,
        (frequencyKernel t : ℂ) *
          Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
            (charFun mu (-t / eps) - charFun nu (-t / eps))‖ ≤
        ∫ t in (-2 : ℝ)..2,
          ‖(frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
              (charFun mu (-t / eps) - charFun nu (-t / eps))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (-2 : ℝ)..2,
          2 * ‖charFun mu (-t / eps) - charFun nu (-t / eps)‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_norm.comp
          (((Complex.continuous_ofReal.comp continuous_frequencyKernel).mul
            (Complex.continuous_exp.comp (by fun_prop))).mul
              ((continuous_charFun.comp (by fun_prop)).sub
                (continuous_charFun.comp (by fun_prop))))).intervalIntegrable _ _)
        ((continuous_const.mul
          (continuous_norm.comp
            ((continuous_charFun.comp (by fun_prop)).sub
              (continuous_charFun.comp (by fun_prop))))).intervalIntegrable _ _)
      intro t _
      change
        ‖(frequencyKernel t : ℂ) *
            Complex.exp (((t * x) / eps : ℝ) * Complex.I) *
              (charFun mu (-t / eps) - charFun nu (-t / eps))‖ ≤
          2 * ‖charFun mu (-t / eps) - charFun nu (-t / eps)‖
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      have hfreq : ‖(frequencyKernel t : ℂ)‖ ≤ 2 := by
        simpa [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (frequencyKernel_nonneg t)] using frequencyKernel_le_two t
      exact mul_le_mul_of_nonneg_right hfreq (norm_nonneg _)
    _ = 2 * eps * fourierError mu nu eps := by
      rw [intervalIntegral.integral_const_mul,
        integral_norm_comp_neg_div
          (g := fun t ↦ ‖charFun mu t - charFun nu t‖)
          (continuous_norm.comp (continuous_charFun.sub continuous_charFun)) heps,
        fourierError]
      ring

/-- The two smoothing-kernel expectations differ by the Fourier `L¹` error. -/
lemma kernelAverage_le_kernelAverage_add_fourierError
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu eps x ≤ kernelAverage nu eps x +
      2 * eps * fourierError mu nu eps := by
  have hmu := ofReal_kernelAverage_eq_kernelFourierAverage mu heps.ne' x
  have hnu := ofReal_kernelAverage_eq_kernelFourierAverage nu heps.ne' x
  have hnorm : |kernelAverage mu eps x - kernelAverage nu eps x| =
      ‖kernelFourierAverage mu eps x - kernelFourierAverage nu eps x‖ := by
    calc
      |kernelAverage mu eps x - kernelAverage nu eps x| =
          ‖((kernelAverage mu eps x - kernelAverage nu eps x : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖kernelFourierAverage mu eps x - kernelFourierAverage nu eps x‖ := by
        congr 1
        push_cast
        rw [hmu, hnu]
  have hdiff : kernelAverage mu eps x - kernelAverage nu eps x ≤
      2 * eps * fourierError mu nu eps := by
    calc
      kernelAverage mu eps x - kernelAverage nu eps x ≤
          |kernelAverage mu eps x - kernelAverage nu eps x| := le_abs_self _
      _ = ‖kernelFourierAverage mu eps x - kernelFourierAverage nu eps x‖ := hnorm
      _ ≤ 2 * eps * fourierError mu nu eps :=
        norm_kernelFourierAverage_sub_le mu nu heps x
  linarith

/-- **KSSS Lemma 6.1 (relative Esseen)**, with the explicit absolute
constant supplied by the summable cell envelope. -/
theorem relative_esseen_6_1
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) :
    concentration mu eps ≤
      (∑' k : ℤ, kernelCellWeight k) *
        (concentration nu eps + eps * fourierError mu nu eps) := by
  apply csSup_le (range_nonempty _)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  calc
    smallBall mu eps x ≤ kernelAverage mu eps x :=
      smallBall_le_kernelAverage mu heps x
    _ ≤ kernelAverage nu eps x + 2 * eps * fourierError mu nu eps :=
      kernelAverage_le_kernelAverage_add_fourierError mu nu heps x
    _ ≤ concentration nu eps * (∑' k : ℤ, kernelCellWeight k) +
          2 * eps * fourierError mu nu eps := by
      gcongr
      exact kernelAverage_le_cellMass_mul_concentration nu heps x
    _ ≤ (∑' k : ℤ, kernelCellWeight k) *
          (concentration nu eps + eps * fourierError mu nu eps) := by
      have herr : 0 ≤ eps * fourierError mu nu eps :=
        mul_nonneg heps.le (fourierError_nonneg mu nu heps)
      have hmass := two_le_kernelCellWeightSum
      nlinarith

/-! ### The non-uniform cell decomposition for KSSS Lemma 6.2 -/

def kernelCellCenter (x eps : ℝ) (k : ℤ) : ℝ :=
  x + (2 * (k : ℝ) + 1) * eps

lemma kernelCell_subset_centered (x : ℝ) {eps : ℝ} (heps : 0 < eps) (k : ℤ) :
    kernelCell x eps k ⊆
      Icc (kernelCellCenter x eps k - eps) (kernelCellCenter x eps k + eps) := by
  exact kernelCell_subset_smallBall x heps k

lemma concentration_le_of_smallBall_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {eps B : ℝ}
    (hB : ∀ y : ℝ, smallBall mu eps y ≤ B) :
    concentration mu eps ≤ B := by
  apply csSup_le (range_nonempty _)
  intro z hz
  rcases hz with ⟨y, rfl⟩
  exact hB y

/-- The cell terms whose centers lie in the exponential tail relevant at
the point `x`. -/
def kernelHighCellTerm (x eps : ℝ) (k : ℤ) : ℝ → ℝ :=
  if |kernelCellCenter x eps k| ≥ |x| / 2 then kernelCellTerm x eps k else 0

lemma kernelHighCellTerm_nonneg (x eps : ℝ) (k : ℤ) (y : ℝ) :
    0 ≤ kernelHighCellTerm x eps k y := by
  rw [kernelHighCellTerm]
  split_ifs
  · exact kernelCellTerm_nonneg x eps k y
  · exact le_rfl

lemma kernelHighCellTerm_measurable (x eps : ℝ) (k : ℤ) :
    Measurable (kernelHighCellTerm x eps k) := by
  rw [kernelHighCellTerm]
  split_ifs
  · exact kernelCellTerm_measurable x eps k
  · exact measurable_zero

lemma kernelHighCellTerm_integrable
    (mu : Measure ℝ) [IsFiniteMeasure mu] (x eps : ℝ) (k : ℤ) :
    Integrable (kernelHighCellTerm x eps k) mu := by
  rw [kernelHighCellTerm]
  split_ifs
  · exact kernelCellTerm_integrable mu x eps k
  · exact integrable_zero _ _ _

lemma summable_kernelHighCellTerm (x eps y : ℝ) :
    Summable (fun k : ℤ ↦ kernelHighCellTerm x eps k y) := by
  refine summable_kernelCellWeight.of_norm_bounded (fun k ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelHighCellTerm_nonneg x eps k y)]
  rw [kernelHighCellTerm]
  split_ifs
  · by_cases hy : y ∈ kernelCell x eps k
    · simp [kernelCellTerm, hy]
    · simp [kernelCellTerm, hy, kernelCellWeight_nonneg]
  · exact kernelCellWeight_nonneg k

/-- For `|x| > 4 sigma`, the kernel is either uniformly small, or the
point lies in a cell whose center has absolute value at least `|x|/2`. -/
lemma smoothingKernel_le_farTerm_add_highCells
    {x y eps sigma : ℝ} (heps : 0 < eps) (hsigma : 0 < sigma)
    (hepssigma : eps ≤ sigma) (hx : 4 * sigma < |x|) :
    smoothingKernel ((y - x) / eps) ≤
      256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        ∑' k : ℤ, kernelHighCellTerm x eps k y := by
  by_cases hyfar : 3 * |x| / 4 ≤ |y|
  · have hyuniv : y ∈ ⋃ k : ℤ, kernelCell x eps k := by
      rw [iUnion_kernelCell x heps]
      exact mem_univ y
    rcases mem_iUnion.1 hyuniv with ⟨k, hyk⟩
    have hycenter := kernelCell_subset_centered x heps k hyk
    have hdist : |y - kernelCellCenter x eps k| ≤ eps := by
      exact (abs_le).2 ⟨by linarith [hycenter.1], by linarith [hycenter.2]⟩
    have hcenter : |x| / 2 ≤ |kernelCellCenter x eps k| := by
      have htri : |y| ≤ |y - kernelCellCenter x eps k| +
          |kernelCellCenter x eps k| := by
        calc
          |y| = |(y - kernelCellCenter x eps k) + kernelCellCenter x eps k| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      nlinarith
    have hterm : kernelHighCellTerm x eps k y = kernelCellWeight k := by
      rw [kernelHighCellTerm, if_pos hcenter]
      simp [kernelCellTerm, hyk]
    have hsingle : kernelCellWeight k ≤
        ∑' j : ℤ, kernelHighCellTerm x eps j y := by
      rw [← hterm]
      have hsum := (summable_kernelHighCellTerm x eps y).sum_le_tsum {k}
        (fun j _ ↦ kernelHighCellTerm_nonneg x eps j y)
      simpa using hsum
    calc
      smoothingKernel ((y - x) / eps) ≤ kernelCellWeight k :=
        smoothingKernel_on_kernelCell_le heps hyk
      _ ≤ ∑' j : ℤ, kernelHighCellTerm x eps j y := hsingle
      _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          ∑' j : ℤ, kernelHighCellTerm x eps j y := by
        have : 0 ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) := by positivity
        linarith
  · have hynear : |y| < 3 * |x| / 4 := lt_of_not_ge hyfar
    have hdist : |x| / 4 ≤ |y - x| := by
      have htri : |x| ≤ |y| + |y - x| := by
        calc
          |x| = |y - (y - x)| := by ring_nf
          _ ≤ |y| + |y - x| := abs_sub _ _
      linarith
    have hdistSq : x ^ 2 / 16 ≤ (y - x) ^ 2 := by
      nlinarith [sq_abs x, sq_abs (y - x), abs_nonneg x, abs_nonneg (y - x)]
    have hsigmaSq : sigma ^ 2 < x ^ 2 / 16 := by
      nlinarith [sq_abs x, abs_nonneg x]
    have hscale : eps ^ 2 * (((y - x) / eps) ^ 2 + 1) =
        (y - x) ^ 2 + eps ^ 2 := by
      field_simp [heps.ne']
    have hfar : 8 / (((y - x) / eps) ^ 2 + 1) ≤
        256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < ((y - x) / eps) ^ 2 + 1)
        (by positivity : 0 < x ^ 2 + sigma ^ 2)).2
      have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
      nlinarith
    calc
      smoothingKernel ((y - x) / eps) ≤
          8 / (((y - x) / eps) ^ 2 + 1) := smoothingKernel_le_eight_div _
      _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) := hfar
      _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          ∑' k : ℤ, kernelHighCellTerm x eps k y := by
        have : 0 ≤ ∑' k : ℤ, kernelHighCellTerm x eps k y :=
          tsum_nonneg fun k ↦ kernelHighCellTerm_nonneg x eps k y
        linarith

lemma integral_norm_kernelHighCellTerm
    (mu : Measure ℝ) [IsFiniteMeasure mu] (x eps : ℝ) (k : ℤ) :
    (∫ y, ‖kernelHighCellTerm x eps k y‖ ∂mu) =
      if |x| / 2 ≤ |kernelCellCenter x eps k| then
        mu.real (kernelCell x eps k) * kernelCellWeight k else 0 := by
  by_cases hk : |x| / 2 ≤ |kernelCellCenter x eps k|
  · rw [if_pos hk, kernelHighCellTerm, if_pos hk,
      integral_norm_kernelCellTerm]
  · rw [if_neg hk, kernelHighCellTerm, if_neg hk]
    simp

lemma integrable_tsum_kernelHighCellTerm
    (mu : Measure ℝ) [IsFiniteMeasure mu] (x eps : ℝ) :
    Integrable (fun y ↦ ∑' k : ℤ, kernelHighCellTerm x eps k y) mu := by
  refine Integrable.mono' (integrable_const (∑' k : ℤ, kernelCellWeight k))
    ((Measurable.tsum fun k ↦ kernelHighCellTerm_measurable x eps k).aestronglyMeasurable) ?_
  filter_upwards with y
  calc
    ‖∑' k : ℤ, kernelHighCellTerm x eps k y‖ ≤
        ∑' k : ℤ, ‖kernelHighCellTerm x eps k y‖ :=
      norm_tsum_le_tsum_norm (summable_kernelHighCellTerm x eps y).norm
    _ ≤ ∑' k : ℤ, kernelCellWeight k := by
      apply Summable.tsum_le_tsum
      · intro k
        rw [Real.norm_eq_abs, abs_of_nonneg (kernelHighCellTerm_nonneg x eps k y)]
        rw [kernelHighCellTerm]
        split_ifs
        · by_cases hy : y ∈ kernelCell x eps k
          · simp [kernelCellTerm, hy]
          · simp [kernelCellTerm, hy, kernelCellWeight_nonneg]
        · exact kernelCellWeight_nonneg k
      · exact (summable_kernelHighCellTerm x eps y).norm
      · exact summable_kernelCellWeight

lemma integral_norm_kernelHighCellTerm_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {x eps eta sigma : ℝ} (heps : 0 < eps) (heta : 0 < eta) (hsigma : 0 < sigma)
    (hsmall : ∀ z : ℝ, smallBall mu eps z ≤
      (eps / (eta * sigma)) * Real.exp (-eta * |z| / sigma)) (k : ℤ) :
    (∫ y, ‖kernelHighCellTerm x eps k y‖ ∂mu) ≤
      ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) *
        kernelCellWeight k := by
  rw [integral_norm_kernelHighCellTerm]
  by_cases hk : |x| / 2 ≤ |kernelCellCenter x eps k|
  · rw [if_pos hk]
    have hmeasure : mu.real (kernelCell x eps k) ≤
        (eps / (eta * sigma)) *
          Real.exp (-eta * |kernelCellCenter x eps k| / sigma) := by
      calc
        mu.real (kernelCell x eps k) ≤
            smallBall mu eps (kernelCellCenter x eps k) := by
          exact measureReal_mono (kernelCell_subset_centered x heps k)
        _ ≤ _ := hsmall _
    have hexp : Real.exp (-eta * |kernelCellCenter x eps k| / sigma) ≤
        Real.exp (-eta * |x| / (2 * sigma)) := by
      apply Real.exp_le_exp.mpr
      have hnum : -eta * |kernelCellCenter x eps k| ≤ -eta * |x| / 2 := by
        have hmul := mul_le_mul_of_nonpos_left hk (neg_nonpos.mpr heta.le)
        nlinarith
      calc
        -eta * |kernelCellCenter x eps k| / sigma ≤
            (-eta * |x| / 2) / sigma :=
          div_le_div_of_nonneg_right hnum hsigma.le
        _ = -eta * |x| / (2 * sigma) := by field_simp
    have hbase : 0 ≤ eps / (eta * sigma) := by positivity
    exact mul_le_mul_of_nonneg_right
      (hmeasure.trans (mul_le_mul_of_nonneg_left hexp hbase))
      (kernelCellWeight_nonneg k)
  · rw [if_neg hk]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_nonneg _))
      (kernelCellWeight_nonneg k)

/-- Integrated large-`|x|` form of the non-uniform cell decomposition. -/
lemma kernelAverage_le_nonuniform_large
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {x eps eta sigma : ℝ} (heps : 0 < eps) (heta : 0 < eta) (hsigma : 0 < sigma)
    (hepssigma : eps ≤ sigma) (hx : 4 * sigma < |x|)
    (hsmall : ∀ z : ℝ, smallBall mu eps z ≤
      (eps / (eta * sigma)) * Real.exp (-eta * |z| / sigma)) :
    kernelAverage mu eps x ≤
      256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) *
          (∑' k : ℤ, kernelCellWeight k) := by
  let B : ℝ := (eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))
  have htermInt : ∀ k : ℤ, Integrable (kernelHighCellTerm x eps k) mu :=
    kernelHighCellTerm_integrable mu x eps
  have htermLe : ∀ k : ℤ,
      (∫ y, ‖kernelHighCellTerm x eps k y‖ ∂mu) ≤
        B * kernelCellWeight k := by
    intro k
    exact integral_norm_kernelHighCellTerm_le mu heps heta hsigma hsmall k
  have hnormSum : Summable
      (fun k : ℤ ↦ ∫ y, ‖kernelHighCellTerm x eps k y‖ ∂mu) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact integral_nonneg fun y ↦ norm_nonneg _
    · exact htermLe
    · exact summable_kernelCellWeight.mul_left B
  rw [kernelAverage]
  calc
    (∫ y, smoothingKernel ((y - x) / eps) ∂mu) ≤
        ∫ y, (256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          ∑' k : ℤ, kernelHighCellTerm x eps k y) ∂mu := by
      apply integral_mono (integrable_kernelAverage mu heps.ne' x)
        ((integrable_const (256 * eps ^ 2 / (x ^ 2 + sigma ^ 2))).add
          (integrable_tsum_kernelHighCellTerm mu x eps))
      intro y
      exact smoothingKernel_le_farTerm_add_highCells heps hsigma hepssigma hx
    _ = 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        ∑' k : ℤ, ∫ y, kernelHighCellTerm x eps k y ∂mu := by
      rw [integral_add (integrable_const _) (integrable_tsum_kernelHighCellTerm mu x eps),
        integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
        ← integral_tsum_of_summable_integral_norm htermInt hnormSum]
    _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        ∑' k : ℤ, B * kernelCellWeight k := by
      apply add_le_add_right
      apply Summable.tsum_le_tsum
      · intro k
        calc
          (∫ y, kernelHighCellTerm x eps k y ∂mu) ≤
              ∫ y, ‖kernelHighCellTerm x eps k y‖ ∂mu :=
            integral_mono (kernelHighCellTerm_integrable mu x eps k)
              (kernelHighCellTerm_integrable mu x eps k).norm
              (fun y ↦ by
                rw [Real.norm_eq_abs]
                exact le_abs_self _)
          _ ≤ B * kernelCellWeight k := htermLe k
      · exact (hnormSum.of_norm_bounded fun k ↦ norm_integral_le_integral_norm _)
      · exact summable_kernelCellWeight.mul_left B
    _ = 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) *
          (∑' k : ℤ, kernelCellWeight k) := by
      rw [tsum_mul_left]

/-- Uniform-in-`x` non-uniform kernel estimate.  The factor `exp 2` covers
the bounded range `|x| ≤ 4 sigma`; outside it the sharper cell decomposition
applies. -/
lemma kernelAverage_le_nonuniform
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {x eps eta sigma : ℝ} (heps : 0 < eps) (heta : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hepssigma : eps ≤ sigma)
    (hsmall : ∀ z : ℝ, smallBall mu eps z ≤
      (eps / (eta * sigma)) * Real.exp (-eta * |z| / sigma)) :
    kernelAverage mu eps x ≤
      256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
          ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) := by
  by_cases hx : 4 * sigma < |x|
  · calc
      kernelAverage mu eps x ≤
          256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
            ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) *
              (∑' k : ℤ, kernelCellWeight k) :=
        kernelAverage_le_nonuniform_large mu heps heta hsigma hepssigma hx hsmall
      _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
            ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) := by
        have hmass : 0 ≤ ∑' k : ℤ, kernelCellWeight k :=
          tsum_nonneg kernelCellWeight_nonneg
        have hbase : 0 ≤ (eps / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) := by positivity
        have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
        rw [add_le_add_iff_left]
        calc
          (eps / (eta * sigma) * Real.exp (-eta * |x| / (2 * sigma))) *
                (∑' k : ℤ, kernelCellWeight k) =
              1 * (∑' k : ℤ, kernelCellWeight k) *
                (eps / (eta * sigma) *
                  Real.exp (-eta * |x| / (2 * sigma))) := by ring
          _ ≤ Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
                (eps / (eta * sigma) *
                  Real.exp (-eta * |x| / (2 * sigma))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hexp hmass) hbase
  · have hx' : |x| ≤ 4 * sigma := le_of_not_gt hx
    have hconc : concentration mu eps ≤ eps / (eta * sigma) := by
      apply concentration_le_of_smallBall_le
      intro z
      calc
        smallBall mu eps z ≤
            (eps / (eta * sigma)) * Real.exp (-eta * |z| / sigma) := hsmall z
        _ ≤ eps / (eta * sigma) := by
          have hbase : 0 ≤ eps / (eta * sigma) := by positivity
          apply mul_le_of_le_one_right hbase
          apply Real.exp_le_one_iff.mpr
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (abs_nonneg z))
            hsigma.le
    have hexpFactor : 1 ≤ Real.exp 2 * Real.exp (-eta * |x| / (2 * sigma)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hratio : eta * |x| / (2 * sigma) ≤ 2 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hsigma)).2
        nlinarith [abs_nonneg x]
      rw [show -eta * |x| / (2 * sigma) =
        -(eta * |x| / (2 * sigma)) by ring]
      exact sub_nonneg.mpr hratio
    have hmass : 0 ≤ ∑' k : ℤ, kernelCellWeight k :=
      tsum_nonneg kernelCellWeight_nonneg
    have hbase : 0 ≤ eps / (eta * sigma) := by positivity
    calc
      kernelAverage mu eps x ≤
          concentration mu eps * (∑' k : ℤ, kernelCellWeight k) :=
        kernelAverage_le_cellMass_mul_concentration mu heps x
      _ ≤ (eps / (eta * sigma)) *
          (∑' k : ℤ, kernelCellWeight k) :=
        mul_le_mul_of_nonneg_right hconc hmass
      _ ≤ Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
          ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) := by
        calc
          (eps / (eta * sigma)) * (∑' k : ℤ, kernelCellWeight k) =
              1 * ((eps / (eta * sigma)) *
                (∑' k : ℤ, kernelCellWeight k)) := by ring
          _ ≤ (Real.exp 2 * Real.exp (-eta * |x| / (2 * sigma))) *
                ((eps / (eta * sigma)) *
                  (∑' k : ℤ, kernelCellWeight k)) :=
            mul_le_mul_of_nonneg_right hexpFactor (mul_nonneg hbase hmass)
          _ = Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
              ((eps / (eta * sigma)) *
                Real.exp (-eta * |x| / (2 * sigma))) := by ring
      _ ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) *
            ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) := by
        have : 0 ≤ 256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) := by positivity
        linarith

/-- An explicit absolute constant valid simultaneously in Lemmas 6.1 and
6.2. -/
def relativeEsseenConstant : ℝ :=
  256 + Real.exp 2 * (∑' k : ℤ, kernelCellWeight k)

lemma relativeEsseenConstant_nonneg : 0 ≤ relativeEsseenConstant := by
  rw [relativeEsseenConstant]
  exact add_nonneg (by norm_num)
    (mul_nonneg (Real.exp_pos 2).le (tsum_nonneg kernelCellWeight_nonneg))

/-- **KSSS Lemma 6.2 (non-uniform relative Esseen)**. -/
theorem relative_esseen_6_2
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps eta sigma : ℝ} (heps : 0 < eps) (heta : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hepssigma : eps ≤ sigma)
    (hsmall : ∀ y : ℝ, smallBall nu eps y ≤
      (eps / (eta * sigma)) * Real.exp (-eta * |y| / sigma))
    (x : ℝ) :
    smallBall mu eps x ≤ relativeEsseenConstant *
      (eps ^ 2 / (x ^ 2 + sigma ^ 2) +
        (eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) +
        eps * fourierError mu nu eps) := by
  have hkernel := kernelAverage_le_nonuniform nu heps heta heta1 hsigma hepssigma hsmall
    (x := x)
  have hcompare := kernelAverage_le_kernelAverage_add_fourierError mu nu heps x
  have hmass : 0 ≤ ∑' k : ℤ, kernelCellWeight k :=
    tsum_nonneg kernelCellWeight_nonneg
  have hA : 0 ≤ eps ^ 2 / (x ^ 2 + sigma ^ 2) := by positivity
  have hB : 0 ≤ (eps / (eta * sigma)) *
      Real.exp (-eta * |x| / (2 * sigma)) := by positivity
  have hE : 0 ≤ eps * fourierError mu nu eps :=
    mul_nonneg heps.le (fourierError_nonneg mu nu heps)
  have hC256 : (256 : ℝ) ≤ relativeEsseenConstant := by
    rw [relativeEsseenConstant]
    exact le_add_of_nonneg_right
      (mul_nonneg (Real.exp_pos 2).le hmass)
  have hCexp : Real.exp 2 * (∑' k : ℤ, kernelCellWeight k) ≤
      relativeEsseenConstant := by
    rw [relativeEsseenConstant]
    norm_num
  have hC2 : (2 : ℝ) ≤ relativeEsseenConstant := by linarith
  calc
    smallBall mu eps x ≤ kernelAverage mu eps x :=
      smallBall_le_kernelAverage mu heps x
    _ ≤ kernelAverage nu eps x + 2 * eps * fourierError mu nu eps := hcompare
    _ ≤ 256 * (eps ^ 2 / (x ^ 2 + sigma ^ 2)) +
          (Real.exp 2 * (∑' k : ℤ, kernelCellWeight k)) *
            ((eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma))) +
          2 * (eps * fourierError mu nu eps) := by
      calc
        kernelAverage nu eps x + 2 * eps * fourierError mu nu eps ≤
            (256 * eps ^ 2 / (x ^ 2 + sigma ^ 2) +
              (Real.exp 2 * (∑' k : ℤ, kernelCellWeight k)) *
                ((eps / (eta * sigma)) *
                  Real.exp (-eta * |x| / (2 * sigma)))) +
              2 * eps * fourierError mu nu eps :=
          add_le_add_left hkernel _
        _ = 256 * (eps ^ 2 / (x ^ 2 + sigma ^ 2)) +
              (Real.exp 2 * (∑' k : ℤ, kernelCellWeight k)) *
                ((eps / (eta * sigma)) *
                  Real.exp (-eta * |x| / (2 * sigma))) +
              2 * (eps * fourierError mu nu eps) := by ring
    _ ≤ relativeEsseenConstant *
        (eps ^ 2 / (x ^ 2 + sigma ^ 2) +
          (eps / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) +
          eps * fourierError mu nu eps) := by
      calc
        256 * (eps ^ 2 / (x ^ 2 + sigma ^ 2)) +
              (Real.exp 2 * (∑' k : ℤ, kernelCellWeight k)) *
                ((eps / (eta * sigma)) *
                  Real.exp (-eta * |x| / (2 * sigma))) +
              2 * (eps * fourierError mu nu eps) ≤
            relativeEsseenConstant *
                (eps ^ 2 / (x ^ 2 + sigma ^ 2)) +
              relativeEsseenConstant *
                ((eps / (eta * sigma)) *
                  Real.exp (-eta * |x| / (2 * sigma))) +
              relativeEsseenConstant * (eps * fourierError mu nu eps) :=
          add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_right hC256 hA)
              (mul_le_mul_of_nonneg_right hCexp hB))
            (mul_le_mul_of_nonneg_right hC2 hE)
        _ = relativeEsseenConstant *
            (eps ^ 2 / (x ^ 2 + sigma ^ 2) +
              (eps / (eta * sigma)) *
                Real.exp (-eta * |x| / (2 * sigma)) +
              eps * fourierError mu nu eps) := by ring

/-! ### Continuous densities and the local ratio hypothesis for Lemma 6.3 -/

/-- An explicit interval-integral formulation of a continuous probability
density.  This is equivalent to saying that `mu` is the measure with density
`f`; the interval formulation is exactly what the reverse Esseen argument
uses. -/
structure HasContinuousDensity (mu : Measure ℝ) (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  nonneg : ∀ y, 0 ≤ f y
  smallBall_eq_integral : ∀ (eps x : ℝ), 0 ≤ eps →
    smallBall mu eps x = ∫ y in (x - eps)..(x + eps), f y

/-- The density ratio is at most `K` throughout the source window centered
at `x` and having radius `R eps`. -/
def DensityRatioOn (f : ℝ → ℝ) (x eps R K : ℝ) : Prop :=
  ∀ y z : Icc (x - R * eps) (x + R * eps), f y.1 ≤ K * f z.1

lemma DensityRatioOn.apply {f : ℝ → ℝ} {x eps R K y z : ℝ}
    (h : DensityRatioOn f x eps R K)
    (hy : y ∈ Icc (x - R * eps) (x + R * eps))
    (hz : z ∈ Icc (x - R * eps) (x + R * eps)) :
    f y ≤ K * f z :=
  h ⟨y, hy⟩ ⟨z, hz⟩

lemma HasContinuousDensity.intervalIntegrable
    {mu : Measure ℝ} {f : ℝ → ℝ} (h : HasContinuousDensity mu f)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  h.continuous.intervalIntegrable _ _

/-- Equal-length small balls whose two intervals lie in the ratio window
have probabilities within the same factor `K`. -/
lemma smallBall_le_mul_smallBall_of_densityRatio
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {f : ℝ → ℝ}
    (hdens : HasContinuousDensity mu f)
    {x eps R K u v : ℝ} (heps : 0 < eps)
    (hratio : DensityRatioOn f x eps R K)
    (hu : Icc (u - eps) (u + eps) ⊆ Icc (x - R * eps) (x + R * eps))
    (hv : Icc (v - eps) (v + eps) ⊆ Icc (x - R * eps) (x + R * eps)) :
    smallBall mu eps u ≤ K * smallBall mu eps v := by
  have huShift : (∫ s in (-eps)..eps, f (s + u)) =
      ∫ y in (u - eps)..(u + eps), f y := by
    convert intervalIntegral.integral_comp_add_right
      (f := f) (a := -eps) (b := eps) u using 1 <;> ring_nf
  have hvShift : (∫ s in (-eps)..eps, f (s + v)) =
      ∫ y in (v - eps)..(v + eps), f y := by
    convert intervalIntegral.integral_comp_add_right
      (f := f) (a := -eps) (b := eps) v using 1 <;> ring_nf
  rw [hdens.smallBall_eq_integral eps u heps.le,
    hdens.smallBall_eq_integral eps v heps.le, ← huShift, ← hvShift,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith)
    ((hdens.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
    ((continuous_const.mul
      (hdens.continuous.comp (continuous_id.add continuous_const))).intervalIntegrable _ _)
  intro s hs
  apply hratio.apply
  · apply hu
    change u - eps ≤ s + u ∧ s + u ≤ u + eps
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · apply hv
    change v - eps ≤ s + v ∧ s + v ≤ v + eps
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The exact local hypothesis used by the reverse Esseen argument: every
small ball contained in the comparison window is controlled by the central
small ball.  A density ratio implies this property, but the interval form is
strictly more general and is the form supplied by KSSS Theorem 5.2(2). -/
def SmallBallRatioOn (mu : Measure ℝ) (x eps R K : ℝ) : Prop :=
  ∀ u : ℝ,
    Icc (u - eps) (u + eps) ⊆ Icc (x - R * eps) (x + R * eps) →
      smallBall mu eps u ≤ K * smallBall mu eps x

lemma smallBallRatioOn_of_densityRatio
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {f : ℝ → ℝ}
    (hdens : HasContinuousDensity mu f)
    {x eps R K : ℝ} (heps : 0 < eps) (hR : 1 ≤ R)
    (hratio : DensityRatioOn f x eps R K) :
    SmallBallRatioOn mu x eps R K := by
  intro u hu
  apply smallBall_le_mul_smallBall_of_densityRatio mu hdens heps hratio hu
  intro y hy
  constructor <;> nlinarith [hy.1, hy.2, mul_le_mul_of_nonneg_right hR heps.le]

/-! ### The spatial minorant for the reverse Esseen inequality -/

/-- The nonnegative, band-limited base used in KSSS Lemma 6.3.  The
normalization is chosen so that it is bounded by one.  Written in terms of
sinc, this is `sinc (z / 4) ^ 4`. -/
def reverseEsseenBase (z : ℝ) : ℝ :=
  smoothingKernel (z / 4) ^ 2 / 16

lemma reverseEsseenBase_nonneg (z : ℝ) : 0 ≤ reverseEsseenBase z := by
  rw [reverseEsseenBase]
  positivity

lemma reverseEsseenBase_le_one (z : ℝ) : reverseEsseenBase z ≤ 1 := by
  have hk := smoothingKernel_le_four (z / 4)
  have hk0 := smoothingKernel_nonneg (z / 4)
  rw [reverseEsseenBase]
  nlinarith [sq_nonneg (smoothingKernel (z / 4))]

/-- On the quarter interval the smoothing kernel is at least three.  This
quantitative refinement of `one_le_smoothingKernel` supplies the exact
`1/8` coefficient in the reverse relative Esseen inequality. -/
lemma three_le_smoothingKernel_of_abs_le_quarter
    {u : ℝ} (hu : |u| ≤ 1 / 4) :
    3 ≤ smoothingKernel u := by
  by_cases hu0 : u = 0
  · subst u
    norm_num [smoothingKernel]
  have huabs : 0 < |u| := abs_pos.mpr hu0
  have huSq : |u| ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left huSq (abs_nonneg u)
  have herr : |u| ^ 3 / 6 ≤ |u| / 96 := by
    calc
      |u| ^ 3 / 6 = (|u| * |u| ^ 2) / 6 := by ring
      _ ≤ (|u| * (1 / 16 : ℝ)) / 6 := by gcongr
      _ = |u| / 96 := by ring
  have htri' : |u| ≤ |u - Real.sin u| + |Real.sin u| := by
    calc
      |u| = |(u - Real.sin u) + Real.sin u| := by ring_nf
      _ ≤ |u - Real.sin u| + |Real.sin u| := abs_add_le _ _
  have hsin : (95 / 96 : ℝ) * |u| ≤ |Real.sin u| := by
    linarith [Real.abs_sub_sin_le u]
  have hratio : (95 / 96 : ℝ) ≤ |Real.sin u / u| := by
    rw [abs_div]
    exact (le_div_iff₀ huabs).2 hsin
  have hratioSq : (95 / 96 : ℝ) ^ 2 ≤ |Real.sin u / u| ^ 2 := by
    exact (sq_le_sq₀ (by norm_num) (abs_nonneg _)).2 hratio
  rw [smoothingKernel, Real.sinc_of_ne_zero hu0]
  rw [← sq_abs]
  nlinarith

/-- The squared reverse-Esseen base retains at least one eighth of the
central unit interval. -/
lemma one_eighth_le_reverseEsseenBase
    {z : ℝ} (hz : |z| ≤ 1) :
    (1 / 8 : ℝ) ≤ reverseEsseenBase z := by
  have hz4 : |z / 4| ≤ 1 / 4 := by
    rw [abs_div]
    norm_num
    linarith
  have hk := three_le_smoothingKernel_of_abs_le_quarter hz4
  rw [reverseEsseenBase]
  nlinarith [sq_nonneg (smoothingKernel (z / 4))]

/-- On the unit interval the reverse-Esseen base has a fixed positive
lower bound. -/
lemma one_div_sixteen_le_reverseEsseenBase {z : ℝ} (hz : |z| ≤ 1) :
    (1 / 16 : ℝ) ≤ reverseEsseenBase z := by
  have hz4 : |z / 4| ≤ 1 := by
    rw [abs_div]
    norm_num
    linarith
  have hk := one_le_smoothingKernel hz4
  rw [reverseEsseenBase]
  nlinarith [sq_nonneg (smoothingKernel (z / 4))]

/-- The fourth-order decay of the squared smoothing kernel. -/
lemma reverseEsseenBase_le_twoFiftySix_div_pow_four {z : ℝ} (hz : z ≠ 0) :
    reverseEsseenBase z ≤ 256 / z ^ 4 := by
  have hz4 : z / 4 ≠ 0 := div_ne_zero hz (by norm_num)
  have hk := smoothingKernel_le_four_div_sq hz4
  have hk0 := smoothingKernel_nonneg (z / 4)
  have hsq : smoothingKernel (z / 4) ^ 2 ≤
      (4 / (z / 4) ^ 2) ^ 2 :=
    (sq_le_sq₀ hk0 (by positivity)).2 hk
  calc
    reverseEsseenBase z ≤ (4 / (z / 4) ^ 2) ^ 2 / 16 := by
      rw [reverseEsseenBase]
      exact div_le_div_of_nonneg_right hsq (by norm_num)
    _ = 256 / z ^ 4 := by
      field_simp [hz]
      ring

/-- The compactly band-limited spatial minorant used in reverse Esseen.
Its Fourier transform will be computed from the self-convolution of the
triangular kernel. -/
def reverseEsseenMinorant (B z : ℝ) : ℝ :=
  (1 - z ^ 2 / B ^ 2) * reverseEsseenBase z

/-- Pointwise domination by the indicator of the interval `[-B,B]`. -/
lemma reverseEsseenMinorant_le_indicator {B : ℝ} (hB : 0 < B) (z : ℝ) :
    reverseEsseenMinorant B z ≤ if |z| ≤ B then 1 else 0 := by
  by_cases hz : |z| ≤ B
  · rw [if_pos hz, reverseEsseenMinorant]
    have hzsq : z ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs z]
      exact (sq_le_sq₀ (abs_nonneg z) hB.le).2 hz
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    have hfactor0 : 0 ≤ 1 - z ^ 2 / B ^ 2 := by
      rw [sub_nonneg, div_le_one₀ hBsq]
      exact hzsq
    have hfactor1 : 1 - z ^ 2 / B ^ 2 ≤ 1 := by
      have : 0 ≤ z ^ 2 / B ^ 2 := div_nonneg (sq_nonneg z) hBsq.le
      linarith
    exact mul_le_one₀ hfactor1 (reverseEsseenBase_nonneg z)
      (reverseEsseenBase_le_one z)
  · rw [if_neg hz, reverseEsseenMinorant]
    have hlt : B < |z| := lt_of_not_ge hz
    have hsq : B ^ 2 ≤ z ^ 2 := by
      rw [← sq_abs z]
      exact (sq_le_sq₀ hB.le (abs_nonneg z)).2 hlt.le
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    have hfactor : 1 - z ^ 2 / B ^ 2 ≤ 0 := by
      rw [sub_nonpos, one_le_div₀ hBsq]
      exact hsq
    exact mul_nonpos_of_nonpos_of_nonneg hfactor
      (reverseEsseenBase_nonneg z)

/-- The minorant is uniformly positive on the unit interval once `B ≥ 4`.
The deliberately relaxed constant `1/32` leaves room for the later tail
estimate. -/
lemma one_div_thirtyTwo_le_reverseEsseenMinorant
    {B z : ℝ} (hB : 4 ≤ B) (hz : |z| ≤ 1) :
    (1 / 32 : ℝ) ≤ reverseEsseenMinorant B z := by
  have hBpos : 0 < B := by linarith
  have hzsq : z ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one z).2 hz
  have hBsq : 16 ≤ B ^ 2 := by nlinarith
  have hquot : z ^ 2 / B ^ 2 ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hBpos)).2
    nlinarith
  have hfactor : (15 / 16 : ℝ) ≤ 1 - z ^ 2 / B ^ 2 := by
    linarith
  rw [reverseEsseenMinorant]
  calc
    (1 / 32 : ℝ) ≤ (15 / 16 : ℝ) * (1 / 16 : ℝ) := by norm_num
    _ ≤ (1 - z ^ 2 / B ^ 2) * reverseEsseenBase z := by
      exact mul_le_mul hfactor (one_div_sixteen_le_reverseEsseenBase hz)
        (by norm_num) (by linarith)

/-- The negative part of the minorant has an inverse-square envelope.  This
is the source of the `R⁻¹` loss after summing cells outside the density-ratio
window. -/
lemma neg_reverseEsseenMinorant_le {B z : ℝ} (hB : 0 < B) (hz : z ≠ 0) :
    -reverseEsseenMinorant B z ≤ 256 / (B ^ 2 * z ^ 2) := by
  have hbase0 := reverseEsseenBase_nonneg z
  have hbase := reverseEsseenBase_le_twoFiftySix_div_pow_four hz
  have hquot0 : 0 ≤ z ^ 2 / B ^ 2 :=
    div_nonneg (sq_nonneg z) (sq_nonneg B)
  calc
    -reverseEsseenMinorant B z =
        (z ^ 2 / B ^ 2 - 1) * reverseEsseenBase z := by
      rw [reverseEsseenMinorant]
      ring
    _ ≤ (z ^ 2 / B ^ 2) * reverseEsseenBase z := by
      nlinarith
    _ ≤ (z ^ 2 / B ^ 2) * (256 / z ^ 4) :=
      mul_le_mul_of_nonneg_left hbase hquot0
    _ = 256 / (B ^ 2 * z ^ 2) := by
      field_simp [hB.ne', hz]

/-- Multiplication by `z²` costs only one copy of the original smoothing
kernel.  This lets the reverse argument avoid differentiating the Fourier
transform: only the squared kernel and the already established kernel are
compared on the frequency side. -/
lemma sq_mul_reverseEsseenBase_le (z : ℝ) :
    z ^ 2 * reverseEsseenBase z ≤
      4 * smoothingKernel (z / 4) := by
  by_cases hz : z = 0
  · simp [hz, reverseEsseenBase, smoothingKernel_nonneg]
  · have hz4 : z / 4 ≠ 0 := div_ne_zero hz (by norm_num)
    have hk := smoothingKernel_le_four_div_sq hz4
    have hk0 := smoothingKernel_nonneg (z / 4)
    have hsqpos : 0 < (z / 4) ^ 2 := sq_pos_of_ne_zero hz4
    have hscaled : z ^ 2 * smoothingKernel (z / 4) ≤ 64 := by
      have := (le_div_iff₀ hsqpos).1 hk
      nlinarith
    rw [reverseEsseenBase]
    calc
      z ^ 2 * (smoothingKernel (z / 4) ^ 2 / 16) =
          (z ^ 2 * smoothingKernel (z / 4) / 16) *
            smoothingKernel (z / 4) := by ring
      _ ≤ 4 * smoothingKernel (z / 4) := by
        apply mul_le_mul_of_nonneg_right _ hk0
        nlinarith

/-- A derivative-free lower envelope for the reverse minorant. -/
lemma reverseEsseenBase_sub_kernel_le_minorant
    {B : ℝ} (hB : 0 < B) (z : ℝ) :
    reverseEsseenBase z -
        (4 / B ^ 2) * smoothingKernel (z / 4) ≤
      reverseEsseenMinorant B z := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hdiv := div_le_div_of_nonneg_right
    (sq_mul_reverseEsseenBase_le z) hBsq.le
  calc
    reverseEsseenBase z -
          (4 / B ^ 2) * smoothingKernel (z / 4) =
        reverseEsseenBase z -
          (4 * smoothingKernel (z / 4)) / B ^ 2 := by ring
    _ ≤ reverseEsseenBase z -
          (z ^ 2 * reverseEsseenBase z) / B ^ 2 :=
      sub_le_sub_left hdiv _
    _ = reverseEsseenMinorant B z := by
      rw [reverseEsseenMinorant]
      ring

/-- The expectation of the squared smoothing kernel at scale `eps`. -/
def reverseEsseenBaseAverage (mu : Measure ℝ) (eps x : ℝ) : ℝ :=
  ∫ y, reverseEsseenBase ((y - x) / eps) ∂mu

lemma integrable_reverseEsseenBaseAverage
    (mu : Measure ℝ) [IsFiniteMeasure mu] (eps x : ℝ) :
    Integrable (fun y ↦ reverseEsseenBase ((y - x) / eps)) mu := by
  have hcont : Continuous (fun y : ℝ ↦
      reverseEsseenBase ((y - x) / eps)) := by
    rw [show (fun y : ℝ ↦ reverseEsseenBase ((y - x) / eps)) =
        fun y ↦ smoothingKernel (((y - x) / eps) / 4) ^ 2 / 16 by
      funext y
      rfl]
    have hkernel : Continuous (fun y : ℝ ↦
        smoothingKernel (((y - x) / eps) / 4)) :=
      continuous_smoothingKernel.comp (by fun_prop)
    exact (hkernel.pow 2).div_const 16
  refine Integrable.mono' (integrable_const (1 : ℝ))
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (reverseEsseenBase_nonneg _)]
  exact reverseEsseenBase_le_one _

/-- The squared smoothing kernel is the double Fourier integral of the two
triangular frequency kernels. -/
lemma reverseEsseenBase_fourier_double (z : ℝ) :
    (reverseEsseenBase z : ℂ) =
      (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2,
        (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
          Complex.exp (-(((t + s) * z / 4 : ℝ) : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun t ↦
    (frequencyKernel t : ℂ) *
      Complex.exp (-((t * (z / 4) : ℝ) : ℂ) * Complex.I)
  have hk : (smoothingKernel (z / 4) : ℂ) =
      ∫ t in (-2 : ℝ)..2, f t := by
    convert smoothingKernel_fourier (z / 4) using 1 <;>
      simp only [f] <;> push_cast <;> ring
  rw [reverseEsseenBase]
  push_cast
  rw [hk]
  calc
    (∫ t in (-2 : ℝ)..2, f t) ^ 2 / 16 =
        (1 / 16 : ℂ) * ((∫ t in (-2 : ℝ)..2, f t) *
          (∫ s in (-2 : ℝ)..2, f s)) := by ring
    _ = (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2,
          f t * (∫ s in (-2 : ℝ)..2, f s) := by
      rw [intervalIntegral.integral_mul_const]
    _ = (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2,
          f t * f s := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      change f t * (∫ s in (-2 : ℝ)..2, f s) =
        ∫ s in (-2 : ℝ)..2, f t * f s
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2,
        (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
          Complex.exp (-(((t : ℂ) + (s : ℂ)) * (z : ℂ) / 4) * Complex.I) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [f]
      calc
        (frequencyKernel t : ℂ) *
            Complex.exp (-((t * (z / 4) : ℝ) : ℂ) * Complex.I) *
              ((frequencyKernel s : ℂ) *
                Complex.exp (-((s * (z / 4) : ℝ) : ℂ) * Complex.I)) =
            (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
              (Complex.exp (-((t * (z / 4) : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-((s * (z / 4) : ℝ) : ℂ) * Complex.I)) := by ring
        _ = (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
              Complex.exp
                (-((t * (z / 4) : ℝ) : ℂ) * Complex.I +
                  -((s * (z / 4) : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.exp_add]
        _ = (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
              Complex.exp
                (-(((t : ℂ) + (s : ℂ)) * (z : ℂ) / 4) * Complex.I) := by
            congr 2
            push_cast
            ring

noncomputable def reverseEsseenTripleIntegrand (eps x t s y : ℝ) : ℂ :=
  (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
    Complex.exp (-((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I))

lemma reverseEsseenTripleIntegrand_norm_le (eps x t s y : ℝ) :
    ‖reverseEsseenTripleIntegrand eps x t s y‖ ≤ 4 := by
  rw [reverseEsseenTripleIntegrand, norm_mul, norm_mul]
  have hphase : ‖Complex.exp
      (-((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [show -((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I) =
        (((-((t + s) * (y - x) / (4 * eps)) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring, Complex.norm_exp_ofReal_mul_I]
  rw [hphase, mul_one]
  have ht : ‖(frequencyKernel t : ℂ)‖ ≤ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (frequencyKernel_nonneg t)] using frequencyKernel_le_two t
  have hs : ‖(frequencyKernel s : ℂ)‖ ≤ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (frequencyKernel_nonneg s)] using frequencyKernel_le_two s
  nlinarith [norm_nonneg (frequencyKernel t : ℂ),
    norm_nonneg (frequencyKernel s : ℂ)]

lemma continuous_reverseEsseenTripleIntegrand (eps x : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      reverseEsseenTripleIntegrand eps x p.1.1 p.2 p.1.2) := by
  rw [show (fun p : (ℝ × ℝ) × ℝ ↦
      reverseEsseenTripleIntegrand eps x p.1.1 p.2 p.1.2) =
      fun p ↦ (frequencyKernel p.1.1 : ℂ) * (frequencyKernel p.2 : ℂ) *
        Complex.exp
          (-((((p.1.1 + p.2) * (p.1.2 - x) / (4 * eps) : ℝ) : ℂ) * Complex.I)) by
    funext p
    rfl]
  have ht : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (frequencyKernel p.1.1 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_frequencyKernel.comp (continuous_fst.comp continuous_fst))
  have hs : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (frequencyKernel p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_frequencyKernel.comp continuous_snd)
  exact (ht.mul hs).mul (Complex.continuous_exp.comp (by fun_prop))

noncomputable def reverseEsseenDoubleIntegrand (eps x t y : ℝ) : ℂ :=
  ∫ s in (-2 : ℝ)..2, reverseEsseenTripleIntegrand eps x t s y

lemma continuous_reverseEsseenDoubleIntegrand (eps x : ℝ) :
    Continuous (Function.uncurry (reverseEsseenDoubleIntegrand eps x)) := by
  have hparam : Continuous
      (Function.uncurry (fun p : ℝ × ℝ ↦ fun s : ℝ ↦
        reverseEsseenTripleIntegrand eps x p.1 s p.2)) := by
    change Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      reverseEsseenTripleIntegrand eps x p.1.1 p.2 p.1.2)
    exact continuous_reverseEsseenTripleIntegrand eps x
  change Continuous (fun p : ℝ × ℝ ↦
    ∫ s in (-2 : ℝ)..2, reverseEsseenTripleIntegrand eps x p.1 s p.2)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hparam (-2 : ℝ) 2

lemma reverseEsseenDoubleIntegrand_norm_le (eps x t y : ℝ) :
    ‖reverseEsseenDoubleIntegrand eps x t y‖ ≤ 16 := by
  have hscont : Continuous (fun s : ℝ ↦
      ‖reverseEsseenTripleIntegrand eps x t s y‖) := by
    apply continuous_norm.comp
    rw [show (fun s : ℝ ↦ reverseEsseenTripleIntegrand eps x t s y) =
        fun s ↦ (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
          Complex.exp
            (-((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I)) by
      funext s
      rfl]
    have hs : Continuous (fun s : ℝ ↦ (frequencyKernel s : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_frequencyKernel
    exact (continuous_const.mul hs).mul
      (Complex.continuous_exp.comp (by fun_prop))
  rw [reverseEsseenDoubleIntegrand]
  calc
    ‖∫ s in (-2 : ℝ)..2, reverseEsseenTripleIntegrand eps x t s y‖ ≤
        ∫ s in (-2 : ℝ)..2, ‖reverseEsseenTripleIntegrand eps x t s y‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _s in (-2 : ℝ)..2, (4 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hscont.intervalIntegrable _ _) intervalIntegrable_const
      intro s _
      exact reverseEsseenTripleIntegrand_norm_le eps x t s y
    _ = 16 := by norm_num [intervalIntegral.integral_const]

lemma integrable_reverseEsseenDoubleIntegrand_prod
    (mu : Measure ℝ) [IsFiniteMeasure mu] (eps x : ℝ) :
    Integrable (Function.uncurry (reverseEsseenDoubleIntegrand eps x))
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := by
  let : IsFiniteMeasure (volume.restrict (uIoc (-2 : ℝ) 2)) := by
    rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    infer_instance
  have hconst : Integrable (fun _ : ℝ × ℝ ↦ (16 : ℝ))
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := integrable_const _
  refine Integrable.mono' (g := fun _ : ℝ × ℝ ↦ (16 : ℝ)) hconst
    (continuous_reverseEsseenDoubleIntegrand eps x).aestronglyMeasurable ?_
  filter_upwards with p
  change ‖reverseEsseenDoubleIntegrand eps x p.1 p.2‖ ≤ 16
  exact reverseEsseenDoubleIntegrand_norm_le eps x p.1 p.2

lemma integrable_reverseEsseenTripleIntegrand_prod
    (mu : Measure ℝ) [IsFiniteMeasure mu] (eps x t : ℝ) :
    Integrable (Function.uncurry (reverseEsseenTripleIntegrand eps x t))
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := by
  let : IsFiniteMeasure (volume.restrict (uIoc (-2 : ℝ) 2)) := by
    rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    infer_instance
  have hcont : Continuous
      (Function.uncurry (reverseEsseenTripleIntegrand eps x t)) := by
    change Continuous (fun p : ℝ × ℝ ↦
      reverseEsseenTripleIntegrand eps x t p.1 p.2)
    rw [show (fun p : ℝ × ℝ ↦
        reverseEsseenTripleIntegrand eps x t p.1 p.2) =
        fun p ↦ (frequencyKernel t : ℂ) * (frequencyKernel p.1 : ℂ) *
          Complex.exp
            (-((((t + p.1) * (p.2 - x) / (4 * eps) : ℝ) : ℂ) * Complex.I)) by
      funext p
      rfl]
    have hs : Continuous (fun p : ℝ × ℝ ↦ (frequencyKernel p.1 : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_frequencyKernel.comp continuous_fst)
    exact (continuous_const.mul hs).mul
      (Complex.continuous_exp.comp (by fun_prop))
  have hconst : Integrable (fun _ : ℝ × ℝ ↦ (4 : ℝ))
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := integrable_const _
  refine Integrable.mono' (g := fun _ : ℝ × ℝ ↦ (4 : ℝ)) hconst
    hcont.aestronglyMeasurable ?_
  filter_upwards with p
  change ‖reverseEsseenTripleIntegrand eps x t p.1 p.2‖ ≤ 4
  exact reverseEsseenTripleIntegrand_norm_le eps x t p.1 p.2

noncomputable def reverseEsseenBaseFourierAverage
    (mu : Measure ℝ) (eps x : ℝ) : ℂ :=
  (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2,
    (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
      Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I) *
        charFun mu (-(t + s) / (4 * eps))

lemma ofReal_reverseEsseenBaseAverage_eq_fourier
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    (reverseEsseenBaseAverage mu eps x : ℂ) =
      reverseEsseenBaseFourierAverage mu eps x := by
  let F : ℝ → ℝ → ℝ → ℂ := reverseEsseenTripleIntegrand eps x
  let H : ℝ → ℝ → ℂ := reverseEsseenDoubleIntegrand eps x
  let : IsFiniteMeasure (volume.restrict (uIoc (-2 : ℝ) 2)) := by
    rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    infer_instance
  have hFnorm : ∀ t s y, ‖F t s y‖ ≤ 4 := by
    intro t s y
    exact reverseEsseenTripleIntegrand_norm_le eps x t s y
  have hFcont : Continuous (fun p : (ℝ × ℝ) × ℝ ↦ F p.1.1 p.2 p.1.2) := by
    exact continuous_reverseEsseenTripleIntegrand eps x
  have hHcont : Continuous (Function.uncurry H) := by
    exact continuous_reverseEsseenDoubleIntegrand eps x
  have hHnorm : ∀ t y, ‖H t y‖ ≤ 16 := by
    intro t y
    exact reverseEsseenDoubleIntegrand_norm_le eps x t y
  have hHint : Integrable (Function.uncurry H)
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := by
    exact integrable_reverseEsseenDoubleIntegrand_prod mu eps x
  have hFint (t : ℝ) : Integrable (Function.uncurry (F t))
      ((volume.restrict (uIoc (-2 : ℝ) 2)).prod mu) := by
    exact integrable_reverseEsseenTripleIntegrand_prod mu eps x t
  have hpoint (y : ℝ) :
      (reverseEsseenBase ((y - x) / eps) : ℂ) =
        (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2, F t s y := by
    convert reverseEsseenBase_fourier_double ((y - x) / eps) using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [F, reverseEsseenTripleIntegrand]
    congr 2
    push_cast
    field_simp [heps.ne']
  rw [reverseEsseenBaseAverage, ← integral_complex_ofReal]
  calc
    (∫ y, (reverseEsseenBase ((y - x) / eps) : ℂ) ∂mu) =
        ∫ y, (1 / 16 : ℂ) *
          (∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2, F t s y) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (1 / 16 : ℂ) * ∫ y,
          (∫ t in (-2 : ℝ)..2, H t y) ∂mu := by
      rw [integral_const_mul]
      congr 1
    _ = (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ y, H t y ∂mu := by
      rw [intervalIntegral_integral_swap hHint]
    _ = (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2,
          ∫ s in (-2 : ℝ)..2, ∫ y, F t s y ∂mu := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [H, reverseEsseenDoubleIntegrand, F]
      rw [intervalIntegral_integral_swap (hFint t)]
    _ = reverseEsseenBaseFourierAverage mu eps x := by
      rw [reverseEsseenBaseFourierAverage]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [F, reverseEsseenTripleIntegrand]
      calc
        (∫ y, (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
            Complex.exp
              (-((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I)) ∂mu) =
            (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
              ∫ y, Complex.exp
                (-((((t + s) * (y - x) / (4 * eps) : ℝ) : ℂ) * Complex.I)) ∂mu := by
          rw [integral_const_mul]
        _ = (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
            ∫ y, Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I) *
              Complex.exp ((-(t + s) / (4 * eps) * y : ℝ) * Complex.I) ∂mu := by
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          rw [← Complex.exp_add]
          congr 2
          push_cast
          field_simp [heps.ne']
          ring
        _ = (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
            (Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I) *
              ∫ y, Complex.exp ((-(t + s) / (4 * eps) * y : ℝ) *
                Complex.I) ∂mu) := by
          rw [integral_const_mul]
        _ = (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
            Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I) *
              charFun mu (-(t + s) / (4 * eps)) := by
          rw [← mul_assoc, charFun_apply_real]
          congr 1
          apply integral_congr_ae
          filter_upwards with y
          congr 1
          push_cast
          ring

lemma integral_shifted_charFunDiff_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps t : ℝ} (heps : 0 < eps) (ht : t ∈ Icc (-2 : ℝ) 2) :
    (∫ s in (-2 : ℝ)..2,
      ‖charFun mu (-(t + s) / (4 * eps)) -
        charFun nu (-(t + s) / (4 * eps))‖) ≤
      4 * eps * fourierError mu nu eps := by
  let g : ℝ → ℝ := fun u ↦ ‖charFun mu u - charFun nu u‖
  have hg : Continuous g :=
    continuous_norm.comp (continuous_charFun.sub continuous_charFun)
  let c : ℝ := -1 / (4 * eps)
  let d : ℝ := -t / (4 * eps)
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hsub := intervalIntegral.integral_comp_mul_add
    (f := g) (a := (-2 : ℝ)) (b := 2) (c := c) hc d
  have hchange : (fun s : ℝ ↦
      ‖charFun mu (-(t + s) / (4 * eps)) -
        charFun nu (-(t + s) / (4 * eps))‖) =
      fun s ↦ g (c * s + d) := by
    funext s
    dsimp only [g, c, d]
    congr 2 <;> field_simp [heps.ne'] <;> ring_nf
  have hlower : -(2 / eps) ≤ -(t + 2) / (4 * eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) heps)).2
    have hscale : -(2 / eps) * (4 * eps) = (-8 : ℝ) := by
      field_simp [heps.ne']
      norm_num
    rw [hscale]
    linarith [ht.2]
  have hmiddle : -(t + 2) / (4 * eps) ≤ (2 - t) / (4 * eps) := by
    apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) heps)).2
    linarith
  have hupper : (2 - t) / (4 * eps) ≤ 2 / eps := by
    apply (div_le_iff₀ (mul_pos (by norm_num) heps)).2
    have hscale : (2 / eps) * (4 * eps) = (8 : ℝ) := by
      field_simp [heps.ne']
      norm_num
    rw [hscale]
    linarith [ht.1]
  have hmono :
      (∫ u in -(t + 2) / (4 * eps)..(2 - t) / (4 * eps), g u) ≤
        ∫ u in -(2 / eps)..(2 / eps), g u := by
    apply intervalIntegral.integral_mono_interval hlower hmiddle hupper
    · exact Filter.Eventually.of_forall fun u ↦ norm_nonneg _
    · exact hg.intervalIntegrable _ _
  rw [hchange]
  calc
    (∫ s in (-2 : ℝ)..2, g (c * s + d)) =
        c⁻¹ * ∫ u in c * (-2) + d..c * 2 + d, g u := by
      simpa only [smul_eq_mul] using hsub
    _ = 4 * eps *
        ∫ u in -(t + 2) / (4 * eps)..(2 - t) / (4 * eps), g u := by
      have hcinv : c⁻¹ = -(4 * eps) := by
        dsimp only [c]
        field_simp [heps.ne']
      have hleft : c * (-2) + d = (2 - t) / (4 * eps) := by
        dsimp only [c, d]
        field_simp [heps.ne']
        ring
      have hright : c * 2 + d = -(t + 2) / (4 * eps) := by
        dsimp only [c, d]
        field_simp [heps.ne']
        ring
      rw [hcinv, hleft, hright, intervalIntegral.integral_symm]
      ring
    _ ≤ 4 * eps * ∫ u in -(2 / eps)..(2 / eps), g u := by
      exact mul_le_mul_of_nonneg_left hmono (mul_nonneg (by norm_num) heps.le)
    _ = 4 * eps * fourierError mu nu eps := by
      rw [fourierError]

lemma norm_reverseEsseenBaseFourierAverage_sub_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    ‖reverseEsseenBaseFourierAverage mu eps x -
        reverseEsseenBaseFourierAverage nu eps x‖ ≤
      4 * eps * fourierError mu nu eps := by
  let A : Measure ℝ → ℝ → ℝ → ℂ := fun rho t s ↦
    (frequencyKernel t : ℂ) * (frequencyKernel s : ℂ) *
      Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I) *
        charFun rho (-(t + s) / (4 * eps))
  let D : ℝ → ℝ → ℂ := fun t s ↦ A mu t s - A nu t s
  have hAcont (rho : Measure ℝ) [IsFiniteMeasure rho] :
      Continuous (Function.uncurry (A rho)) := by
    dsimp only [A, Function.uncurry_apply_pair]
    have ht : Continuous (fun p : ℝ × ℝ ↦
        (frequencyKernel p.1 : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_frequencyKernel.comp continuous_fst)
    have hs : Continuous (fun p : ℝ × ℝ ↦
        (frequencyKernel p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_frequencyKernel.comp continuous_snd)
    exact (((ht.mul hs).mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_charFun.comp (by fun_prop)))
  have hDcont : Continuous (Function.uncurry D) := by
    exact (hAcont mu).sub (hAcont nu)
  have hAinnerCont (rho : Measure ℝ) [IsFiniteMeasure rho] :
      Continuous (fun t ↦ ∫ s in (-2 : ℝ)..2, A rho t s) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hAcont rho) (-2 : ℝ) 2
  have hDinnerCont : Continuous (fun t ↦ ∫ s in (-2 : ℝ)..2, D t s) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hDcont (-2 : ℝ) 2
  have hrepl : reverseEsseenBaseFourierAverage mu eps x -
      reverseEsseenBaseFourierAverage nu eps x =
        (1 / 16 : ℂ) * ∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2, D t s := by
    rw [reverseEsseenBaseFourierAverage,
      reverseEsseenBaseFourierAverage]
    rw [← mul_sub]
    congr 1
    rw [← intervalIntegral.integral_sub
      ((hAinnerCont mu).intervalIntegrable (-2 : ℝ) 2)
      ((hAinnerCont nu).intervalIntegrable (-2 : ℝ) 2)]
    apply intervalIntegral.integral_congr
    intro t _
    have hmuInt : IntervalIntegrable (fun s : ℝ ↦ A mu t s) volume (-2 : ℝ) 2 := by
      exact ((hAcont mu).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hnuInt : IntervalIntegrable (fun s : ℝ ↦ A nu t s) volume (-2 : ℝ) 2 := by
      exact ((hAcont nu).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    change (∫ s in (-2 : ℝ)..2, A mu t s) -
      (∫ s in (-2 : ℝ)..2, A nu t s) =
        ∫ s in (-2 : ℝ)..2, D t s
    rw [← intervalIntegral.integral_sub
      hmuInt hnuInt]
  have hDnorm : ∀ t s,
      ‖D t s‖ ≤ 4 *
        ‖charFun mu (-(t + s) / (4 * eps)) -
          charFun nu (-(t + s) / (4 * eps))‖ := by
    intro t s
    dsimp only [D, A]
    rw [← mul_sub]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have ht : ‖(frequencyKernel t : ℂ)‖ ≤ 2 := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (frequencyKernel_nonneg t)] using frequencyKernel_le_two t
    have hs : ‖(frequencyKernel s : ℂ)‖ ≤ 2 := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (frequencyKernel_nonneg s)] using frequencyKernel_le_two s
    have hprod : ‖(frequencyKernel t : ℂ)‖ *
        ‖(frequencyKernel s : ℂ)‖ ≤ 4 := by
      nlinarith [norm_nonneg (frequencyKernel t : ℂ),
        norm_nonneg (frequencyKernel s : ℂ)]
    exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  have hinner : ∀ t ∈ Icc (-2 : ℝ) 2,
      ‖∫ s in (-2 : ℝ)..2, D t s‖ ≤
        16 * eps * fourierError mu nu eps := by
    intro t ht
    have hargCont : Continuous (fun s : ℝ ↦ -(t + s) / (4 * eps)) := by
      fun_prop
    have hfreqCont : Continuous (fun s : ℝ ↦ (frequencyKernel s : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_frequencyKernel
    have hphaseCont : Continuous (fun s : ℝ ↦
        Complex.exp (((t + s) * x / (4 * eps) : ℝ) * Complex.I)) := by
      exact Complex.continuous_exp.comp (by fun_prop)
    have hmuSliceCont : Continuous (fun s : ℝ ↦ A mu t s) := by
      dsimp only [A]
      exact (((continuous_const.mul hfreqCont).mul hphaseCont).mul
        (continuous_charFun.comp hargCont))
    have hnuSliceCont : Continuous (fun s : ℝ ↦ A nu t s) := by
      dsimp only [A]
      exact (((continuous_const.mul hfreqCont).mul hphaseCont).mul
        (continuous_charFun.comp hargCont))
    have hDsliceCont : Continuous (fun s : ℝ ↦ ‖D t s‖) := by
      apply continuous_norm.comp
      change Continuous (fun s : ℝ ↦ A mu t s - A nu t s)
      exact hmuSliceCont.sub hnuSliceCont
    have hcharNormCont : Continuous (fun s : ℝ ↦ 4 *
        ‖charFun mu (-(t + s) / (4 * eps)) -
          charFun nu (-(t + s) / (4 * eps))‖) := by
      exact continuous_const.mul (continuous_norm.comp
        ((continuous_charFun.comp hargCont).sub
          (continuous_charFun.comp hargCont)))
    calc
      ‖∫ s in (-2 : ℝ)..2, D t s‖ ≤
          ∫ s in (-2 : ℝ)..2, ‖D t s‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ s in (-2 : ℝ)..2, 4 *
          ‖charFun mu (-(t + s) / (4 * eps)) -
            charFun nu (-(t + s) / (4 * eps))‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hDsliceCont.intervalIntegrable _ _)
          (hcharNormCont.intervalIntegrable _ _)
        intro s _
        exact hDnorm t s
      _ = 4 * (∫ s in (-2 : ℝ)..2,
          ‖charFun mu (-(t + s) / (4 * eps)) -
            charFun nu (-(t + s) / (4 * eps))‖) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ 4 * (4 * eps * fourierError mu nu eps) := by
        exact mul_le_mul_of_nonneg_left
          (integral_shifted_charFunDiff_le mu nu heps ht) (by norm_num)
      _ = 16 * eps * fourierError mu nu eps := by ring
  rw [hrepl, norm_mul]
  have hconstNorm : ‖(1 / 16 : ℂ)‖ = (1 / 16 : ℝ) := by norm_num
  rw [hconstNorm]
  calc
    (1 / 16 : ℝ) * ‖∫ t in (-2 : ℝ)..2, ∫ s in (-2 : ℝ)..2, D t s‖ ≤
        (1 / 16 : ℝ) * ∫ t in (-2 : ℝ)..2,
          ‖∫ s in (-2 : ℝ)..2, D t s‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ (1 / 16 : ℝ) * ∫ _t in (-2 : ℝ)..2,
          16 * eps * fourierError mu nu eps := by
      gcongr
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_norm.comp hDinnerCont).intervalIntegrable _ _)
        intervalIntegrable_const
      intro t ht
      exact hinner t ht
    _ = 4 * eps * fourierError mu nu eps := by
      norm_num [intervalIntegral.integral_const]
      ring

lemma reverseEsseenBaseAverage_le_add_fourierError
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    reverseEsseenBaseAverage mu eps x ≤
      reverseEsseenBaseAverage nu eps x +
        4 * eps * fourierError mu nu eps := by
  have hmu := ofReal_reverseEsseenBaseAverage_eq_fourier mu heps x
  have hnu := ofReal_reverseEsseenBaseAverage_eq_fourier nu heps x
  have hnorm : |reverseEsseenBaseAverage mu eps x -
      reverseEsseenBaseAverage nu eps x| =
      ‖reverseEsseenBaseFourierAverage mu eps x -
        reverseEsseenBaseFourierAverage nu eps x‖ := by
    calc
      |reverseEsseenBaseAverage mu eps x - reverseEsseenBaseAverage nu eps x| =
          ‖((reverseEsseenBaseAverage mu eps x -
            reverseEsseenBaseAverage nu eps x : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖reverseEsseenBaseFourierAverage mu eps x -
          reverseEsseenBaseFourierAverage nu eps x‖ := by
        congr 1
        push_cast
        rw [hmu, hnu]
  have hdiff : reverseEsseenBaseAverage mu eps x -
      reverseEsseenBaseAverage nu eps x ≤
        4 * eps * fourierError mu nu eps := by
    calc
      reverseEsseenBaseAverage mu eps x - reverseEsseenBaseAverage nu eps x ≤
          |reverseEsseenBaseAverage mu eps x -
            reverseEsseenBaseAverage nu eps x| := le_abs_self _
      _ = ‖reverseEsseenBaseFourierAverage mu eps x -
          reverseEsseenBaseFourierAverage nu eps x‖ := hnorm
      _ ≤ 4 * eps * fourierError mu nu eps :=
        norm_reverseEsseenBaseFourierAverage_sub_le mu nu heps x
  linarith

/-- The squared kernel retains a fixed fraction of the mass in the central
radius-`eps` interval. -/
lemma one_div_sixteen_mul_smallBall_le_reverseEsseenBaseAverage
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    (1 / 16 : ℝ) * smallBall mu eps x ≤
      reverseEsseenBaseAverage mu eps x := by
  rw [smallBall, reverseEsseenBaseAverage,
    ← integral_indicator_one measurableSet_Icc,
    ← integral_const_mul]
  apply integral_mono
  · exact (Integrable.indicator (integrable_const (1 : ℝ))
      measurableSet_Icc).const_mul _
  · exact integrable_reverseEsseenBaseAverage mu eps x
  · intro y
    change (1 / 16 : ℝ) * (Icc (x - eps) (x + eps)).indicator 1 y ≤
      reverseEsseenBase ((y - x) / eps)
    by_cases hy : y ∈ Icc (x - eps) (x + eps)
    · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
      apply one_div_sixteen_le_reverseEsseenBase
      rw [abs_div, abs_of_pos heps]
      apply (div_le_one heps).2
      exact (abs_le).2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rw [Set.indicator_of_notMem hy, mul_zero]
      exact reverseEsseenBase_nonneg _

/-- The sharpened central-mass bound used in the final form of KSSS
Lemma 6.3. -/
lemma one_eighth_mul_smallBall_le_reverseEsseenBaseAverage
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    (1 / 8 : ℝ) * smallBall mu eps x ≤
      reverseEsseenBaseAverage mu eps x := by
  rw [smallBall, reverseEsseenBaseAverage,
    ← integral_indicator_one measurableSet_Icc,
    ← integral_const_mul]
  apply integral_mono
  · exact (Integrable.indicator (integrable_const (1 : ℝ))
      measurableSet_Icc).const_mul _
  · exact integrable_reverseEsseenBaseAverage mu eps x
  · intro y
    change (1 / 8 : ℝ) * (Icc (x - eps) (x + eps)).indicator 1 y ≤
      reverseEsseenBase ((y - x) / eps)
    by_cases hy : y ∈ Icc (x - eps) (x + eps)
    · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
      apply one_eighth_le_reverseEsseenBase
      rw [abs_div, abs_of_pos heps]
      apply (div_le_one heps).2
      exact (abs_le).2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rw [Set.indicator_of_notMem hy, mul_zero]
      exact reverseEsseenBase_nonneg _

/-- A radius-`4 eps` interval is covered by four radius-`eps` intervals.
This finite covering is the only radius conversion needed by the
derivative-free reverse-Esseen argument. -/
lemma smallBall_four_mul_le_concentration
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    smallBall mu (4 * eps) x ≤ 4 * concentration mu eps := by
  let A := Icc (x - 4 * eps) (x - 2 * eps)
  let B := Icc (x - 2 * eps) x
  let C := Icc x (x + 2 * eps)
  let D := Icc (x + 2 * eps) (x + 4 * eps)
  have hcover : Icc (x - 4 * eps) (x + 4 * eps) ⊆
      A ∪ (B ∪ (C ∪ D)) := by
    intro y hy
    by_cases hA : y ≤ x - 2 * eps
    · exact Or.inl ⟨hy.1, hA⟩
    · right
      by_cases hB : y ≤ x
      · exact Or.inl ⟨by linarith, hB⟩
      · right
        by_cases hC : y ≤ x + 2 * eps
        · exact Or.inl ⟨by linarith, hC⟩
        · exact Or.inr ⟨by linarith, hy.2⟩
  have hmono :
      mu.real (Icc (x - 4 * eps) (x + 4 * eps)) ≤
        mu.real (A ∪ (B ∪ (C ∪ D))) :=
    measureReal_mono hcover
  have hABCD : mu.real (A ∪ (B ∪ (C ∪ D))) ≤
      mu.real A + mu.real (B ∪ (C ∪ D)) :=
    measureReal_union_le A (B ∪ (C ∪ D))
  have hBCD : mu.real (B ∪ (C ∪ D)) ≤
      mu.real B + mu.real (C ∪ D) :=
    measureReal_union_le B (C ∪ D)
  have hCD : mu.real (C ∪ D) ≤ mu.real C + mu.real D :=
    measureReal_union_le C D
  have hA : mu.real A ≤ concentration mu eps := by
    dsimp [A]
    convert smallBall_le_concentration mu eps (x - 3 * eps) using 1 <;>
      simp only [smallBall] <;> ring_nf
  have hB : mu.real B ≤ concentration mu eps := by
    dsimp [B]
    convert smallBall_le_concentration mu eps (x - eps) using 1 <;>
      simp only [smallBall] <;> ring_nf
  have hC : mu.real C ≤ concentration mu eps := by
    dsimp [C]
    convert smallBall_le_concentration mu eps (x + eps) using 1 <;>
      simp only [smallBall] <;> ring_nf
  have hD : mu.real D ≤ concentration mu eps := by
    dsimp [D]
    convert smallBall_le_concentration mu eps (x + 3 * eps) using 1 <;>
      simp only [smallBall] <;> ring_nf
  rw [smallBall]
  linarith

/-- The spatial half of reverse Esseen.  The large interval majorizes a
squared-kernel average, with a correction involving only the original
smoothing kernel. -/
lemma reverseEsseenBaseAverage_sub_kernelAverage_le_smallBall
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps B : ℝ} (heps : 0 < eps) (hB : 0 < B) (x : ℝ) :
    reverseEsseenBaseAverage mu eps x -
        (4 / B ^ 2) * kernelAverage mu (4 * eps) x ≤
      smallBall mu (B * eps) x := by
  have hbase : Integrable (fun y : ℝ ↦
      reverseEsseenBase ((y - x) / eps)) mu :=
    integrable_reverseEsseenBaseAverage mu eps x
  have hfourEps : 4 * eps ≠ 0 := mul_ne_zero (by norm_num) heps.ne'
  have hkernel : Integrable (fun y : ℝ ↦
      smoothingKernel ((y - x) / (4 * eps))) mu :=
    integrable_kernelAverage mu hfourEps x
  have hscaledKernel : Integrable (fun y : ℝ ↦
      (4 / B ^ 2) * smoothingKernel ((y - x) / (4 * eps))) mu :=
    hkernel.const_mul _
  have hpoint : ∀ y : ℝ,
      reverseEsseenBase ((y - x) / eps) -
          (4 / B ^ 2) * smoothingKernel ((y - x) / (4 * eps)) ≤
        (Icc (x - B * eps) (x + B * eps)).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) y := by
    intro y
    let z : ℝ := (y - x) / eps
    have hscale : (y - x) / (4 * eps) = z / 4 := by
      dsimp only [z]
      field_simp [heps.ne']
    rw [hscale]
    calc
      reverseEsseenBase z -
            (4 / B ^ 2) * smoothingKernel (z / 4) ≤
          reverseEsseenMinorant B z :=
        reverseEsseenBase_sub_kernel_le_minorant hB z
      _ ≤ if |z| ≤ B then 1 else 0 :=
        reverseEsseenMinorant_le_indicator hB z
      _ = (Icc (x - B * eps) (x + B * eps)).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) y := by
        by_cases hz : |z| ≤ B
        · have habs : |y - x| ≤ B * eps := by
            rw [abs_div, abs_of_pos heps] at hz
            exact (div_le_iff₀ heps).1 hz
          have hy : y ∈ Icc (x - B * eps) (x + B * eps) := by
            rcases (abs_le).1 habs with ⟨hlo, hhi⟩
            constructor <;> linarith
          rw [if_pos hz, Set.indicator_of_mem hy]
        · have hy : y ∉ Icc (x - B * eps) (x + B * eps) := by
            intro hy
            apply hz
            have habs : |y - x| ≤ B * eps := by
              apply (abs_le).2
              exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
            dsimp only [z]
            rw [abs_div, abs_of_pos heps]
            exact (div_le_iff₀ heps).2 habs
          rw [if_neg hz, Set.indicator_of_notMem hy]
  calc
    reverseEsseenBaseAverage mu eps x -
          (4 / B ^ 2) * kernelAverage mu (4 * eps) x =
        ∫ y, (reverseEsseenBase ((y - x) / eps) -
          (4 / B ^ 2) * smoothingKernel ((y - x) / (4 * eps))) ∂mu := by
      rw [reverseEsseenBaseAverage, kernelAverage,
        integral_sub hbase hscaledKernel, integral_const_mul]
    _ ≤ ∫ y, (Icc (x - B * eps) (x + B * eps)).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) y ∂mu := by
      apply integral_mono (hbase.sub hscaledKernel)
        (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc)
      exact hpoint
    _ = smallBall mu (B * eps) x := by
      rw [smallBall, ← integral_indicator_one measurableSet_Icc]
      congr 1

/-! ### The spatial summation and Fourier comparison for KSSS Lemma 6.3 -/

lemma tsum_nat_if_ge_le_shift
    {f : ℕ → ℝ} (hf : Summable f) (hn : ∀ n, 0 ≤ f n) (N : ℕ) :
    (∑' n : ℕ, if N ≤ n then f n else 0) ≤
      ∑' n : ℕ, f (n + N) := by
  let S : Set ℕ := {n | N ≤ n}
  have hshift : Summable (fun n : ℕ ↦ f (n + N)) :=
    (summable_nat_add_iff N).2 hf
  let i : S → ℕ := fun n ↦ n.1 - N
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    dsimp only [i] at hab
    have ha : N ≤ a.1 := a.2
    have hb : N ≤ b.1 := b.2
    omega
  have hle := tsum_comp_le_tsum_of_inj hshift
    (fun n ↦ hn (n + N)) hi
  have hsub : (∑' n : S, f n.1) =
      ∑' n : ℕ, if N ≤ n then f n else 0 := by
    rw [tsum_subtype]
    apply tsum_congr
    intro n
    by_cases hNn : N ≤ n
    · simp [S, hNn]
    · simp [S, hNn]
  rw [← hsub]
  calc
    (∑' n : S, f n.1) = ∑' n : S, f (i n + N) := by
      apply tsum_congr
      intro n
      congr 1
      dsimp only [i]
      exact (Nat.sub_add_cancel n.2).symm
    _ ≤ ∑' n : ℕ, f (n + N) := hle

lemma tsum_nat_kernelCellWeight_tail
    (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ,
      if N ≤ n then kernelCellWeight (n : ℤ) else 0) ≤ 32 / N := by
  let f : ℕ → ℝ := fun n ↦ kernelCellWeight (n : ℤ)
  have hf : Summable f := summable_kernelCellWeight.comp_injective Nat.cast_injective
  have htail := tsum_nat_if_ge_le_shift hf
    (fun n ↦ kernelCellWeight_nonneg (n : ℤ)) N
  let g : ℝ → ℝ := fun x ↦ 16 * x ^ (-2 : ℝ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hganti : AntitoneOn g (Ici (N : ℝ)) := by
    intro a ha b hb hab
    dsimp only [g]
    have hrpow := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (r := (-2 : ℝ)) (by norm_num)
      (show a ∈ Ioi (0 : ℝ) by exact hNpos.trans_le ha)
      (show b ∈ Ioi (0 : ℝ) by exact hNpos.trans_le hb) hab
    nlinarith
  have hgint : IntegrableOn g (Ioi (N : ℝ)) := by
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hNpos).const_mul 16
  have hg0 : ∀ t ∈ Ioi (N : ℝ), 0 ≤ g t := by
    intro t ht
    dsimp only [g]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (hNpos.trans ht).le _)
  have hgintegral : (∫ x in Ioi (N : ℝ), g x) = 16 / N := by
    rw [show g = fun x : ℝ ↦ 16 * x ^ (-2 : ℝ) by rfl,
      integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hNpos]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have hgtail := AntitoneOn.tsum_comp_add_le_integral N hganti hgint hg0
  have hgSum : Summable (fun n : ℕ ↦ g (n + N : ℕ)) := by
    have hbase0 : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have hbase : Summable (fun n : ℕ ↦ 16 / (n : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using hbase0.mul_left 16
    refine ((summable_nat_add_iff N).2 hbase).congr (fun n ↦ ?_)
    dsimp only [g]
    have hposNat : 0 < n + N := by omega
    have hpos : (0 : ℝ) < n + N := by exact_mod_cast hposNat
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    ring
  have hshiftMajor : (∑' n : ℕ, f (n + N)) ≤
      ∑' n : ℕ, g (n + N : ℕ) := by
    apply Summable.tsum_le_tsum
    · intro n
      dsimp only [f, g]
      rw [kernelCellWeight]
      have hposNat : 0 < n + N := by omega
      have hpos : (0 : ℝ) < n + N := by exact_mod_cast hposNat
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀
        (by positivity : 0 < ((n + N : ℕ) : ℝ) ^ 2 + 1)
        (by positivity : 0 < ((n + N : ℕ) : ℝ) ^ 2)).2
      nlinarith
    · exact hf.comp_injective (fun a b h ↦ by omega)
    · exact hgSum
  calc
    (∑' n : ℕ, if N ≤ n then kernelCellWeight (n : ℤ) else 0) ≤
        ∑' n : ℕ, f (n + N) := htail
    _ ≤ ∑' n : ℕ, g (n + N : ℕ) := hshiftMajor
    _ = g N + ∑' n : ℕ, g (n + N + 1 : ℕ) := by
      rw [hgSum.tsum_eq_zero_add]
      simp only [zero_add]
      congr 1
      apply tsum_congr
      intro n
      congr 1
      push_cast
      ring
    _ ≤ 16 / N + 16 / N := by
      gcongr
      · dsimp only [g]
        rw [Real.rpow_neg (by positivity), Real.rpow_two]
        rw [← div_eq_mul_inv]
        apply (div_le_div_iff₀ (sq_pos_of_pos hNpos) hNpos).2
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
      · rw [← hgintegral]
        exact hgtail
    _ = 32 / N := by ring

lemma tsum_int_kernelCellWeight_tail
    (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℤ,
      if N ≤ k.natAbs then kernelCellWeight k else 0) ≤ 64 / N := by
  let f : ℤ → ℝ := fun k ↦
    if N ≤ k.natAbs then kernelCellWeight k else 0
  have hf : Summable f := by
    exact summable_kernelCellWeight.of_norm_bounded (fun k ↦ by
      dsimp only [f]
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellWeight_nonneg k)]
      · simp [kernelCellWeight_nonneg])
  have hsplit := tsum_of_nat_of_neg_add_one
    (hf.comp_injective Nat.cast_injective)
    (hf.comp_injective (@Int.negSucc.inj))
  have hpos : (∑' n : ℕ, f n) ≤ 32 / N := by
    simpa [f] using
      tsum_nat_kernelCellWeight_tail N hN
  have hneg : (∑' n : ℕ, f (-(n + 1))) ≤ ∑' n : ℕ, f n := by
    let p : ℕ → ℝ := fun n ↦ f (n : ℤ)
    have hp : Summable p := hf.comp_injective Nat.cast_injective
    have hpn : ∀ n, 0 ≤ p n := by
      intro n
      dsimp only [p, f]
      split_ifs
      · exact kernelCellWeight_nonneg (n : ℤ)
      · exact le_rfl
    have hsucc := tsum_comp_le_tsum_of_inj hp hpn Nat.succ_injective
    calc
      (∑' n : ℕ, f (-(n + 1))) = ∑' n : ℕ, p (n + 1) := by
        apply tsum_congr
        intro n
        dsimp only [p, f]
        simp only [Int.natAbs_neg, Nat.cast_add, Nat.cast_one]
        congr 1
        simp only [kernelCellWeight]
        push_cast
        ring
      _ ≤ ∑' n : ℕ, p n := by
        simpa [Function.comp_def] using hsucc
      _ = ∑' n : ℕ, f n := by rfl
  rw [hsplit]
  calc
    (∑' n : ℕ, f n) + ∑' n : ℕ, f (-(n + 1)) ≤
        32 / N + 32 / N := add_le_add hpos (hneg.trans hpos)
    _ = 64 / N := by ring

lemma kernelCell_ball_subset_ratioWindow
    {x eps R : ℝ} (heps : 0 < eps) {N : ℕ}
    (hNle : (N : ℝ) ≤ R / 4) (hR : 4 ≤ R) {k : ℤ}
    (hk : k.natAbs < N) :
    Icc (x + ((2 * (k : ℝ) + 1) * eps) - eps)
        (x + ((2 * (k : ℝ) + 1) * eps) + eps) ⊆
      Icc (x - R * eps) (x + R * eps) := by
  have hkabs : |(k : ℝ)| < N := by
    have hk' : ((k.natAbs : ℕ) : ℝ) < N := by
      exact_mod_cast hk
    simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hk'
  have hklo : -(N : ℝ) < k := by
    exact (abs_lt.1 hkabs).1
  have hkhi : (k : ℝ) < N := by
    exact (abs_lt.1 hkabs).2
  intro y hy
  constructor
  · have hRN : 2 * (N : ℝ) ≤ R := by linarith
    nlinarith [hy.1]
  · have hRN : 2 * (N : ℝ) + 2 ≤ R := by linarith
    nlinarith [hy.2]

lemma center_ball_subset_ratioWindow
    {x eps R : ℝ} (heps : 0 < eps) (hR : 1 ≤ R) :
    Icc (x - eps) (x + eps) ⊆ Icc (x - R * eps) (x + R * eps) := by
  intro y hy
  constructor <;> nlinarith [hy.1, hy.2]

lemma smoothingKernel_four_scale_on_kernelCell_le
    {x y eps : ℝ} (heps : 0 < eps) {k : ℤ}
    (hy : y ∈ kernelCell x eps k) :
    smoothingKernel ((y - x) / (4 * eps)) ≤ 8 * kernelCellWeight k := by
  have hy' := hy
  rw [kernelCell] at hy'
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hy'
  have hzlow : 2 * (k : ℝ) ≤ (y - x) / eps := by
    apply (le_div_iff₀ heps).2
    nlinarith [hy'.1]
  have hzup : (y - x) / eps < 2 * ((k : ℝ) + 1) := by
    apply (div_lt_iff₀ heps).2
    nlinarith [hy'.2]
  by_cases hk0 : k = 0
  · subst k
    rw [kernelCellWeight]
    norm_num
    exact (smoothingKernel_le_four _).trans (by norm_num)
  by_cases hkm1 : k = -1
  · subst k
    rw [kernelCellWeight]
    norm_num
    exact (smoothingKernel_le_four _).trans (by norm_num)
  have hkCases : (1 : ℤ) ≤ k ∨ k ≤ -2 := by omega
  have hsq : (k : ℝ) ^ 2 ≤ ((y - x) / eps) ^ 2 := by
    rcases hkCases with hk | hk
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    · have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast hk
      nlinarith
  have hscale : (y - x) / (4 * eps) = ((y - x) / eps) / 4 := by
    field_simp [heps.ne']
  rw [hscale]
  calc
    smoothingKernel (((y - x) / eps) / 4) ≤
        8 / ((((y - x) / eps) / 4) ^ 2 + 1) := smoothingKernel_le_eight_div _
    _ ≤ 128 / ((k : ℝ) ^ 2 + 1) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < (((y - x) / eps) / 4) ^ 2 + 1)
        (by positivity : 0 < (k : ℝ) ^ 2 + 1)).2
      nlinarith
    _ = 8 * kernelCellWeight k := by
      rw [kernelCellWeight]
      ring

lemma smoothingKernel_four_scale_le_tsum
    {x y eps : ℝ} (heps : 0 < eps) :
    smoothingKernel ((y - x) / (4 * eps)) ≤
      8 * ∑' k : ℤ, kernelCellTerm x eps k y := by
  have hyuniv : y ∈ ⋃ k : ℤ, kernelCell x eps k := by
    rw [iUnion_kernelCell x heps]
    exact mem_univ y
  rcases mem_iUnion.1 hyuniv with ⟨k, hyk⟩
  calc
    smoothingKernel ((y - x) / (4 * eps)) ≤
        8 * kernelCellWeight k :=
      smoothingKernel_four_scale_on_kernelCell_le heps hyk
    _ = 8 * kernelCellTerm x eps k y := by
      simp [kernelCellTerm, hyk]
    _ ≤ 8 * ∑' j : ℤ, kernelCellTerm x eps j y := by
      gcongr
      have hsum := (summable_kernelCellTerm x eps y).sum_le_tsum {k}
        (fun j _ ↦ kernelCellTerm_nonneg x eps j y)
      simpa using hsum

lemma kernelAverage_four_mul_le_weightedCells
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu (4 * eps) x ≤
      8 * ∑' k : ℤ,
        mu.real (kernelCell x eps k) * kernelCellWeight k := by
  have htermInt : ∀ k : ℤ, Integrable (kernelCellTerm x eps k) mu :=
    kernelCellTerm_integrable mu x eps
  have hnormSum : Summable
      (fun k : ℤ ↦ ∫ y, ‖kernelCellTerm x eps k y‖ ∂mu) := by
    refine summable_kernelCellWeight.of_norm_bounded (fun k ↦ ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y ↦ norm_nonneg _),
      integral_norm_kernelCellTerm]
    have hprob : mu.real (kernelCell x eps k) ≤ 1 := by
      calc
        mu.real (kernelCell x eps k) ≤ mu.real univ :=
          measureReal_mono (subset_univ _)
        _ = 1 := by simp
    calc
      mu.real (kernelCell x eps k) * kernelCellWeight k ≤
          1 * kernelCellWeight k :=
        mul_le_mul_of_nonneg_right hprob (kernelCellWeight_nonneg k)
      _ = kernelCellWeight k := one_mul _
  rw [kernelAverage]
  calc
    (∫ y, smoothingKernel ((y - x) / (4 * eps)) ∂mu) ≤
        ∫ y, 8 * (∑' k : ℤ, kernelCellTerm x eps k y) ∂mu := by
      apply integral_mono (integrable_kernelAverage mu
          (mul_ne_zero (by norm_num) heps.ne') x)
        ((integrable_tsum_kernelCellTerm mu x eps).const_mul 8)
      intro y
      exact smoothingKernel_four_scale_le_tsum heps
    _ = 8 * ∫ y, (∑' k : ℤ, kernelCellTerm x eps k y) ∂mu := by
      rw [integral_const_mul]
    _ = 8 * ∑' k : ℤ, ∫ y, kernelCellTerm x eps k y ∂mu := by
      rw [integral_tsum_of_summable_integral_norm htermInt hnormSum]
    _ = 8 * ∑' k : ℤ,
        mu.real (kernelCell x eps k) * kernelCellWeight k := by
      congr 1
      apply tsum_congr
      intro k
      rw [integral_kernelCellTerm]

lemma measureReal_kernelCell_le_mul_smallBall
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps)
    (hratio : SmallBallRatioOn nu x eps R K) {N : ℕ}
    (hNle : (N : ℝ) ≤ R / 4) (hR : 4 ≤ R) {k : ℤ}
    (hk : k.natAbs < N) :
    nu.real (kernelCell x eps k) ≤ K * smallBall nu eps x := by
  let u := x + ((2 * (k : ℝ) + 1) * eps)
  calc
    nu.real (kernelCell x eps k) ≤ smallBall nu eps u := by
      exact measureReal_mono (kernelCell_subset_smallBall x heps k)
    _ ≤ K * smallBall nu eps x := by
      exact hratio u (kernelCell_ball_subset_ratioWindow heps hNle hR hk)

lemma summable_kernelCellWeight_tail (N : ℕ) :
    Summable (fun k : ℤ ↦
      if N ≤ k.natAbs then kernelCellWeight k else 0) := by
  exact summable_kernelCellWeight.of_norm_bounded (fun k ↦ by
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (kernelCellWeight_nonneg k)]
    · simp [kernelCellWeight_nonneg])

lemma weightedCells_le_near_add_tail
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 0 ≤ K)
    (hratio : SmallBallRatioOn nu x eps R K) {N : ℕ} (hN : 1 ≤ N)
    (hNle : (N : ℝ) ≤ R / 4) (hR : 4 ≤ R) :
    (∑' k : ℤ, nu.real (kernelCell x eps k) * kernelCellWeight k) ≤
      K * smallBall nu eps x * (∑' k : ℤ, kernelCellWeight k) +
        concentration nu eps * (64 / N) := by
  let tail : ℤ → ℝ := fun k ↦
    if N ≤ k.natAbs then kernelCellWeight k else 0
  have hmassSummable : Summable (fun k : ℤ ↦
      nu.real (kernelCell x eps k) * kernelCellWeight k) := by
    refine summable_kernelCellWeight.of_norm_bounded (fun k ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg measureReal_nonneg
      (kernelCellWeight_nonneg k))]
    have hprob : nu.real (kernelCell x eps k) ≤ 1 := by
      calc
        nu.real (kernelCell x eps k) ≤ nu.real univ :=
          measureReal_mono (subset_univ _)
        _ = 1 := by simp
    nlinarith [kernelCellWeight_nonneg k]
  have htailSummable : Summable tail := by
    simpa only [tail] using summable_kernelCellWeight_tail N
  have hrhsSummable : Summable (fun k : ℤ ↦
      K * smallBall nu eps x * kernelCellWeight k +
        concentration nu eps * tail k) :=
    (summable_kernelCellWeight.mul_left
      (K * smallBall nu eps x)).add
      (htailSummable.mul_left (concentration nu eps))
  have hterm : ∀ k : ℤ,
      nu.real (kernelCell x eps k) * kernelCellWeight k ≤
        K * smallBall nu eps x * kernelCellWeight k +
          concentration nu eps * tail k := by
    intro k
    by_cases hk : k.natAbs < N
    · have hmass := measureReal_kernelCell_le_mul_smallBall
        nu heps hratio hNle hR hk
      have htailZero : tail k = 0 := by
        simp [tail, Nat.not_le.2 hk]
      rw [htailZero, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right hmass (kernelCellWeight_nonneg k)
    · have hk' : N ≤ k.natAbs := Nat.le_of_not_gt hk
      have hmass := measureReal_kernelCell_le_concentration nu x heps k
      have htailEq : tail k = kernelCellWeight k := by simp [tail, hk']
      rw [htailEq]
      have hnear0 : 0 ≤ K * smallBall nu eps x * kernelCellWeight k :=
        mul_nonneg (mul_nonneg hK (smallBall_nonneg nu eps x))
          (kernelCellWeight_nonneg k)
      have hfar := mul_le_mul_of_nonneg_right hmass (kernelCellWeight_nonneg k)
      linarith
  calc
    (∑' k : ℤ, nu.real (kernelCell x eps k) * kernelCellWeight k) ≤
        ∑' k : ℤ, (K * smallBall nu eps x * kernelCellWeight k +
          concentration nu eps * tail k) :=
      Summable.tsum_le_tsum hterm hmassSummable hrhsSummable
    _ = K * smallBall nu eps x * (∑' k : ℤ, kernelCellWeight k) +
        concentration nu eps * (∑' k : ℤ, tail k) := by
      rw [Summable.tsum_add
        (summable_kernelCellWeight.mul_left (K * smallBall nu eps x))
        (htailSummable.mul_left (concentration nu eps))]
      rw [tsum_mul_left, tsum_mul_left]
    _ ≤ K * smallBall nu eps x * (∑' k : ℤ, kernelCellWeight k) +
        concentration nu eps * (64 / N) := by
      gcongr
      · exact concentration_nonneg nu eps
      · simpa only [tail] using tsum_int_kernelCellWeight_tail N hN

lemma concentration_four_mul_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) :
    concentration mu (4 * eps) ≤ 4 * concentration mu eps := by
  apply csSup_le (range_nonempty _)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact smallBall_four_mul_le_concentration mu heps x

lemma kernelAverage_four_mul_le_concentration
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu (4 * eps) x ≤
      4 * concentration mu eps * (∑' k : ℤ, kernelCellWeight k) := by
  calc
    kernelAverage mu (4 * eps) x ≤
        concentration mu (4 * eps) *
          (∑' k : ℤ, kernelCellWeight k) :=
      kernelAverage_le_cellMass_mul_concentration mu
        (mul_pos (by norm_num) heps) x
    _ ≤ 4 * concentration mu eps *
        (∑' k : ℤ, kernelCellWeight k) := by
      gcongr
      · exact tsum_nonneg fun k ↦ kernelCellWeight_nonneg k
      · exact concentration_four_mul_le mu heps

lemma kernelAverage_four_mul_le_ratio_tail
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 0 ≤ K)
    (hR : 8 ≤ R) (hratio : SmallBallRatioOn nu x eps R K) :
    kernelAverage nu (4 * eps) x ≤
      8 * K * smallBall nu eps x *
          (∑' k : ℤ, kernelCellWeight k) +
        (4096 / R) * concentration nu eps := by
  let N := ⌊R / 4⌋₊
  have hRdiv : (2 : ℝ) ≤ R / 4 := by linarith
  have hNtwo : 2 ≤ N := by
    exact Nat.le_floor hRdiv
  have hNone : 1 ≤ N := hNtwo.trans' (by norm_num)
  have hNle : (N : ℝ) ≤ R / 4 := by
    exact Nat.floor_le (by linarith)
  have hRlt : R / 4 < (N : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (R / 4)
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
  have hRle : R ≤ 8 * (N : ℝ) := by
    nlinarith
  have htail : (64 : ℝ) / N ≤ 512 / R := by
    apply (div_le_div_iff₀
      (show (0 : ℝ) < N by linarith)
      (show 0 < R by linarith)).2
    nlinarith
  have hweighted := weightedCells_le_near_add_tail
    nu heps hK hratio hNone hNle (by linarith : 4 ≤ R)
  calc
    kernelAverage nu (4 * eps) x ≤
        8 * ∑' k : ℤ,
          nu.real (kernelCell x eps k) * kernelCellWeight k :=
      kernelAverage_four_mul_le_weightedCells nu heps x
    _ ≤ 8 * (K * smallBall nu eps x *
          (∑' k : ℤ, kernelCellWeight k) +
        concentration nu eps * (64 / N)) := by
      gcongr
    _ ≤ 8 * (K * smallBall nu eps x *
          (∑' k : ℤ, kernelCellWeight k) +
        concentration nu eps * (512 / R)) := by
      gcongr
      · exact concentration_nonneg nu eps
    _ = 8 * K * smallBall nu eps x *
          (∑' k : ℤ, kernelCellWeight k) +
        (4096 / R) * concentration nu eps := by ring

lemma kernelCellWeightSum_le_eighty :
    (∑' k : ℤ, kernelCellWeight k) ≤ 80 := by
  have htail := tsum_int_kernelCellWeight_tail 1 (by norm_num)
  calc
    (∑' k : ℤ, kernelCellWeight k) = kernelCellWeight 0 +
        ∑' k : ℤ, if k = 0 then 0 else kernelCellWeight k :=
      summable_kernelCellWeight.tsum_eq_add_tsum_ite 0
    _ = 16 + ∑' k : ℤ,
        if 1 ≤ k.natAbs then kernelCellWeight k else 0 := by
      congr 1
      · norm_num [kernelCellWeight]
      · apply tsum_congr
        intro k
        by_cases hk : k = 0
        · subst k
          simp
        · have hkabs : 1 ≤ k.natAbs := by
            exact Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hk)
          simp [hk, hkabs]
    _ ≤ 16 + 64 / (1 : ℝ) := by
      gcongr
      simpa using htail
    _ = 80 := by norm_num

lemma fourierError_comm
    (mu nu : Measure ℝ) (eps : ℝ) :
    fourierError mu nu eps = fourierError nu mu eps := by
  rw [fourierError, fourierError]
  apply intervalIntegral.integral_congr
  intro t _
  exact norm_sub_rev _ _

lemma fourierError_four_mul_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) :
    fourierError mu nu (4 * eps) ≤ fourierError mu nu eps := by
  rw [fourierError, fourierError]
  have hcut : 2 / (4 * eps) ≤ 2 / eps := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) heps) heps).2
    nlinarith
  apply intervalIntegral.integral_mono_interval
  · exact neg_le_neg hcut
  · have hpos : 0 < 2 / (4 * eps) := by positivity
    linarith
  · exact hcut
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _
  · exact (continuous_norm.comp
      (continuous_charFun.sub continuous_charFun)).intervalIntegrable _ _

lemma one_half_le_reverseEsseenBase
    {z : ℝ} (hz : |z| ≤ 1) :
    (1 / 2 : ℝ) ≤ reverseEsseenBase z := by
  have hz4 : |z / 4| ≤ 1 / 4 := by
    rw [abs_div]
    norm_num
    linarith
  have hk := three_le_smoothingKernel_of_abs_le_quarter hz4
  rw [reverseEsseenBase]
  nlinarith [sq_nonneg (smoothingKernel (z / 4))]

lemma one_half_mul_smallBall_le_reverseEsseenBaseAverage
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    (1 / 2 : ℝ) * smallBall mu eps x ≤
      reverseEsseenBaseAverage mu eps x := by
  rw [smallBall, reverseEsseenBaseAverage,
    ← integral_indicator_one measurableSet_Icc,
    ← integral_const_mul]
  apply integral_mono
  · exact (Integrable.indicator (integrable_const (1 : ℝ))
      measurableSet_Icc).const_mul _
  · exact integrable_reverseEsseenBaseAverage mu eps x
  · intro y
    change (1 / 2 : ℝ) * (Icc (x - eps) (x + eps)).indicator 1 y ≤
      reverseEsseenBase ((y - x) / eps)
    by_cases hy : y ∈ Icc (x - eps) (x + eps)
    · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
      apply one_half_le_reverseEsseenBase
      rw [abs_div, abs_of_pos heps]
      apply (div_le_one heps).2
      exact (abs_le).2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rw [Set.indicator_of_notMem hy, mul_zero]
      exact reverseEsseenBase_nonneg _

lemma kernelAverage_four_mul_compare
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    kernelAverage mu (4 * eps) x ≤ kernelAverage nu (4 * eps) x +
      8 * eps * fourierError mu nu eps := by
  calc
    kernelAverage mu (4 * eps) x ≤ kernelAverage nu (4 * eps) x +
        2 * (4 * eps) * fourierError mu nu (4 * eps) :=
      kernelAverage_le_kernelAverage_add_fourierError mu nu
        (mul_pos (by norm_num) heps) x
    _ ≤ kernelAverage nu (4 * eps) x +
        2 * (4 * eps) * fourierError mu nu eps := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (fourierError_four_mul_le mu nu heps) (by positivity))
    _ = kernelAverage nu (4 * eps) x +
        8 * eps * fourierError mu nu eps := by ring

lemma kernelCorrection_le
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 1 ≤ K) (hR : 4 ≤ R)
    (hratio : SmallBallRatioOn nu x eps R K) :
    (4 / (10000 * K) ^ 2) * kernelAverage mu (4 * eps) x ≤
      (3 / 8 : ℝ) * smallBall nu eps x + concentration nu eps / R +
        eps * fourierError mu nu eps := by
  let q : ℝ := 4 / (10000 * K) ^ 2
  let W : ℝ := ∑' k : ℤ, kernelCellWeight k
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hBpos : 0 < 10000 * K := mul_pos (by norm_num) hKpos
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hBsq : (100000000 : ℝ) ≤ (10000 * K) ^ 2 := by
    nlinarith
  have hq : q ≤ (1 / 25000000 : ℝ) := by
    dsimp only [q]
    apply (div_le_iff₀ (sq_pos_of_pos hBpos)).2
    nlinarith
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hqK : q * K ≤ (1 / 25000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hKsq hq0
    have heq : q * K ^ 2 = (1 / 25000000 : ℝ) := by
      dsimp only [q]
      field_simp [hKpos.ne']
      ring
    rw [heq] at h
    exact h
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact tsum_nonneg kernelCellWeight_nonneg
  have hW : W ≤ 80 := by
    exact kernelCellWeightSum_le_eighty
  have hnearCoef : q * 8 * K * W ≤ (3 / 8 : ℝ) := by
    calc
      q * 8 * K * W = (q * K) * (8 * W) := by ring
      _ ≤ (1 / 25000000 : ℝ) * (8 * 80) := by
        exact mul_le_mul hqK (by nlinarith)
          (mul_nonneg (by norm_num) hW0) (by positivity)
      _ ≤ (3 / 8 : ℝ) := by norm_num
  have htailCoef : q * 4096 ≤ 1 := by
    calc
      q * 4096 ≤ (1 / 25000000 : ℝ) * 4096 :=
        mul_le_mul_of_nonneg_right hq (by norm_num)
      _ ≤ 1 := by norm_num
  have herrCoef : q * 8 ≤ 1 := by
    calc
      q * 8 ≤ (1 / 25000000 : ℝ) * 8 :=
        mul_le_mul_of_nonneg_right hq (by norm_num)
      _ ≤ 1 := by norm_num
  have hE0 : 0 ≤ fourierError mu nu eps :=
    fourierError_nonneg mu nu heps
  have hcompare := kernelAverage_four_mul_compare mu nu heps x
  change q * kernelAverage mu (4 * eps) x ≤ _
  by_cases hR8 : 8 ≤ R
  · have hnu := kernelAverage_four_mul_le_ratio_tail
      nu heps hKpos.le hR8 hratio
    have hmu : kernelAverage mu (4 * eps) x ≤
        (8 * K * smallBall nu eps x * W +
          (4096 / R) * concentration nu eps) +
            8 * eps * fourierError mu nu eps := by
      exact hcompare.trans (add_le_add hnu le_rfl)
    calc
      q * kernelAverage mu (4 * eps) x ≤
          q * ((8 * K * smallBall nu eps x * W +
            (4096 / R) * concentration nu eps) +
              8 * eps * fourierError mu nu eps) :=
        mul_le_mul_of_nonneg_left hmu hq0
      _ = (q * 8 * K * W) * smallBall nu eps x +
          (q * 4096) * (concentration nu eps / R) +
          (q * 8) * (eps * fourierError mu nu eps) := by ring
      _ ≤ (3 / 8 : ℝ) * smallBall nu eps x +
          1 * (concentration nu eps / R) +
          1 * (eps * fourierError mu nu eps) := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hnearCoef
              (smallBall_nonneg nu eps x))
            (mul_le_mul_of_nonneg_right htailCoef
              (div_nonneg (concentration_nonneg nu eps) hRpos.le)))
          (mul_le_mul_of_nonneg_right herrCoef
            (mul_nonneg heps.le hE0))
      _ = (3 / 8 : ℝ) * smallBall nu eps x +
          concentration nu eps / R +
          eps * fourierError mu nu eps := by ring
  · have hRlt : R < 8 := lt_of_not_ge hR8
    have hnu := kernelAverage_four_mul_le_concentration nu heps x
    have hmu : kernelAverage mu (4 * eps) x ≤
        4 * concentration nu eps * W +
          8 * eps * fourierError mu nu eps :=
      hcompare.trans (add_le_add hnu le_rfl)
    have h4W : 4 * W ≤ 4 * 80 :=
      mul_le_mul_of_nonneg_left hW (by norm_num)
    have h4WR : 4 * W * R ≤ 4 * 80 * 8 := by
      exact mul_le_mul h4W hRlt.le hRpos.le (by positivity)
    have hsmallCoef : q * (4 * W * R) ≤ 1 := by
      calc
        q * (4 * W * R) ≤ (1 / 25000000 : ℝ) * (4 * 80 * 8) :=
          mul_le_mul hq h4WR
            (mul_nonneg (mul_nonneg (by norm_num) hW0) hRpos.le)
            (by positivity)
        _ ≤ 1 := by norm_num
    have hconc : q * (4 * concentration nu eps * W) ≤
        concentration nu eps / R := by
      apply (le_div_iff₀ hRpos).2
      calc
        q * (4 * concentration nu eps * W) * R =
            (q * (4 * W * R)) * concentration nu eps := by ring
        _ ≤ 1 * concentration nu eps :=
          mul_le_mul_of_nonneg_right hsmallCoef
            (concentration_nonneg nu eps)
        _ = concentration nu eps := one_mul _
    calc
      q * kernelAverage mu (4 * eps) x ≤
          q * (4 * concentration nu eps * W +
            8 * eps * fourierError mu nu eps) :=
        mul_le_mul_of_nonneg_left hmu hq0
      _ = q * (4 * concentration nu eps * W) +
          (q * 8) * (eps * fourierError mu nu eps) := by ring
      _ ≤ concentration nu eps / R +
          eps * fourierError mu nu eps := by
        exact add_le_add hconc (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right herrCoef
            (mul_nonneg heps.le hE0))
      _ ≤ (3 / 8 : ℝ) * smallBall nu eps x +
          concentration nu eps / R + eps * fourierError mu nu eps := by
        nlinarith [smallBall_nonneg nu eps x]

lemma relative_esseen_6_3_five
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 1 ≤ K) (hR : 4 ≤ R)
    (hratio : SmallBallRatioOn nu x eps R K) :
    (1 / 8 : ℝ) * smallBall nu eps x -
        5 * (concentration nu eps / R + eps * fourierError mu nu eps) ≤
      smallBall mu ((10000 * K) * eps) x := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hBpos : 0 < 10000 * K := mul_pos (by norm_num) hKpos
  have hcentral :=
    one_half_mul_smallBall_le_reverseEsseenBaseAverage nu heps x
  have hfour := reverseEsseenBaseAverage_le_add_fourierError
    nu mu heps x
  rw [fourierError_comm nu mu eps] at hfour
  have hspatial := reverseEsseenBaseAverage_sub_kernelAverage_le_smallBall
    mu heps hBpos x
  have hcorr := kernelCorrection_le mu nu heps hK hR hratio
  have hbaseMu : reverseEsseenBaseAverage mu eps x ≤
      smallBall mu ((10000 * K) * eps) x +
        (4 / (10000 * K) ^ 2) * kernelAverage mu (4 * eps) x := by
    linarith
  have hconc0 : 0 ≤ concentration nu eps / R :=
    div_nonneg (concentration_nonneg nu eps)
      (lt_of_lt_of_le (by norm_num) hR).le
  have herr0 : 0 ≤ eps * fourierError mu nu eps :=
    mul_nonneg heps.le (fourierError_nonneg mu nu heps)
  have hnoise0 : 0 ≤ concentration nu eps / R +
      eps * fourierError mu nu eps := add_nonneg hconc0 herr0
  have hchain : (1 / 2 : ℝ) * smallBall nu eps x ≤
      smallBall mu ((10000 * K) * eps) x +
        (3 / 8 : ℝ) * smallBall nu eps x +
          concentration nu eps / R + eps * fourierError mu nu eps +
            4 * eps * fourierError mu nu eps := by
    calc
    (1 / 2 : ℝ) * smallBall nu eps x ≤
        reverseEsseenBaseAverage nu eps x := hcentral
    _ ≤ reverseEsseenBaseAverage mu eps x +
        4 * eps * fourierError mu nu eps := hfour
    _ ≤ smallBall mu ((10000 * K) * eps) x +
        (4 / (10000 * K) ^ 2) * kernelAverage mu (4 * eps) x +
          4 * eps * fourierError mu nu eps := by
      linarith
    _ ≤ smallBall mu ((10000 * K) * eps) x +
        (3 / 8 : ℝ) * smallBall nu eps x +
          concentration nu eps / R + eps * fourierError mu nu eps +
            4 * eps * fourierError mu nu eps := by
      linarith
  linarith [hchain, hconc0, herr0]

theorem relative_esseen_6_3_of_smallBallRatio
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 1 ≤ K) (hR : 4 ≤ R)
    (hratio : SmallBallRatioOn nu x eps R K) :
    (1 / 8 : ℝ) * smallBall nu eps x -
        relativeEsseenConstant *
          (concentration nu eps / R + eps * fourierError mu nu eps) ≤
      smallBall mu ((10000 * K) * eps) x := by
  have hfive := relative_esseen_6_3_five
    mu nu heps hK hR hratio
  have hC : (5 : ℝ) ≤ relativeEsseenConstant := by
    rw [relativeEsseenConstant]
    have hsum : 0 ≤ ∑' k : ℤ, kernelCellWeight k :=
      tsum_nonneg kernelCellWeight_nonneg
    have hexp : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
    nlinarith [mul_nonneg hexp hsum]
  have hnoise0 : 0 ≤ concentration nu eps / R +
      eps * fourierError mu nu eps := by
    exact add_nonneg
      (div_nonneg (concentration_nonneg nu eps)
        (lt_of_lt_of_le (by norm_num) hR).le)
      (mul_nonneg heps.le (fourierError_nonneg mu nu heps))
  linarith [mul_le_mul_of_nonneg_right hC hnoise0]

/-- Density-ratio formulation of KSSS Lemma 6.3.  This is retained as a
convenient corollary of the more general interval-ratio theorem above. -/
theorem relative_esseen_6_3
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {f : ℝ → ℝ} (hdens : HasContinuousDensity nu f)
    {x eps R K : ℝ} (heps : 0 < eps) (hK : 1 ≤ K) (hR : 4 ≤ R)
    (hratio : DensityRatioOn f x eps R K) :
    (1 / 8 : ℝ) * smallBall nu eps x -
        relativeEsseenConstant *
          (concentration nu eps / R + eps * fourierError mu nu eps) ≤
      smallBall mu ((10000 * K) * eps) x := by
  apply relative_esseen_6_3_of_smallBallRatio mu nu heps hK hR
  exact smallBallRatioOn_of_densityRatio nu hdens heps (by linarith) hratio


end

end Esseen
end Erdos88
