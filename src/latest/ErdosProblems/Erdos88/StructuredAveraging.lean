/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos88.StructuredTypical
import ErdosProblems.Erdos88.Esseen

/-!
# Weighted smoothing estimates for the structured branch

This file develops the Walsh--Fourier estimate used in KSSS Claim 12.3.
The first step keeps the contribution of the coordinates of a Walsh
monomial instead of discarding their sine factors.  This is the source of
the power of the Fourier frequency in the weighted smoothing estimate.
-/

open scoped BigOperators symmDiff

namespace Erdos88.LinearLCDCancellation

/-- The elementary Gaussian-power envelope needed to integrate the
frequency estimate. -/
lemma integrable_abs_pow_mul_exp_neg_mul_sq (m : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun x : ℝ ↦ |x| ^ m * Real.exp (-b * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (s := (m : ℝ)) hb (by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have hn := h.norm
  convert hn using 1
  funext x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    Real.rpow_natCast, abs_pow]

/-- Exact whole-line integral of the Gaussian-power envelope. -/
lemma integral_abs_pow_mul_exp_neg_mul_sq (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| ^ m * Real.exp (-b * x ^ 2) =
      2 * (b ^ (-((m : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
        Real.Gamma (((m : ℝ) + 1) / 2)) := by
  calc
    ∫ x : ℝ, |x| ^ m * Real.exp (-b * x ^ 2) =
        ∫ x : ℝ,
          |x| ^ (m : ℝ) * Real.exp (-b * |x| ^ 2) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_natCast, sq_abs]
    _ = 2 * ∫ x : ℝ in Set.Ioi 0,
        x ^ (m : ℝ) * Real.exp (-b * x ^ 2) := by
      simpa only [] using integral_comp_abs
        (f := fun x : ℝ ↦ x ^ (m : ℝ) * Real.exp (-b * x ^ 2))
    _ = 2 * (b ^ (-((m : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
        Real.Gamma (((m : ℝ) + 1) / 2)) := by
      congr 1
      have hgamma := _root_.integral_rpow_mul_exp_neg_mul_rpow
        (p := (2 : ℝ)) (q := (m : ℝ)) (b := b)
        (by norm_num) (by
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith) hb
      calc
        ∫ x : ℝ in Set.Ioi 0,
            x ^ (m : ℝ) * Real.exp (-b * x ^ (2 : ℕ)) =
            ∫ x : ℝ in Set.Ioi 0,
              x ^ (m : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change x ^ (m : ℝ) * Real.exp (-b * x ^ (2 : ℕ)) =
            x ^ (m : ℝ) * Real.exp (-b * x ^ (2 : ℝ))
          have hp2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) :=
            Real.rpow_natCast x 2
          rw [hp2]
        _ = _ := hgamma

/-- The explicit one-dimensional constant produced by a Walsh support of
cardinality `m` when the squared coefficient mass is `M`. -/
noncomputable def smoothingWalshGammaFactor (M : ℝ) (m : ℕ) : ℝ :=
  4 * (((M - m) / Real.pi ^ 2) ^ (-((m : ℝ) + 1) / 2) *
    (1 / 2 : ℝ) * Real.Gamma (((m : ℝ) + 1) / 2))

lemma smoothingWalshGammaFactor_nonneg {M : ℝ} {m : ℕ}
    (hm : (m : ℝ) < M) : 0 ≤ smoothingWalshGammaFactor M m := by
  unfold smoothingWalshGammaFactor
  have hbase : 0 < (M - m) / Real.pi ^ 2 :=
    div_pos (sub_pos.mpr hm) (sq_pos_of_pos Real.pi_pos)
  have hgamma : 0 < Real.Gamma (((m : ℝ) + 1) / 2) := by
    apply Real.Gamma_pos_of_pos
    positivity
  positivity

/-- In the central Fourier window, a Walsh monomial contributes one sine
factor on each of its coordinates, while every other coordinate retains
the usual Gaussian cosine decay.  This is the pointwise product estimate
underlying KSSS Claim 12.3. -/
theorem norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (t : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4) (ht : |t| ≤ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      Complex.exp (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
        Complex.I) * rademacherWalshMonomial S xi)‖ ≤
      ∏ i, if i ∈ S then |t| * |beta i|
        else Real.exp (-((-t * beta i) / Real.pi) ^ 2) := by
  rw [finExpectation_exp_rademacher_linear_mul_walshMonomial, norm_prod]
  apply Finset.prod_le_prod
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, if_pos hiS, norm_mul, Complex.norm_I,
        Complex.norm_real, one_mul, Real.norm_eq_abs]
      calc
        |Real.sin (-t * beta i)| ≤ |-t * beta i| := Real.abs_sin_le_abs
        _ = |t| * |beta i| := by rw [abs_mul, abs_neg]
    · rw [if_neg hiS, if_neg hiS, Complex.norm_real, Real.norm_eq_abs]
      apply Fourier.abs_cos_le_exp_neg_sq_div_pi_sq
      calc
        |-t * beta i| = |t| * |beta i| := by rw [abs_mul, abs_neg]
        _ ≤ 2 * (Real.pi / 4) := mul_le_mul ht (hbeta i) (abs_nonneg _) (by norm_num)
        _ = Real.pi / 2 := by ring

/-- Split form of the preceding estimate.  The selected coordinates retain
their small sine factors and the complementary coordinates combine into a
single Gaussian exponential. -/
theorem norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le_split
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (t : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4) (ht : |t| ≤ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      Complex.exp (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
        Complex.I) * rademacherWalshMonomial S xi)‖ ≤
      (∏ i ∈ S, |t| * |beta i|) *
        Real.exp (-∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
          ((-t * beta i) / Real.pi) ^ 2) := by
  refine (norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le
    beta S t hbeta ht).trans_eq ?_
  rw [Finset.prod_ite]
  have hselected : Finset.univ.filter (fun i ↦ i ∈ S) = S := by
    ext i
    simp
  rw [hselected, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]

/-- Source-shaped central-window estimate: after deleting the coordinates of
the Walsh monomial, at most one unit of squared coefficient mass is lost per
coordinate.  The retained sine factors give the power `|t| ^ S.card`. -/
theorem norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le_sqMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (t : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4) (ht : |t| ≤ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      Complex.exp (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
        Complex.I) * rademacherWalshMonomial S xi)‖ ≤
      |t| ^ S.card * Real.exp (-(t ^ 2 / Real.pi ^ 2) *
        ((∑ i, beta i ^ 2) - S.card)) := by
  refine (norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le_split
    beta S t hbeta ht).trans ?_
  have hbetaOne (i : I) : |beta i| ≤ 1 := by
    exact (hbeta i).trans (by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      simpa using Real.pi_le_four)
  have hselected : (∏ i ∈ S, |t| * |beta i|) ≤ |t| ^ S.card := by
    calc
      (∏ i ∈ S, |t| * |beta i|) ≤ ∏ _i ∈ S, |t| * 1 := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          exact mul_le_mul_of_nonneg_left (hbetaOne i) (abs_nonneg t)
      _ = |t| ^ S.card := by simp
  have hinside : (∑ i ∈ S, beta i ^ 2) ≤ (S.card : ℝ) := by
    calc
      (∑ i ∈ S, beta i ^ 2) ≤ ∑ _i ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hsquare : |beta i| ^ 2 ≤ (1 : ℝ) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg (beta i)) (by norm_num)).2 (hbetaOne i)
        nlinarith [sq_abs (beta i)]
      _ = (S.card : ℝ) := by simp
  have hfilter : Finset.univ.filter (fun i ↦ i ∉ S) = Finset.univ \ S := by
    ext i
    simp
  have hsplit :
      (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S), beta i ^ 2) +
          ∑ i ∈ S, beta i ^ 2 = ∑ i, beta i ^ 2 := by
    rw [hfilter]
    exact Finset.sum_sdiff (Finset.subset_univ S)
  have hscale (i : I) :
      ((-t * beta i) / Real.pi) ^ 2 =
        (t ^ 2 / Real.pi ^ 2) * beta i ^ 2 := by
    field_simp [Real.pi_ne_zero]
  have houter :
      (t ^ 2 / Real.pi ^ 2) * ((∑ i, beta i ^ 2) - S.card) ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
          ((-t * beta i) / Real.pi) ^ 2 := by
    simp_rw [hscale, ← Finset.mul_sum]
    have hfactor : 0 ≤ t ^ 2 / Real.pi ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hfactor
    linarith
  apply mul_le_mul hselected
  · apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg houter
  · exact Real.exp_nonneg _
  · exact pow_nonneg (abs_nonneg _) _

/-- Exact finite-expectation/Fourier identity for a smoothed Walsh
monomial.  The translation parameter contributes only the unit-modulus
phase in front of the Rademacher characteristic function. -/
lemma finExpectation_smoothingKernel_mul_walshMonomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (target : ℝ) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          rademacherWalshMonomial S xi) =
      ∫ t in (-2 : ℝ)..2,
        (Esseen.frequencyKernel t : ℂ) *
          Complex.exp ((t * target : ℝ) * Complex.I) *
            Fourier.finExpectation (I → Bool) (fun xi ↦
              Complex.exp
                (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
                  Complex.I) * rademacherWalshMonomial S xi) := by
  classical
  let X : (I → Bool) → ℝ := fun xi ↦
    (∑ i, beta i * Fourier.rademacherSign (xi i)) - target
  let H : ℝ → (I → Bool) → ℂ := fun t xi ↦
    (Esseen.frequencyKernel t : ℂ) *
      Complex.exp ((t * target : ℝ) * Complex.I) *
        (Complex.exp
          (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
            Complex.I) * rademacherWalshMonomial S xi)
  have hHInt (xi : I → Bool) :
      IntervalIntegrable (fun t ↦ H t xi) MeasureTheory.volume (-2) 2 := by
    exact (((Complex.continuous_ofReal.comp Esseen.continuous_frequencyKernel).mul
      (Complex.continuous_exp.comp (by fun_prop))).mul
        ((Complex.continuous_exp.comp (by fun_prop)).mul continuous_const)).intervalIntegrable _ _
  have hpoint (xi : I → Bool) :
      (Esseen.smoothingKernel (X xi) : ℂ) * rademacherWalshMonomial S xi =
        ∫ t in (-2 : ℝ)..2, H t xi := by
    rw [Esseen.smoothingKernel_fourier, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [H, X]
    have hsum :
        (∑ i, (-t * beta i) * Fourier.rademacherSign (xi i)) =
          -t * ∑ i, beta i * Fourier.rademacherSign (xi i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hphase :
        Complex.exp
          (-((t : ℂ) *
              (((∑ i, beta i * Fourier.rademacherSign (xi i)) - target : ℝ) : ℂ)) *
            Complex.I) =
          Complex.exp ((t * target : ℝ) * Complex.I) *
            Complex.exp
              (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
                Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hsum]
      push_cast
      ring
    change (Esseen.frequencyKernel t : ℂ) *
        Complex.exp
          (-((t : ℂ) *
              (((∑ i, beta i * Fourier.rademacherSign (xi i)) - target : ℝ) : ℂ)) *
            Complex.I) * rademacherWalshMonomial S xi = _
    rw [hphase]
    ring
  rw [Fourier.finExpectation]
  change (∑ xi, (Esseen.smoothingKernel (X xi) : ℂ) *
      rademacherWalshMonomial S xi) / _ = _
  simp_rw [hpoint]
  have hsumInt :
      (∑ xi : I → Bool, ∫ t in (-2 : ℝ)..2, H t xi) =
        ∫ t in (-2 : ℝ)..2, ∑ xi : I → Bool, H t xi := by
    symm
    simpa using intervalIntegral.integral_finsetSum
      (s := (Finset.univ : Finset (I → Bool)))
      (fun xi _ ↦ hHInt xi)
  rw [hsumInt, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [H]
  rw [Fourier.finExpectation]
  rw [← Finset.mul_sum]
  ring

/-- Integral form of the Walsh smoothing estimate.  This is the analytic
core of Claim 12.3 before evaluating the one-dimensional Gaussian
integral.  The bound is uniform in the translate `target`. -/
theorem norm_finExpectation_smoothingKernel_mul_walshMonomial_le_integral
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          rademacherWalshMonomial S xi)‖ ≤
      ∫ t in (-2 : ℝ)..2,
        Esseen.frequencyKernel t * |t| ^ S.card *
          Real.exp (-(t ^ 2 / Real.pi ^ 2) *
            ((∑ i, beta i ^ 2) - S.card)) := by
  rw [finExpectation_smoothingKernel_mul_walshMonomial beta S target]
  let g : ℝ → ℝ := fun t ↦
    Esseen.frequencyKernel t * |t| ^ S.card *
      Real.exp (-(t ^ 2 / Real.pi ^ 2) *
        ((∑ i, beta i ^ 2) - S.card))
  have hg : IntervalIntegrable g MeasureTheory.volume (-2) 2 := by
    exact ((Esseen.continuous_frequencyKernel.mul (continuous_abs.pow S.card)).mul
      (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · filter_upwards with t ht
    have htAbs : |t| ≤ 2 := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
    let E : ℂ := Fourier.finExpectation (I → Bool) (fun xi ↦
      Complex.exp
        (((∑ i, (-t * beta i) * Fourier.rademacherSign (xi i) : ℝ) : ℂ) *
          Complex.I) * rademacherWalshMonomial S xi)
    have hE : ‖E‖ ≤ |t| ^ S.card *
        Real.exp (-(t ^ 2 / Real.pi ^ 2) *
          ((∑ i, beta i ^ 2) - S.card)) :=
      norm_finExpectation_exp_small_rademacher_linear_mul_walshMonomial_le_sqMass
        beta S t hbeta htAbs
    change ‖(Esseen.frequencyKernel t : ℂ) *
        Complex.exp ((t * target : ℝ) * Complex.I) * E‖ ≤ g t
    have hphase : ‖Complex.exp ((t * target : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Esseen.frequencyKernel_nonneg t), hphase, mul_one]
    simpa only [g, mul_assoc] using
      mul_le_mul_of_nonneg_left hE (Esseen.frequencyKernel_nonneg t)
  · exact hg

/-- Evaluated Claim 12.3 monomial bound, with an explicit Gamma-factor
constant.  It has the required inverse power `(|beta|²-|S|)^(-(l+1)/2)`
and remains uniform in the translate. -/
theorem norm_finExpectation_smoothingKernel_mul_walshMonomial_le_gamma
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (S : Finset I) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hmass : (S.card : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          rademacherWalshMonomial S xi)‖ ≤
      4 * ((((∑ i, beta i ^ 2) - S.card) / Real.pi ^ 2) ^
          (-((S.card : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
            Real.Gamma (((S.card : ℝ) + 1) / 2)) := by
  let B : ℝ := (∑ i, beta i ^ 2) - S.card
  let b : ℝ := B / Real.pi ^ 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  have hb : 0 < b := div_pos hB (sq_pos_of_pos Real.pi_pos)
  let e : ℝ → ℝ := fun t ↦ |t| ^ S.card * Real.exp (-b * t ^ 2)
  have heInt : MeasureTheory.Integrable e := by
    simpa only [e] using
      integrable_abs_pow_mul_exp_neg_mul_sq S.card hb
  have hinterval :
      (∫ t in (-2 : ℝ)..2,
        Esseen.frequencyKernel t * |t| ^ S.card *
          Real.exp (-(t ^ 2 / Real.pi ^ 2) *
            ((∑ i, beta i ^ 2) - S.card))) ≤
        ∫ t : ℝ, 2 * e t := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hfInt : MeasureTheory.IntegrableOn (fun t : ℝ ↦
        Esseen.frequencyKernel t * |t| ^ S.card *
          Real.exp (-(t ^ 2 / Real.pi ^ 2) *
            ((∑ i, beta i ^ 2) - S.card))) (Set.Ioc (-2) 2) :=
      (((Esseen.continuous_frequencyKernel.mul (continuous_abs.pow S.card)).mul
        (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable (-2) 2).1
    calc
      (∫ t : ℝ in Set.Ioc (-2) 2,
        Esseen.frequencyKernel t * |t| ^ S.card *
          Real.exp (-(t ^ 2 / Real.pi ^ 2) *
            ((∑ i, beta i ^ 2) - S.card))) ≤
          ∫ t : ℝ in Set.Ioc (-2) 2, 2 * e t := by
        apply MeasureTheory.setIntegral_mono_on hfInt
          (heInt.const_mul 2).integrableOn measurableSet_Ioc
        intro t ht
        have hexp :
            -(t ^ 2 / Real.pi ^ 2) *
                ((∑ i, beta i ^ 2) - S.card) = -b * t ^ 2 := by
          dsimp only [b, B]
          ring
        rw [hexp]
        dsimp only [e]
        have hnonneg : 0 ≤ |t| ^ S.card * Real.exp (-b * t ^ 2) := by
          positivity
        calc
          Esseen.frequencyKernel t * |t| ^ S.card * Real.exp (-b * t ^ 2) =
              Esseen.frequencyKernel t *
                (|t| ^ S.card * Real.exp (-b * t ^ 2)) := by ring
          _ ≤ 2 * (|t| ^ S.card * Real.exp (-b * t ^ 2)) :=
            mul_le_mul_of_nonneg_right (Esseen.frequencyKernel_le_two t) hnonneg
      _ ≤ ∫ t : ℝ, 2 * e t := by
        apply MeasureTheory.setIntegral_le_integral (heInt.const_mul 2)
        filter_upwards with t
        dsimp only [e]
        positivity
  refine (norm_finExpectation_smoothingKernel_mul_walshMonomial_le_integral
    beta S target hbeta).trans (hinterval.trans_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ t : ℝ, e t) =
      2 * (b ^ (-((S.card : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
        Real.Gamma (((S.card : ℝ) + 1) / 2)) by
    simpa only [e] using integral_abs_pow_mul_exp_neg_mul_sq S.card hb]
  dsimp only [b, B]
  ring

/-- Finite Walsh-polynomial form of the evaluated smoothing estimate.  It
is the summation step used after expanding the first two powers of the
quadratic form in Claim 12.3. -/
theorem norm_finExpectation_smoothingKernel_mul_walshSum_le_gamma
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (beta : I → ℝ) (c : J → ℂ) (support : J → Finset I) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hmass : ∀ j, ((support j).card : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          ∑ j, c j * rademacherWalshMonomial (support j) xi)‖ ≤
      ∑ j, ‖c j‖ *
        (4 * ((((∑ i, beta i ^ 2) - (support j).card) / Real.pi ^ 2) ^
          (-(((support j).card : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
            Real.Gamma ((((support j).card : ℝ) + 1) / 2))) := by
  have hpoint : (fun xi : I → Bool ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          ∑ j, c j * rademacherWalshMonomial (support j) xi) =
      (fun xi ↦ ∑ j, c j *
        ((Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
            rademacherWalshMonomial (support j) xi)) := by
    funext xi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hpoint, finExpectation_sum]
  calc
    ‖∑ j, Fourier.finExpectation (I → Bool) (fun xi ↦ c j *
        ((Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
            rademacherWalshMonomial (support j) xi))‖ ≤
        ∑ j, ‖Fourier.finExpectation (I → Bool) (fun xi ↦ c j *
          ((Esseen.smoothingKernel
            ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
              rademacherWalshMonomial (support j) xi))‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ *
        (4 * ((((∑ i, beta i ^ 2) - (support j).card) / Real.pi ^ 2) ^
          (-(((support j).card : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
            Real.Gamma ((((support j).card : ℝ) + 1) / 2))) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Fourier.finExpectation_const_mul, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact norm_finExpectation_smoothingKernel_mul_walshMonomial_le_gamma
        beta (support j) target hbeta (hmass j)

/-- Walsh support of a quadratic Rademacher monomial.  Symmetric difference
correctly makes a diagonal term constant. -/
def rademacherPairSupport {I : Type*} [DecidableEq I]
    (q : I × I) : Finset I := ({q.1} : Finset I) ∆ {q.2}

@[simp] lemma rademacherWalshMonomial_pairSupport
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I × I) (xi : I → Bool) :
    rademacherWalshMonomial (rademacherPairSupport q) xi =
      (Fourier.rademacherSign (xi q.1) : ℂ) *
        Fourier.rademacherSign (xi q.2) := by
  simpa [rademacherPairSupport, rademacherWalshMonomial] using
    (rademacherWalshMonomial_mul ({q.1} : Finset I) {q.2} xi).symm

lemma rademacherQuadratic_eq_walshSum
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (xi : I → Bool) :
    ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j) : ℝ) : ℂ) =
      ∑ q : I × I, (A q.1 q.2 : ℂ) *
        rademacherWalshMonomial (rademacherPairSupport q) xi := by
  rw [Fintype.sum_prod_type]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [rademacherWalshMonomial_pairSupport (i, j)]
  ring

/-- Exact Walsh expansion of a power of a quadratic Rademacher form. -/
lemma rademacherQuadratic_pow_eq_walshSum
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (xi : I → Bool) (k : ℕ) :
    (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k) =
      ∑ q : Fin k → I × I,
        (∏ r, (A (q r).1 (q r).2 : ℂ)) *
          rademacherWalshMonomial
            (xorSupport rademacherPairSupport q) xi := by
  rw [rademacherQuadratic_eq_walshSum A xi]
  exact walshSum_pow
    (fun q : I × I ↦ (A q.1 q.2 : ℂ)) rademacherPairSupport xi k

lemma rademacherPairSupport_card_le_two
    {I : Type*} [DecidableEq I] (q : I × I) :
    (rademacherPairSupport q).card ≤ 2 := by
  calc
    (rademacherPairSupport q).card ≤
        (({q.1} : Finset I) ∪ {q.2}).card :=
      Finset.card_le_card (by
        unfold rademacherPairSupport
        exact Finset.symmDiff_subset_union)
    _ ≤ ({q.1} : Finset I).card + ({q.2} : Finset I).card :=
      Finset.card_union_le _ _
    _ = 2 := by simp

lemma card_rademacherPairSupport
    {I : Type*} [DecidableEq I] (q : I × I) :
    (rademacherPairSupport q).card = if q.1 = q.2 then 0 else 2 := by
  by_cases hq : q.1 = q.2
  · simp [rademacherPairSupport, hq]
  · rw [rademacherPairSupport, Finset.symmDiff_def]
    have hleft : ({q.1} : Finset I) \ {q.2} = {q.1} := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        exact ⟨hx, fun hx2 ↦ hq (hx.symm.trans hx2)⟩
    have hright : ({q.2} : Finset I) \ {q.1} = {q.2} := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        exact ⟨hx, fun hx1 ↦ hq (hx1.symm.trans hx)⟩
    rw [hleft, hright]
    simp [hq]

/-- Exact quadratic-power form of Claim 12.3, prior to the finite
support-counting estimate.  Every summand already has the correct inverse
power dictated by the cardinality of its resulting Walsh support. -/
theorem norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_pow_le_gamma
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (k : ℕ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hmass : ((2 * k : ℕ) : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k))‖ ≤
      ∑ q : Fin k → I × I,
        ‖∏ r, (A (q r).1 (q r).2 : ℂ)‖ *
          (4 * (
            (((∑ i, beta i ^ 2) -
                (xorSupport rademacherPairSupport q).card) / Real.pi ^ 2) ^
              (-(((xorSupport rademacherPairSupport q).card : ℝ) + 1) / 2) *
            (1 / 2 : ℝ) *
            Real.Gamma
              ((((xorSupport rademacherPairSupport q).card : ℝ) + 1) / 2))) := by
  have hdegree : ∀ q : I × I, (rademacherPairSupport q).card ≤ 2 :=
    rademacherPairSupport_card_le_two
  have hsupport (q : Fin k → I × I) :
      (xorSupport rademacherPairSupport q).card ≤ k * 2 :=
    xorSupport_card_le rademacherPairSupport hdegree q
  have hsupportMass (q : Fin k → I × I) :
      ((xorSupport rademacherPairSupport q).card : ℝ) <
        ∑ i, beta i ^ 2 := by
    have hcast : ((xorSupport rademacherPairSupport q).card : ℝ) ≤
        ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [Nat.mul_comm] using hsupport q)
    exact hcast.trans_lt hmass
  have hpoint : (fun xi : I → Bool ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k)) =
      (fun xi ↦
        (Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          ∑ q : Fin k → I × I,
            (∏ r, (A (q r).1 (q r).2 : ℂ)) *
              rademacherWalshMonomial
                (xorSupport rademacherPairSupport q) xi) := by
    funext xi
    rw [rademacherQuadratic_pow_eq_walshSum]
  rw [hpoint]
  simpa only using
    (norm_finExpectation_smoothingKernel_mul_walshSum_le_gamma
      beta
      (fun q : Fin k → I × I ↦ ∏ r, (A (q r).1 (q r).2 : ℂ))
      (fun q ↦ xorSupport rademacherPairSupport q) target hbeta hsupportMass)

/-- The finite type of Walsh supports that can occur in the `k`-th power
of a quadratic form. -/
abbrev QuadraticPowerWalshSupport (I : Type*) (k : ℕ) :=
  {S : Finset I // S.card ≤ 2 * k}

/-- The actual support of one ordered expansion term, bundled with its
degree bound. -/
def quadraticPowerResultSupport
    {I : Type*} [DecidableEq I] (k : ℕ) (q : Fin k → I × I) :
    QuadraticPowerWalshSupport I k :=
  ⟨xorSupport rademacherPairSupport q, by
    have h := xorSupport_card_le rademacherPairSupport
      (fun p : I × I ↦ rademacherPairSupport_card_le_two p) q
    simpa [Nat.mul_comm] using h⟩

@[simp] lemma quadraticPowerResultSupport_one_val
    {I : Type*} [DecidableEq I] (q : Fin 1 → I × I) :
    (quadraticPowerResultSupport 1 q).1 = rademacherPairSupport (q 0) := by
  simp [quadraticPowerResultSupport, xorSupport]

/-- Coefficient after collecting all ordered quadratic-power terms with
the same Walsh support. -/
noncomputable def quadraticPowerWalshCoeff
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (k : ℕ) (S : QuadraticPowerWalshSupport I k) : ℂ :=
  ∑ q : Fin k → I × I with quadraticPowerResultSupport k q = S,
    ∏ r, (A (q r).1 (q r).2 : ℂ)

/-- With entries bounded by one, a collected Walsh coefficient is bounded
by the cardinality of its ordered-expansion fiber. -/
lemma norm_quadraticPowerWalshCoeff_le_card_fiber
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (k : ℕ) (S : QuadraticPowerWalshSupport I k)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ‖quadraticPowerWalshCoeff A k S‖ ≤
      ((Finset.univ.filter (fun q : Fin k → I × I ↦
        quadraticPowerResultSupport k q = S)).card : ℝ) := by
  rw [quadraticPowerWalshCoeff]
  calc
    ‖∑ q : Fin k → I × I with quadraticPowerResultSupport k q = S,
        ∏ r, (A (q r).1 (q r).2 : ℂ)‖ ≤
        ∑ q : Fin k → I × I with quadraticPowerResultSupport k q = S,
          ‖∏ r, (A (q r).1 (q r).2 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin k → I × I with quadraticPowerResultSupport k _q = S,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_prod]
      calc
        (∏ r, ‖(A (q r).1 (q r).2 : ℂ)‖) ≤ ∏ _r, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro r hr
            exact norm_nonneg _
          · intro r hr
            simpa [Real.norm_eq_abs] using hA (q r).1 (q r).2
        _ = 1 := by simp
    _ = ((Finset.univ.filter (fun q : Fin k → I × I ↦
        quadraticPowerResultSupport k q = S)).card : ℝ) := by simp

lemma card_quadraticPowerFiber_one_of_card_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : QuadraticPowerWalshSupport I 1) (hS : S.1.card = 0) :
    (Finset.univ.filter (fun q : Fin 1 → I × I ↦
      quadraticPowerResultSupport 1 q = S)).card ≤ Fintype.card I := by
  let F := Finset.univ.filter (fun q : Fin 1 → I × I ↦
    quadraticPowerResultSupport 1 q = S)
  have hdiag (q : ↑F) : (q.1 0).1 = (q.1 0).2 := by
    have hqS := (Finset.mem_filter.mp q.2).2
    have hsupp := congrArg Subtype.val hqS
    rw [quadraticPowerResultSupport_one_val] at hsupp
    have hcard := card_rademacherPairSupport (q.1 0)
    rw [hsupp, hS] at hcard
    by_contra hne
    simp [hne] at hcard
  let f : ↑F → I := fun q ↦ (q.1 0).1
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    funext x
    have hx : x = 0 := Subsingleton.elim x 0
    subst x
    apply Prod.ext
    · change (q.1 0).1 = (r.1 0).1 at hqr
      exact hqr
    · change (q.1 0).1 = (r.1 0).1 at hqr
      rw [← hdiag q, ← hdiag r]
      exact hqr
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma card_quadraticPowerFiber_one_of_card_one
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : QuadraticPowerWalshSupport I 1) (hS : S.1.card = 1) :
    (Finset.univ.filter (fun q : Fin 1 → I × I ↦
      quadraticPowerResultSupport 1 q = S)).card = 0 := by
  have hempty : (Finset.univ.filter (fun q : Fin 1 → I × I ↦
      quadraticPowerResultSupport 1 q = S)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).2
    have hsupp := congrArg Subtype.val hqS
    rw [quadraticPowerResultSupport_one_val] at hsupp
    have hcard := card_rademacherPairSupport (q 0)
    rw [hsupp, hS] at hcard
    by_cases hdiag : (q 0).1 = (q 0).2 <;> simp [hdiag] at hcard
  rw [hempty]
  rfl

lemma card_quadraticPowerFiber_one_of_card_two
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : QuadraticPowerWalshSupport I 1) (hS : S.1.card = 2) :
    (Finset.univ.filter (fun q : Fin 1 → I × I ↦
      quadraticPowerResultSupport 1 q = S)).card ≤ 4 := by
  let F := Finset.univ.filter (fun q : Fin 1 → I × I ↦
    quadraticPowerResultSupport 1 q = S)
  have hsupp (q : ↑F) : rademacherPairSupport (q.1 0) = S.1 := by
    have hqS := (Finset.mem_filter.mp q.2).2
    simpa only [quadraticPowerResultSupport_one_val] using congrArg Subtype.val hqS
  have hne (q : ↑F) : (q.1 0).1 ≠ (q.1 0).2 := by
    intro heq
    have hcard := card_rademacherPairSupport (q.1 0)
    rw [hsupp q, hS] at hcard
    simp [heq] at hcard
  have hleft (q : ↑F) : (q.1 0).1 ∈ S.1 := by
    rw [← hsupp q, rademacherPairSupport, Finset.symmDiff_def]
    simp [hne q]
  have hright (q : ↑F) : (q.1 0).2 ∈ S.1 := by
    rw [← hsupp q, rademacherPairSupport, Finset.symmDiff_def]
    simp [Ne.symm (hne q)]
  let f : ↑F → (↑S.1 × ↑S.1) := fun q ↦
    (⟨(q.1 0).1, hleft q⟩, ⟨(q.1 0).2, hright q⟩)
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    funext x
    have hx : x = 0 := Subsingleton.elim x 0
    subst x
    apply Prod.ext
    · exact congrArg (fun p ↦ p.1.1) hqr
    · exact congrArg (fun p ↦ p.2.1) hqr
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, hS, Nat.reduceMul] using hcard

/-- Source coefficient count for the first quadratic power: the constant
coefficient has size at most `|I|`, while every nonconstant collected Walsh
coefficient has size at most four. -/
lemma norm_quadraticPowerWalshCoeff_one_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (S : QuadraticPowerWalshSupport I 1)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ‖quadraticPowerWalshCoeff A 1 S‖ ≤
      if S.1.card = 0 then (Fintype.card I : ℝ) else 4 := by
  have hbase := norm_quadraticPowerWalshCoeff_le_card_fiber A 1 S hA
  by_cases hS0 : S.1.card = 0
  · rw [if_pos hS0]
    exact hbase.trans (by
      exact_mod_cast card_quadraticPowerFiber_one_of_card_zero S hS0)
  · rw [if_neg hS0]
    have hSle : S.1.card ≤ 2 := by simpa using S.2
    interval_cases hcard : S.1.card
    · exact (hS0 rfl).elim
    · rw [card_quadraticPowerFiber_one_of_card_one S hcard] at hbase
      exact hbase.trans (by norm_num)
    · exact hbase.trans (by
        exact_mod_cast card_quadraticPowerFiber_one_of_card_two S hcard)

/-- Regroup the raw ordered expansion by its resulting Walsh support. -/
lemma rademacherQuadratic_pow_eq_groupedWalshSum
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (xi : I → Bool) (k : ℕ) :
    (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k) =
      ∑ S : QuadraticPowerWalshSupport I k,
        quadraticPowerWalshCoeff A k S * rademacherWalshMonomial S.1 xi := by
  rw [rademacherQuadratic_pow_eq_walshSum]
  let d : (Fin k → I × I) → ℂ := fun q ↦
    ∏ r, (A (q r).1 (q r).2 : ℂ)
  let sigma : (Fin k → I × I) → QuadraticPowerWalshSupport I k :=
    quadraticPowerResultSupport k
  calc
    (∑ q : Fin k → I × I,
        (∏ r, (A (q r).1 (q r).2 : ℂ)) *
          rademacherWalshMonomial (xorSupport rademacherPairSupport q) xi) =
        ∑ q : Fin k → I × I,
          d q * rademacherWalshMonomial (sigma q).1 xi := by rfl
    _ = ∑ S : QuadraticPowerWalshSupport I k,
          ∑ q : Fin k → I × I with sigma q = S,
            d q * rademacherWalshMonomial (sigma q).1 xi := by
      symm
      exact Finset.sum_fiberwise (Finset.univ : Finset (Fin k → I × I))
        sigma (fun q ↦ d q * rademacherWalshMonomial (sigma q).1 xi)
    _ = ∑ S : QuadraticPowerWalshSupport I k,
          quadraticPowerWalshCoeff A k S * rademacherWalshMonomial S.1 xi := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [quadraticPowerWalshCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hsigma : sigma q = S := (Finset.mem_filter.mp hq).2
      rw [← hsigma]

/-- Grouped quadratic-power version of Claim 12.3.  Unlike the raw ordered
sum, this has exactly one coefficient for each degree-`2k` Walsh support;
the remaining source estimate is the finite coefficient-counting bound for
`k = 1,2`. -/
theorem norm_finExpectation_smoothingKernel_mul_groupedRademacherQuadratic_pow_le_gamma
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (k : ℕ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hmass : ((2 * k : ℕ) : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k))‖ ≤
      ∑ S : QuadraticPowerWalshSupport I k,
        ‖quadraticPowerWalshCoeff A k S‖ *
          (4 * ((((∑ i, beta i ^ 2) - S.1.card) / Real.pi ^ 2) ^
            (-((S.1.card : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
              Real.Gamma (((S.1.card : ℝ) + 1) / 2))) := by
  have hsupportMass (S : QuadraticPowerWalshSupport I k) :
      (S.1.card : ℝ) < ∑ i, beta i ^ 2 := by
    have hcast : (S.1.card : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast S.2
    exact hcast.trans_lt hmass
  have hpoint : (fun xi : I → Bool ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ k)) =
      (fun xi ↦
        (Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          ∑ S : QuadraticPowerWalshSupport I k,
            quadraticPowerWalshCoeff A k S *
              rademacherWalshMonomial S.1 xi) := by
    funext xi
    rw [rademacherQuadratic_pow_eq_groupedWalshSum]
  rw [hpoint]
  exact norm_finExpectation_smoothingKernel_mul_walshSum_le_gamma
    beta (quadraticPowerWalshCoeff A k) (fun S ↦ S.1) target hbeta hsupportMass

/-- Fully collected first-power estimate in the coefficient-counting form
used by Claim 12.3.  The remaining finite sum has one term for each support
of cardinality at most two; its coefficient is `|I|` for the constant term
and at most four for every other support. -/
theorem norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_collected
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hmass : (2 : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ))‖ ≤
      ∑ S : QuadraticPowerWalshSupport I 1,
        (if S.1.card = 0 then (Fintype.card I : ℝ) else 4) *
          smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card := by
  have hbase :=
    norm_finExpectation_smoothingKernel_mul_groupedRademacherQuadratic_pow_le_gamma
      beta A 1 target hbeta (by simpa using hmass)
  have hbase' :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦
        (Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ 1))‖ ≤
        ∑ S : QuadraticPowerWalshSupport I 1,
          ‖quadraticPowerWalshCoeff A 1 S‖ *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card := by
    simpa only [smoothingWalshGammaFactor] using hbase
  have hbase'' :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦
        (Esseen.smoothingKernel
          ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
          ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j) : ℝ) : ℂ))‖ ≤
        ∑ S : QuadraticPowerWalshSupport I 1,
          ‖quadraticPowerWalshCoeff A 1 S‖ *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card := by
    simpa only [pow_one] using hbase'
  refine hbase''.trans ?_
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_right
    (norm_quadraticPowerWalshCoeff_one_le A S hA)
  apply smoothingWalshGammaFactor_nonneg
  have hcard : (S.1.card : ℝ) ≤ 2 := by
    exact_mod_cast (by simpa using S.2)
  exact hcard.trans_lt hmass

/-! ## Parseval control for the second quadratic power -/

/-- Uniform expectation of a Walsh monomial on the independent Rademacher
cube.  This is the arbitrary-finite-type version of the usual vanishing of
every nonconstant Walsh character. -/
lemma finExpectation_rademacherWalshMonomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) :
    Fourier.finExpectation (I → Bool) (rademacherWalshMonomial S) =
      if S = ∅ then 1 else 0 := by
  have h := finExpectation_exp_rademacher_linear_mul_walshMonomial
    (fun _ : I ↦ (0 : ℝ)) S
  simp only [Finset.sum_const_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, one_mul, Real.sin_zero, Real.cos_zero] at h
  by_cases hS : S = ∅
  · subst S
    simpa using h
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hprod :
        (∏ i : I, if i ∈ S then Complex.I * 0 else (1 : ℂ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    exact h.trans hprod

/-- Distinct Walsh monomials are orthogonal in the independent Rademacher
cube. -/
lemma finExpectation_rademacherWalshMonomial_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (S T : Finset I) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      rademacherWalshMonomial S xi * rademacherWalshMonomial T xi) =
      if S = T then 1 else 0 := by
  simp_rw [rademacherWalshMonomial_mul]
  rw [finExpectation_rademacherWalshMonomial]
  simp

/-- Parseval for a finite complex Walsh sum whose supports are distinct. -/
lemma finExpectation_norm_sq_walshSum
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (c : J → ℂ) (support : J → Finset I)
    (hsupport : Function.Injective support) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      ((‖∑ j, c j * rademacherWalshMonomial (support j) xi‖ ^ 2 : ℝ) : ℂ)) =
      ∑ j, ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
  have hpoint (xi : I → Bool) :
      ((‖∑ j, c j * rademacherWalshMonomial (support j) xi‖ ^ 2 : ℝ) : ℂ) =
        (∑ j, c j * rademacherWalshMonomial (support j) xi) *
          starRingEnd ℂ (∑ j, c j * rademacherWalshMonomial (support j) xi) := by
    rw [Complex.sq_norm, Complex.mul_conj]
  have hstar (S : Finset I) (xi : I → Bool) :
      starRingEnd ℂ (rademacherWalshMonomial S xi) =
        rademacherWalshMonomial S xi := by
    simp [rademacherWalshMonomial]
  have hexpand : (fun xi : I → Bool ↦
      ((‖∑ j, c j * rademacherWalshMonomial (support j) xi‖ ^ 2 : ℝ) : ℂ)) =
      fun xi ↦ ∑ j, ∑ k,
        (c j * starRingEnd ℂ (c k)) *
          (rademacherWalshMonomial (support j) xi *
            rademacherWalshMonomial (support k) xi) := by
    funext xi
    rw [hpoint]
    simp_rw [map_sum, map_mul, hstar]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hexpand, finExpectation_sum]
  simp_rw [finExpectation_sum, Fourier.finExpectation_const_mul,
    finExpectation_rademacherWalshMonomial_mul]
  classical
  simp [hsupport.eq_iff, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Parseval identifies the squared norm of all collected coefficients in
the second quadratic power with its fourth Rademacher moment. -/
lemma sum_sq_norm_quadraticPowerWalshCoeff_two
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) :
    ∑ S : QuadraticPowerWalshSupport I 2,
        ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2 =
      Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean A 4 := by
  have hp := finExpectation_norm_sq_walshSum
    (I := I) (J := QuadraticPowerWalshSupport I 2)
    (quadraticPowerWalshCoeff A 2) (fun S ↦ S.1)
    (fun S T h ↦ Subtype.ext h)
  have hgroup (xi : I → Bool) :
      ∑ S : QuadraticPowerWalshSupport I 2,
          quadraticPowerWalshCoeff A 2 S *
            rademacherWalshMonomial S.1 xi =
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ 2) :=
    (rademacherQuadratic_pow_eq_groupedWalshSum A xi 2).symm
  have hleft :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        ((‖∑ S : QuadraticPowerWalshSupport I 2,
            quadraticPowerWalshCoeff A 2 S *
              rademacherWalshMonomial S.1 xi‖ ^ 2 : ℝ) : ℂ)) =
        (Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean
          A 4 : ℂ) := by
    rw [Fourier.finExpectation,
      Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [hgroup]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    norm_cast
    ring
  rw [hleft] at hp
  exact_mod_cast hp.symm

/-- Bonami plus the exact quadratic second moment gives a uniform `L²`
bound for all degree-at-most-four collected coefficients. -/
lemma sum_sq_norm_quadraticPowerWalshCoeff_two_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbound : ∀ i j, |A i j| ≤ 1) :
    ∑ S : QuadraticPowerWalshSupport I 2,
        ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2 ≤
      324 * (Fintype.card I : ℝ) ^ 4 := by
  rw [sum_sq_norm_quadraticPowerWalshCoeff_two A]
  have hfour :=
    Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean_two_pow_succ_le
      A 1
  have htwo := quadraticCubeMean_two_le_card_sq_mul A 1 hA hdiag
    (by norm_num) hbound
  norm_num [Erdos88.RademacherHypercontractivity.CubePoly.bonamiExponent]
    at hfour
  calc
    Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean A 4 ≤
        81 *
          Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean
            A 2 ^ 2 := hfour
    _ ≤ 81 * (2 * (Fintype.card I : ℝ) ^ 2 * 1 ^ 2) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (sq_le_sq₀ (by
        unfold Erdos88.RademacherHypercontractivity.CubePoly.quadraticCubeMean
        positivity) (by positivity)).2 htwo
    _ = 324 * (Fintype.card I : ℝ) ^ 4 := by ring

/-- There are at most `|I|^l` possible Walsh supports of cardinality `l`.
The statement is phrased for the bounded support type used by a quadratic
power, but the proof only uses injectivity of the underlying finset. -/
lemma card_quadraticPowerWalshSupport_filter_le_pow
    {I : Type*} [Fintype I] [DecidableEq I] (k l : ℕ) :
    ((Finset.univ : Finset (QuadraticPowerWalshSupport I k)).filter
      (fun S ↦ S.1.card = l)).card ≤ Fintype.card I ^ l := by
  let D := (Finset.univ : Finset (QuadraticPowerWalshSupport I k)).filter
    (fun S ↦ S.1.card = l)
  let f : ↑D → {S : Finset I // S.card = l} := fun S ↦
    ⟨S.1.1, (Finset.mem_filter.mp S.2).2⟩
  have hf : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply Subtype.ext
    change S.1.1 = T.1.1
    exact congrArg (fun U : {S : Finset I // S.card = l} ↦ U.1) h
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_finset_len] at hcard
  have hfinal := hcard.trans (Nat.choose_le_pow _ _)
  simpa only [Fintype.card_coe, D] using hfinal

/-- Degree-by-degree `L¹` control of the coefficients of the squared
quadratic form.  Parseval and Bonami supply the `18 |I|²` factor, while
the square root is the Cauchy--Schwarz cost for at most `|I|^l` supports.
This is the coefficient-summing form needed in Claim 12.3. -/
lemma sum_norm_quadraticPowerWalshCoeff_two_filter_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (l : ℕ)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbound : ∀ i j, |A i j| ≤ 1) :
    ∑ S : QuadraticPowerWalshSupport I 2 with S.1.card = l,
        ‖quadraticPowerWalshCoeff A 2 S‖ ≤
      18 * (Fintype.card I : ℝ) ^ 2 *
        Real.sqrt ((Fintype.card I : ℝ) ^ l) := by
  let D := (Finset.univ : Finset (QuadraticPowerWalshSupport I 2)).filter
    (fun S ↦ S.1.card = l)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt D
    (fun S ↦ ‖quadraticPowerWalshCoeff A 2 S‖) (fun _ ↦ (1 : ℝ))
  have hsq : ∑ S ∈ D, ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2 ≤
      324 * (Fintype.card I : ℝ) ^ 4 := by
    calc
      ∑ S ∈ D, ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2 ≤
          ∑ S : QuadraticPowerWalshSupport I 2,
            ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        intro i hi hnot
        positivity
      _ ≤ 324 * (Fintype.card I : ℝ) ^ 4 :=
        sum_sq_norm_quadraticPowerWalshCoeff_two_le A hA hdiag hbound
  have hsqrt1 : Real.sqrt (∑ S ∈ D,
      ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2) ≤
      18 * (Fintype.card I : ℝ) ^ 2 := by
    calc
      Real.sqrt (∑ S ∈ D, ‖quadraticPowerWalshCoeff A 2 S‖ ^ 2) ≤
          Real.sqrt (324 * (Fintype.card I : ℝ) ^ 4) :=
        Real.sqrt_le_sqrt hsq
      _ = 18 * (Fintype.card I : ℝ) ^ 2 := by
        rw [show 324 * (Fintype.card I : ℝ) ^ 4 =
            (18 * (Fintype.card I : ℝ) ^ 2) ^ 2 by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
  have hcard : (D.card : ℝ) ≤ (Fintype.card I : ℝ) ^ l := by
    exact_mod_cast card_quadraticPowerWalshSupport_filter_le_pow
      (I := I) 2 l
  have hsqrt2 : Real.sqrt (∑ _S ∈ D, (1 : ℝ) ^ 2) ≤
      Real.sqrt ((Fintype.card I : ℝ) ^ l) := by
    apply Real.sqrt_le_sqrt
    simpa only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using hcard
  change (∑ S ∈ D, ‖quadraticPowerWalshCoeff A 2 S‖) ≤ _
  have hc' := hc.trans (mul_le_mul hsqrt1 hsqrt2
    (Real.sqrt_nonneg _) (by positivity))
  simpa only [mul_one] using hc'

/-- The cardinality of a degree-at-most-four support, bundled as an element
of `Fin 5`. -/
def quadraticPowerSupportCardFour
    {I : Type*} [DecidableEq I]
    (S : QuadraticPowerWalshSupport I 2) : Fin 5 :=
  ⟨S.1.card, by omega⟩

/-- Regroup a sum over degree-at-most-four supports by exact cardinality. -/
lemma sum_quadraticPowerWalshSupport_eq_sum_cardFour
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : QuadraticPowerWalshSupport I 2 → ℝ) :
    ∑ S, f S = ∑ l : Fin 5, ∑ S with S.1.card = l.1, f S := by
  let sigma : QuadraticPowerWalshSupport I 2 → Fin 5 :=
    quadraticPowerSupportCardFour
  calc
    ∑ S, f S = ∑ l : Fin 5,
        ∑ S : QuadraticPowerWalshSupport I 2 with sigma S = l, f S := by
      symm
      exact Finset.sum_fiberwise
        (Finset.univ : Finset (QuadraticPowerWalshSupport I 2)) sigma f
    _ = ∑ l : Fin 5, ∑ S with S.1.card = l.1, f S := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr
      · ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact congrArg Fin.val h
        · intro h
          exact Fin.ext h
      · intro S hS
        rfl

/-- Fully collected second-power estimate for Claim 12.3.  The right side
has five explicit degree slices.  Its degree-`l` coefficient mass is bounded
by `18 |I|² sqrt(|I|^l)` and its smoothing factor has the exact inverse
power supplied by the Walsh calculation above. -/
theorem norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_sq_le_collected
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hmass : (4 : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ 2))‖ ≤
      ∑ l : Fin 5,
        (18 * (Fintype.card I : ℝ) ^ 2 *
          Real.sqrt ((Fintype.card I : ℝ) ^ l.1)) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
  have hbase :=
    norm_finExpectation_smoothingKernel_mul_groupedRademacherQuadratic_pow_le_gamma
      beta A 2 target hbeta (by simpa using hmass)
  have hbase' :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        (((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ) ^ 2))‖ ≤
      ∑ S : QuadraticPowerWalshSupport I 2,
        ‖quadraticPowerWalshCoeff A 2 S‖ *
          smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card := by
    simpa only [smoothingWalshGammaFactor] using hbase
  refine hbase'.trans ?_
  rw [sum_quadraticPowerWalshSupport_eq_sum_cardFour]
  apply Finset.sum_le_sum
  intro l hl
  have hfacNonneg : 0 ≤
      smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
    apply smoothingWalshGammaFactor_nonneg
    have hl4 : (l.1 : ℝ) ≤ 4 := by
      exact_mod_cast (Nat.le_of_lt_succ l.2)
    exact hl4.trans_lt hmass
  calc
    ∑ S : QuadraticPowerWalshSupport I 2 with S.1.card = l.1,
        ‖quadraticPowerWalshCoeff A 2 S‖ *
          smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card =
        (∑ S : QuadraticPowerWalshSupport I 2 with S.1.card = l.1,
          ‖quadraticPowerWalshCoeff A 2 S‖) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S hS
      have hcard := (Finset.mem_filter.mp hS).2
      rw [hcard]
    _ ≤ (18 * (Fintype.card I : ℝ) ^ 2 *
          Real.sqrt ((Fintype.card I : ℝ) ^ l.1)) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
      apply mul_le_mul_of_nonneg_right _ hfacNonneg
      exact sum_norm_quadraticPowerWalshCoeff_two_filter_le
        A l.1 hA hdiag hbound

/-- Indicator form of the collected second-power estimate.  This is the
form used in Claim 12.2: on the unit interval the smoothing kernel
majorizes one, so the degree-sliced Claim 12.3 estimate controls the
quadratic second moment restricted to that interval. -/
theorem finExpectation_rademacherQuadratic_sq_indicator_le_collected
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hmass : (4 : ℝ) < ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j)) ^ 2 else 0) ≤
      ∑ l : Fin 5,
        (18 * (Fintype.card I : ℝ) ^ 2 *
          Real.sqrt ((Fintype.card I : ℝ) ^ l.1)) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let Q : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  let K : (I → Bool) → ℝ := fun xi ↦
    Esseen.smoothingKernel (L xi - target) * Q xi ^ 2
  have hmono (xi : I → Bool) :
      (if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) ≤ K xi := by
    by_cases hx : |L xi - target| ≤ 1
    · rw [if_pos hx]
      dsimp only [K]
      have hk := Esseen.one_le_smoothingKernel hx
      nlinarith [sq_nonneg (Q xi)]
    · rw [if_neg hx]
      dsimp only [K]
      exact mul_nonneg (Esseen.smoothingKernel_nonneg _) (sq_nonneg _)
  have hmeanMono :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) ≤
        Fourier.finExpectation (I → Bool) K := by
    rw [Fourier.finExpectation, Fourier.finExpectation,
      div_le_div_iff_of_pos_right]
    · exact Finset.sum_le_sum fun xi _ ↦ hmono xi
    · exact_mod_cast Fintype.card_pos
  have hKnonneg (xi : I → Bool) : 0 ≤ K xi := by
    dsimp only [K]
    exact mul_nonneg (Esseen.smoothingKernel_nonneg _) (sq_nonneg _)
  have hcast :
      Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ)) =
        ((Fourier.finExpectation (I → Bool) K : ℝ) : ℂ) := by
    rw [Fourier.finExpectation, Fourier.finExpectation]
    push_cast
    rfl
  have hnorm :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ =
        Fourier.finExpectation (I → Bool) K := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [Fourier.finExpectation]
    exact div_nonneg (Finset.sum_nonneg fun xi _ ↦ hKnonneg xi)
      (by positivity)
  have hkernel :=
    norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_sq_le_collected
      beta A target hbeta hA hdiag hbound hmass
  have hkernel' :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ ≤
      ∑ l : Fin 5,
        (18 * (Fintype.card I : ℝ) ^ 2 *
          Real.sqrt ((Fintype.card I : ℝ) ^ l.1)) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
    simpa only [K, L, Q, Complex.ofReal_mul, Complex.ofReal_pow] using hkernel
  simpa only [L, Q] using hmeanMono.trans (hnorm.symm.le.trans hkernel')

/-- A uniform numerical bound for the five Gamma values occurring in the
degree-at-most-four estimate. -/
lemma Gamma_card_le_four_le_two (m : ℕ) (hm : m ≤ 4) :
    Real.Gamma (((m : ℝ) + 1) / 2) ≤ 2 := by
  interval_cases m
  · rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num,
      Real.Gamma_one_half_eq]
    have hsqrt : Real.sqrt Real.pi ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt Real.pi_le_four
    convert hsqrt using 1 <;> norm_num
  · norm_num [Real.Gamma_one]
  · norm_num
    exact Real.Gamma_three_div_two_lt_one.le.trans (by norm_num)
  · norm_num [Real.Gamma_two]
  · have hrec := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
    have hthree := Real.Gamma_three_div_two_lt_one
    norm_num at hrec ⊢
    rw [hrec]
    nlinarith [Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]

/-- Uniformly simplify the exact Gamma factor when the coefficient mass is
at least eight.  The intentionally coarse constant `32` avoids any hidden
asymptotic notation and is adequate for Claim 12.2. -/
lemma smoothingWalshGammaFactor_le
    {M : ℝ} {m : ℕ} (hM : 8 ≤ M) (hm : m ≤ 4) :
    smoothingWalshGammaFactor M m ≤
      4 * (M / 32) ^ (-((m : ℝ) + 1) / 2) := by
  have hpiSq : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos.le, Real.pi_le_four,
      sq_nonneg (4 - Real.pi)]
  have hmR : (m : ℝ) ≤ 4 := by exact_mod_cast hm
  have hbase : M / 32 ≤ (M - m) / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 32)
      (sq_pos_of_pos Real.pi_pos)]
    have hmul := mul_le_mul_of_nonneg_left hpiSq (by linarith : 0 ≤ M)
    nlinarith
  have hM32 : 0 ≤ M / 32 := by positivity
  let p : ℝ := ((m : ℝ) + 1) / 2
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hM32pos : 0 < M / 32 := by positivity
  have hotherPos : 0 < (M - m) / Real.pi ^ 2 := hM32pos.trans_le hbase
  have hpow := Real.rpow_le_rpow hM32 hbase hp
  have hrpowNeg : ((M - m) / Real.pi ^ 2) ^ (-p) ≤
      (M / 32) ^ (-p) := by
    rw [Real.rpow_neg hotherPos.le, Real.rpow_neg hM32]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hotherPos p)
      (Real.rpow_pos_of_pos hM32pos p)).2 hpow
  have hexpEq : -((m : ℝ) + 1) / 2 = -p := by
    dsimp only [p]
    ring
  have hrpow : ((M - m) / Real.pi ^ 2) ^ (-((m : ℝ) + 1) / 2) ≤
      (M / 32) ^ (-((m : ℝ) + 1) / 2) := by
    rw [hexpEq]
    exact hrpowNeg
  unfold smoothingWalshGammaFactor
  have hgamma := Gamma_card_le_four_le_two m hm
  have hrpowNonneg : 0 ≤ (M / 32) ^ (-((m : ℝ) + 1) / 2) :=
    Real.rpow_nonneg hM32 _
  have hgammaPos : 0 ≤ Real.Gamma (((m : ℝ) + 1) / 2) :=
    (Real.Gamma_pos_of_pos (by positivity)).le
  calc
    4 * (((M - ↑m) / Real.pi ^ 2) ^ (-((m : ℝ) + 1) / 2) *
        (1 / 2 : ℝ) * Real.Gamma (((m : ℝ) + 1) / 2)) ≤
        4 * ((M / 32) ^ (-((m : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
          Real.Gamma (((m : ℝ) + 1) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ hgammaPos
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact hrpow
    _ ≤ 4 * (M / 32) ^ (-((m : ℝ) + 1) / 2) := by
      calc
        4 * ((M / 32) ^ (-((m : ℝ) + 1) / 2) * (1 / 2 : ℝ) *
          Real.Gamma (((m : ℝ) + 1) / 2)) ≤
            4 * ((M / 32) ^ (-((m : ℝ) + 1) / 2) *
              (1 / 2 : ℝ) * 2) := by
          gcongr
        _ = 4 * (M / 32) ^ (-((m : ℝ) + 1) / 2) := by ring

/-- The power of the ambient cardinality in every degree slice of the
second-power estimate is exactly `3 / 2`. -/
lemma degreeSlice_scale {N q : ℝ} {m : ℕ}
    (hN : 0 < N) (hq : 0 < q) :
    N ^ 2 * Real.sqrt (N ^ m) *
        ((q * N / 32) ^ (-((m : ℝ) + 1) / 2)) =
      (q / 32) ^ (-((m : ℝ) + 1) / 2) *
        N ^ (3 / 2 : ℝ) := by
  have hq32 : 0 ≤ q / 32 := by positivity
  have hN0 : 0 ≤ N := hN.le
  have hbase : q * N / 32 = (q / 32) * N := by ring
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast N 2, ← Real.rpow_natCast N m]
  rw [← Real.rpow_mul hN0]
  rw [hbase, Real.mul_rpow hq32 hN0]
  rw [← Real.rpow_add hN]
  rw [show
      N ^ (((2 : ℕ) : ℝ) + (m : ℝ) * (1 / 2 : ℝ)) *
          ((q / 32) ^ (-((m : ℝ) + 1) / 2) *
            N ^ (-((m : ℝ) + 1) / 2)) =
        (q / 32) ^ (-((m : ℝ) + 1) / 2) *
          (N ^ (((2 : ℕ) : ℝ) + (m : ℝ) * (1 / 2 : ℝ)) *
            N ^ (-((m : ℝ) + 1) / 2)) by ring]
  rw [← Real.rpow_add hN]
  congr 1
  ring

/-- Source-scale simplification of one degree slice.  A linear lower bound
`q * N` on the coefficient mass makes every degree at most four contribute
at most a `q`-dependent constant times `N^(3/2)`. -/
lemma degreeSlice_le_sourceScale {N M q : ℝ} {m : ℕ}
    (hN : 0 < N) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : m ≤ 4) (hMN : q * N ≤ M) :
    N ^ 2 * Real.sqrt (N ^ m) *
        ((M / 32) ^ (-((m : ℝ) + 1) / 2)) ≤
      (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
  have hq32pos : 0 < q / 32 := by positivity
  have hq32one : q / 32 ≤ 1 := by linarith
  have hM32 : q * N / 32 ≤ M / 32 := by linarith
  have hqN32pos : 0 < q * N / 32 := by positivity
  have hp : -((m : ℝ) + 1) / 2 ≤ 0 := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hinv : (M / 32) ^ (-((m : ℝ) + 1) / 2) ≤
      (q * N / 32) ^ (-((m : ℝ) + 1) / 2) :=
    Real.rpow_le_rpow_of_nonpos hqN32pos hM32 hp
  have hmR : (m : ℝ) ≤ 4 := by exact_mod_cast hm
  have hqpow : (q / 32) ^ (-((m : ℝ) + 1) / 2) ≤
      (q / 32) ^ (-(5 : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_ge hq32pos hq32one
    linarith
  calc
    N ^ 2 * Real.sqrt (N ^ m) *
        ((M / 32) ^ (-((m : ℝ) + 1) / 2)) ≤
        N ^ 2 * Real.sqrt (N ^ m) *
          ((q * N / 32) ^ (-((m : ℝ) + 1) / 2)) := by
      gcongr
    _ = (q / 32) ^ (-((m : ℝ) + 1) / 2) * N ^ (3 / 2 : ℝ) :=
      degreeSlice_scale hN hq
    _ ≤ (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
      gcongr

/-- Claim 12.3 at the source scale for the quadratic second moment.  If the
linear coefficient mass is at least `q |I|`, the quadratic square restricted
to a unit window has expectation `O_q(|I|^(3/2))`, with an explicit constant. -/
theorem finExpectation_rademacherQuadratic_sq_indicator_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j)) ^ 2 else 0) ≤
      360 * (q / 32) ^ (-(5 : ℝ) / 2) *
        (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
  let N : ℝ := Fintype.card I
  let M : ℝ := ∑ i, beta i ^ 2
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hbase := finExpectation_rademacherQuadratic_sq_indicator_le_collected
    beta A target hbeta hA hdiag hbound (by linarith)
  have hmassM : 8 ≤ M := by simpa only [M] using hmass
  calc
    Fourier.finExpectation (I → Bool) (fun xi ↦
        if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
          (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j)) ^ 2 else 0) ≤
        ∑ l : Fin 5,
          (18 * N ^ 2 * Real.sqrt (N ^ l.1)) *
            smoothingWalshGammaFactor M l.1 := by
      simpa only [N, M] using hbase
    _ ≤ ∑ _l : Fin 5,
        72 * (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hl4 : l.1 ≤ 4 := by omega
      have hfac := smoothingWalshGammaFactor_le hmassM hl4
      calc
        (18 * N ^ 2 * Real.sqrt (N ^ l.1)) *
            smoothingWalshGammaFactor M l.1 ≤
            (18 * N ^ 2 * Real.sqrt (N ^ l.1)) *
              (4 * (M / 32) ^ (-((l.1 : ℝ) + 1) / 2)) := by
          gcongr
        _ = 72 * (N ^ 2 * Real.sqrt (N ^ l.1) *
              (M / 32) ^ (-((l.1 : ℝ) + 1) / 2)) := by ring
        _ ≤ 72 * ((q / 32) ^ (-(5 : ℝ) / 2) *
              N ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (degreeSlice_le_sourceScale hN hq hq1 hl4 hqmass) (by norm_num)
        _ = 72 * (q / 32) ^ (-(5 : ℝ) / 2) *
              N ^ (3 / 2 : ℝ) := by ring
    _ = 360 * (q / 32) ^ (-(5 : ℝ) / 2) *
        (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
      simp only [Fin.sum_univ_five]
      dsimp only [N]
      ring

def quadraticPowerSupportCardTwo
    {I : Type*} [DecidableEq I]
    (S : QuadraticPowerWalshSupport I 1) : Fin 3 :=
  ⟨S.1.card, by omega⟩

lemma sum_quadraticPowerWalshSupport_one_eq_sum_cardTwo
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : QuadraticPowerWalshSupport I 1 → ℝ) :
    ∑ S, f S = ∑ l : Fin 3, ∑ S with S.1.card = l.1, f S := by
  let sigma : QuadraticPowerWalshSupport I 1 → Fin 3 :=
    quadraticPowerSupportCardTwo
  calc
    ∑ S, f S = ∑ l : Fin 3,
        ∑ S : QuadraticPowerWalshSupport I 1 with sigma S = l, f S := by
      symm
      exact Finset.sum_fiberwise
        (Finset.univ : Finset (QuadraticPowerWalshSupport I 1)) sigma f
    _ = ∑ l : Fin 3, ∑ S with S.1.card = l.1, f S := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr
      · ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact congrArg Fin.val h
        · intro h
          exact Fin.ext h
      · intro S hS
        rfl

theorem norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_cardTwo
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : I → ℝ) (A : I → I → ℝ) (target : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hmass : (2 : ℝ) < ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ))‖ ≤
      ∑ l : Fin 3,
        ((if l.1 = 0 then (Fintype.card I : ℝ) else 4) *
          (Fintype.card I : ℝ) ^ l.1) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := by
  have hbase := norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_collected
    beta A target hbeta hA hmass
  refine hbase.trans ?_
  rw [sum_quadraticPowerWalshSupport_one_eq_sum_cardTwo]
  apply Finset.sum_le_sum
  intro l hl
  let D := (Finset.univ : Finset (QuadraticPowerWalshSupport I 1)).filter
    (fun S ↦ S.1.card = l.1)
  let c : ℝ := if l.1 = 0 then (Fintype.card I : ℝ) else 4
  let g : ℝ := smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1
  have hc : 0 ≤ c := by
    dsimp only [c]
    split <;> positivity
  have hg : 0 ≤ g := by
    dsimp only [g]
    apply smoothingWalshGammaFactor_nonneg
    have hl2 : (l.1 : ℝ) ≤ 2 := by
      exact_mod_cast (Nat.le_of_lt_succ l.2)
    exact hl2.trans_lt hmass
  have hcard : (D.card : ℝ) ≤ (Fintype.card I : ℝ) ^ l.1 := by
    exact_mod_cast card_quadraticPowerWalshSupport_filter_le_pow
      (I := I) 1 l.1
  change Finset.sum D (fun S ↦
      (if S.1.card = 0 then (Fintype.card I : ℝ) else 4) *
        smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card) ≤ _
  calc
    Finset.sum D (fun S ↦
      (if S.1.card = 0 then (Fintype.card I : ℝ) else 4) *
        smoothingWalshGammaFactor (∑ i, beta i ^ 2) S.1.card) =
        Finset.sum D (fun _S ↦ c * g) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSl : S.1.card = l.1 := (Finset.mem_filter.mp hS).2
      simp only [c, g, hSl]
    _ = (D.card : ℝ) * (c * g) := by simp
    _ ≤ (Fintype.card I : ℝ) ^ l.1 * (c * g) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hc hg)
    _ = (c * (Fintype.card I : ℝ) ^ l.1) * g := by ring
    _ = ((if l.1 = 0 then (Fintype.card I : ℝ) else 4) *
          (Fintype.card I : ℝ) ^ l.1) *
            smoothingWalshGammaFactor (∑ i, beta i ^ 2) l.1 := rfl

lemma firstDegreeSlice_le_sourceScale {N M q : ℝ} {m : ℕ}
    (hN : 1 ≤ N) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : m ≤ 2) (hMN : q * N ≤ M) :
    ((if m = 0 then N else 4) * N ^ m) *
        ((M / 32) ^ (-((m : ℝ) + 1) / 2)) ≤
      4 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hq32pos : 0 < q / 32 := by positivity
  have hq32one : q / 32 ≤ 1 := by linarith
  have hM32 : q * N / 32 ≤ M / 32 := by linarith
  have hqN32pos : 0 < q * N / 32 := by positivity
  have hp : -((m : ℝ) + 1) / 2 ≤ 0 := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hinv : (M / 32) ^ (-((m : ℝ) + 1) / 2) ≤
      (q * N / 32) ^ (-((m : ℝ) + 1) / 2) :=
    Real.rpow_le_rpow_of_nonpos hqN32pos hM32 hp
  calc
    ((if m = 0 then N else 4) * N ^ m) *
        ((M / 32) ^ (-((m : ℝ) + 1) / 2)) ≤
      ((if m = 0 then N else 4) * N ^ m) *
        ((q * N / 32) ^ (-((m : ℝ) + 1) / 2)) := by
      gcongr
    _ ≤ 4 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N := by
      interval_cases m
      · rw [if_pos rfl, pow_zero, mul_one]
        norm_num only [Nat.cast_zero, zero_add]
        rw [show q * N / 32 = (q / 32) * N by ring,
          Real.mul_rpow hq32pos.le hNpos.le]
        norm_num only
        have hleft :
            N * ((q / 32) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2)) =
              (q / 32) ^ (-(1 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
          calc
            N * ((q / 32) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2)) =
              (q / 32) ^ (-(1 : ℝ) / 2) *
                (N * N ^ (-(1 : ℝ) / 2)) := by ring
            _ = (q / 32) ^ (-(1 : ℝ) / 2) *
                (N ^ (1 : ℝ) * N ^ (-(1 : ℝ) / 2)) := by
              rw [Real.rpow_one]
            _ = (q / 32) ^ (-(1 : ℝ) / 2) *
                N ^ ((1 : ℝ) + (-(1 : ℝ) / 2)) := by
              rw [Real.rpow_add hNpos]
            _ = (q / 32) ^ (-(1 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
              congr 1
              ring
        have hleft' :
            N * ((q / 32) ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ))) =
              (q / 32) ^ (-(1 / 2 : ℝ)) * N ^ (1 / 2 : ℝ) := by
          convert hleft using 1 <;> ring
        rw [hleft', Real.sqrt_eq_rpow]
        have hqpow : (q / 32) ^ (-(1 : ℝ) / 2) ≤
            (q / 32) ^ (-(3 : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_ge hq32pos hq32one
          norm_num
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
        nlinarith [Real.rpow_nonneg hq32pos.le (-(3 : ℝ) / 2)]
      · rw [if_neg one_ne_zero, pow_one]
        norm_num only [Nat.cast_one]
        rw [show q * N / 32 = (q / 32) * N by ring,
          Real.mul_rpow hq32pos.le hNpos.le]
        norm_num only
        have hNinv : N * N ^ (-(1 : ℝ)) = 1 := by
          rw [Real.rpow_neg_one, mul_inv_cancel₀]
          exact ne_of_gt hNpos
        have hleft :
            4 * N * ((q / 32) ^ (-(1 : ℝ)) * N ^ (-(1 : ℝ))) =
              4 * (q / 32) ^ (-(1 : ℝ)) := by
          rw [show
            4 * N * ((q / 32) ^ (-(1 : ℝ)) * N ^ (-(1 : ℝ))) =
              4 * (q / 32) ^ (-(1 : ℝ)) *
                (N * N ^ (-(1 : ℝ))) by ring, hNinv, mul_one]
        rw [hleft, Real.sqrt_eq_rpow]
        have hsqrt : 1 ≤ N ^ (1 / 2 : ℝ) := by
          exact Real.one_le_rpow hN (by norm_num)
        have hqpow : (q / 32) ^ (-(1 : ℝ)) ≤
            (q / 32) ^ (-(3 : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_ge hq32pos hq32one
          norm_num
        have hcalc :
            4 * (q / 32) ^ (-(1 : ℝ)) ≤
              4 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
          calc
          4 * (q / 32) ^ (-(1 : ℝ)) ≤
              4 * (q / 32) ^ (-(3 : ℝ) / 2) := by gcongr
          _ ≤ 4 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
            exact le_mul_of_one_le_right
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hq32pos.le _)) hsqrt
        convert hcalc using 1 <;> ring
      · rw [if_neg (by norm_num : (2 : ℕ) ≠ 0)]
        norm_num only [Nat.cast_ofNat]
        rw [show q * N / 32 = (q / 32) * N by ring,
          Real.mul_rpow hq32pos.le hNpos.le]
        norm_num only
        rw [Real.sqrt_eq_rpow]
        have hleft :
            4 * N ^ 2 *
                ((q / 32) ^ (-(3 : ℝ) / 2) * N ^ (-(3 : ℝ) / 2)) =
              4 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
          calc
            4 * N ^ 2 *
                ((q / 32) ^ (-(3 : ℝ) / 2) * N ^ (-(3 : ℝ) / 2)) =
              4 * (q / 32) ^ (-(3 : ℝ) / 2) *
                (N ^ (2 : ℕ) * N ^ (-(3 : ℝ) / 2)) := by ac_rfl
            _ = 4 * (q / 32) ^ (-(3 : ℝ) / 2) *
                (N ^ (2 : ℝ) * N ^ (-(3 : ℝ) / 2)) := by
              have he : N ^ (2 : ℕ) = N ^ (2 : ℝ) :=
                (Real.rpow_natCast N 2).symm
              rw [he]
            _ = 4 * (q / 32) ^ (-(3 : ℝ) / 2) *
                N ^ ((2 : ℝ) + (-(3 : ℝ) / 2)) := by
              rw [Real.rpow_add hNpos]
            _ = 4 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
              rw [show (2 : ℝ) + (-(3 : ℝ) / 2) = 1 / 2 by ring]
        have hexp : (-(3 : ℝ) / 2) = (-(3 / 2 : ℝ)) := by ring
        rw [hexp] at hleft
        exact hleft.le

theorem norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ))‖ ≤
      48 * (q / 32) ^ (-(3 : ℝ) / 2) *
        Real.sqrt (Fintype.card I : ℝ) := by
  let N : ℝ := Fintype.card I
  let M : ℝ := ∑ i, beta i ^ 2
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos
  have hmassM : 8 ≤ M := by simpa only [M] using hmass
  have hbase := norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_cardTwo
    beta A target hbeta hA (by linarith)
  calc
    ‖Fourier.finExpectation (I → Bool) (fun xi ↦
      (Esseen.smoothingKernel
        ((∑ i, beta i * Fourier.rademacherSign (xi i)) - target) : ℂ) *
        ((∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) : ℝ) : ℂ))‖ ≤
        ∑ l : Fin 3,
          ((if l.1 = 0 then N else 4) * N ^ l.1) *
            smoothingWalshGammaFactor M l.1 := by
      simpa only [N, M] using hbase
    _ ≤ ∑ _l : Fin 3,
        16 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N := by
      apply Finset.sum_le_sum
      intro l hl
      have hl2 : l.1 ≤ 2 := by omega
      have hfac := smoothingWalshGammaFactor_le hmassM (hl2.trans (by norm_num))
      calc
        ((if l.1 = 0 then N else 4) * N ^ l.1) *
            smoothingWalshGammaFactor M l.1 ≤
          ((if l.1 = 0 then N else 4) * N ^ l.1) *
            (4 * (M / 32) ^ (-((l.1 : ℝ) + 1) / 2)) := by
              gcongr
        _ = 4 * (((if l.1 = 0 then N else 4) * N ^ l.1) *
            (M / 32) ^ (-((l.1 : ℝ) + 1) / 2)) := by ring
        _ ≤ 4 * (4 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left
            (firstDegreeSlice_le_sourceScale hN hq hq1 hl2 hqmass)
            (by norm_num)
        _ = 16 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N := by ring
    _ = 48 * (q / 32) ^ (-(3 : ℝ) / 2) *
        Real.sqrt (Fintype.card I : ℝ) := by
      simp only [Fin.sum_univ_three]
      dsimp only [N]
      ring

theorem finExpectation_rademacherQuadratic_indicator_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, |A i j| ≤ 1)
    (hQnonneg : ∀ xi : I → Bool,
      0 ≤ ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi j))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) else 0) ≤
      48 * (q / 32) ^ (-(3 : ℝ) / 2) *
        Real.sqrt (Fintype.card I : ℝ) := by
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let Q : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  let K : (I → Bool) → ℝ := fun xi ↦
    Esseen.smoothingKernel (L xi - target) * Q xi
  have hmono (xi : I → Bool) :
      (if |L xi - target| ≤ 1 then Q xi else 0) ≤ K xi := by
    by_cases hx : |L xi - target| ≤ 1
    · rw [if_pos hx]
      dsimp only [K]
      exact le_mul_of_one_le_left (hQnonneg xi) (Esseen.one_le_smoothingKernel hx)
    · rw [if_neg hx]
      dsimp only [K]
      exact mul_nonneg (Esseen.smoothingKernel_nonneg _) (hQnonneg xi)
  have hmeanMono :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then Q xi else 0) ≤
        Fourier.finExpectation (I → Bool) K := by
    rw [Fourier.finExpectation, Fourier.finExpectation,
      div_le_div_iff_of_pos_right]
    · exact Finset.sum_le_sum fun xi _ ↦ hmono xi
    · exact_mod_cast Fintype.card_pos
  have hKnonneg (xi : I → Bool) : 0 ≤ K xi := by
    dsimp only [K]
    exact mul_nonneg (Esseen.smoothingKernel_nonneg _) (hQnonneg xi)
  have hcast :
      Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ)) =
        ((Fourier.finExpectation (I → Bool) K : ℝ) : ℂ) := by
    rw [Fourier.finExpectation, Fourier.finExpectation]
    push_cast
    rfl
  have hnorm :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ =
        Fourier.finExpectation (I → Bool) K := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [Fourier.finExpectation]
    exact div_nonneg (Finset.sum_nonneg fun xi _ ↦ hKnonneg xi) (by positivity)
  have hkernel :=
    norm_finExpectation_smoothingKernel_mul_rademacherQuadratic_le_sourceScale
      beta A target q hbeta hA hq hq1 hmass hqmass
  have hkernel' :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ ≤
        48 * (q / 32) ^ (-(3 : ℝ) / 2) *
          Real.sqrt (Fintype.card I : ℝ) := by
    simpa only [K, L, Q, Complex.ofReal_mul] using hkernel
  simpa only [L, Q] using hmeanMono.trans (hnorm.symm.le.trans hkernel')


lemma finExpectation_const_mul_real
    (Omega : Type*) [Fintype Omega] [Nonempty Omega]
    (c : ℝ) (f : Omega → ℝ) :
    Fourier.finExpectation Omega (fun omega ↦ c * f omega) =
      c * Fourier.finExpectation Omega f := by
  rw [Fourier.finExpectation, Fourier.finExpectation]
  rw [← Finset.mul_sum]
  ring

/-- The two weighted Claim 12.3 estimates combined in the normalization
used by Claim 12.2. -/
theorem finExpectation_shiftMoment_indicator_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A B : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i) (hAdiag : ∀ i, A i i = 0)
    (hAbound : ∀ i j, |A i j| ≤ 1)
    (hBbound : ∀ i j, |B i j| ≤ 1)
    (hBnonneg : ∀ xi : I → Bool,
      0 ≤ ∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi j))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        ((1 / 8 : ℝ) *
          (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))) ^ 2 +
        ((Fintype.card I : ℝ) / 16) *
          (∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))
      else 0) ≤
      ((45 / 8 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
  let N : ℝ := Fintype.card I
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let QA : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  let QB : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hNsqrt : N * Real.sqrt N = N ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      N * N ^ (1 / 2 : ℝ) = N ^ (1 : ℝ) * N ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hNpos]
      _ = N ^ (3 / 2 : ℝ) := by congr 1 <;> ring
  have htwo := finExpectation_rademacherQuadratic_sq_indicator_le_sourceScale
    beta A target q hbeta hA hAdiag hAbound hq hq1 hmass hqmass
  have hone := finExpectation_rademacherQuadratic_indicator_le_sourceScale
    beta B target q hbeta hBbound hBnonneg hq hq1 hmass hqmass
  have htwoScaled :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) ≤
        (45 / 8 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by
    have hfun : (fun xi : I → Bool ↦
        if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) =
      (fun xi ↦ (1 / 64 : ℝ) *
        (if |L xi - target| ≤ 1 then QA xi ^ 2 else 0)) := by
      funext xi
      by_cases hx : |L xi - target| ≤ 1 <;> simp [hx] <;> ring
    rw [hfun, finExpectation_const_mul_real]
    calc
      (1 / 64 : ℝ) * Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then QA xi ^ 2 else 0) ≤
          (1 / 64 : ℝ) *
            (360 * (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [L, QA, N] using htwo
        · norm_num
      _ = (45 / 8 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by ring
  have honeScaled :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) ≤
        3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
    rw [finExpectation_const_mul_real]
    calc
      (N / 16) * Fourier.finExpectation (I → Bool) (fun xi ↦
          if |L xi - target| ≤ 1 then QB xi else 0) ≤
        (N / 16) *
          (48 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [L, QB, N] using hone
        · positivity
      _ = 3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
        rw [show (N / 16) *
          (48 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N) =
            3 * (q / 32) ^ (-(3 : ℝ) / 2) *
              (N * Real.sqrt N) by ring, hNsqrt]
  have hsplit : (fun xi : I → Bool ↦
      if |L xi - target| ≤ 1 then
        ((1 / 8 : ℝ) * QA xi) ^ 2 + (N / 16) * QB xi else 0) =
      (fun xi ↦
        (if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) +
          (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) := by
    funext xi
    by_cases hx : |L xi - target| ≤ 1 <;> simp [hx]
  change Fourier.finExpectation (I → Bool) (fun xi ↦
      if |L xi - target| ≤ 1 then
        ((1 / 8 : ℝ) * QA xi) ^ 2 + (N / 16) * QB xi else 0) ≤ _
  rw [hsplit, Erdos88.QuadraticCancellation.finExpectation_add_real]
  calc
    Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) +
      Fourier.finExpectation (I → Bool) (fun xi ↦
        (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) ≤
      (45 / 8 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) :=
      add_le_add htwoScaled honeScaled
    _ = ((45 / 8 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
      dsimp only [N]
      ring


theorem finExpectation_rademacherLinear_indicator_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hq : 0 < q)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1
      then 1 else 0) ≤
      4 * (q / 32) ^ (-(1 : ℝ) / 2) *
        (Fintype.card I : ℝ) ^ (-(1 : ℝ) / 2) := by
  let N : ℝ := Fintype.card I
  let M : ℝ := ∑ i, beta i ^ 2
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let K : (I → Bool) → ℝ := fun xi ↦
    Esseen.smoothingKernel (L xi - target)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hq32 : 0 ≤ q / 32 := by positivity
  have hN0 : 0 ≤ N := hN.le
  have hqN32 : q * N / 32 ≤ M / 32 := by
    dsimp only [N, M]
    linarith
  have hqN32pos : 0 < q * N / 32 := by positivity
  have hM32pos : 0 < M / 32 := by
    dsimp only [M]
    positivity
  have hinv : (M / 32) ^ (-(1 : ℝ) / 2) ≤
      (q * N / 32) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hqN32pos hqN32 (by norm_num)
  have hscale : (q * N / 32) ^ (-(1 : ℝ) / 2) =
      (q / 32) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) := by
    rw [show q * N / 32 = (q / 32) * N by ring,
      Real.mul_rpow hq32 hN0]
  have hmono (xi : I → Bool) :
      (if |L xi - target| ≤ 1 then (1 : ℝ) else 0) ≤ K xi := by
    by_cases hx : |L xi - target| ≤ 1
    · rw [if_pos hx]
      exact Esseen.one_le_smoothingKernel hx
    · rw [if_neg hx]
      exact Esseen.smoothingKernel_nonneg _
  have hmeanMono :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then (1 : ℝ) else 0) ≤
        Fourier.finExpectation (I → Bool) K := by
    rw [Fourier.finExpectation, Fourier.finExpectation,
      div_le_div_iff_of_pos_right]
    · exact Finset.sum_le_sum fun xi _ ↦ hmono xi
    · exact_mod_cast Fintype.card_pos
  have hKnonneg (xi : I → Bool) : 0 ≤ K xi := by
    exact Esseen.smoothingKernel_nonneg _
  have hcast :
      Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ)) =
        ((Fourier.finExpectation (I → Bool) K : ℝ) : ℂ) := by
    rw [Fourier.finExpectation, Fourier.finExpectation]
    push_cast
    rfl
  have hnorm :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ =
        Fourier.finExpectation (I → Bool) K := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [Fourier.finExpectation]
    exact div_nonneg (Finset.sum_nonneg fun xi _ ↦ hKnonneg xi) (by positivity)
  have hkernel :=
    norm_finExpectation_smoothingKernel_mul_walshMonomial_le_gamma
      beta (∅ : Finset I) target hbeta (by
        simp only [Finset.card_empty, Nat.cast_zero]
        linarith)
  have hkernel' :
      ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ ≤
        smoothingWalshGammaFactor M 0 := by
    simpa only [K, L, rademacherWalshMonomial, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.cast_zero, M, smoothingWalshGammaFactor] using hkernel
  have hfac : smoothingWalshGammaFactor M 0 ≤
      4 * (M / 32) ^ (-(1 : ℝ) / 2) := by
    simpa only [Nat.cast_zero, zero_add] using
      (smoothingWalshGammaFactor_le (M := M) (m := 0)
        (by simpa only [M] using hmass) (by norm_num))
  calc
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1
      then 1 else 0) =
        Fourier.finExpectation (I → Bool) (fun xi ↦
          if |L xi - target| ≤ 1 then 1 else 0) := by rfl
    _ ≤ Fourier.finExpectation (I → Bool) K := hmeanMono
    _ = ‖Fourier.finExpectation (I → Bool) (fun xi ↦ (K xi : ℂ))‖ :=
      hnorm.symm
    _ ≤ smoothingWalshGammaFactor M 0 := hkernel'
    _ ≤ 4 * (M / 32) ^ (-(1 : ℝ) / 2) := hfac
    _ ≤ 4 * (q * N / 32) ^ (-(1 : ℝ) / 2) := by gcongr
    _ = 4 * (q / 32) ^ (-(1 : ℝ) / 2) *
        (Fintype.card I : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [hscale]
      dsimp only [N]
      ring


def offDiagonal {I : Type*} [DecidableEq I]
    (A : I → I → ℝ) : I → I → ℝ :=
  fun i j ↦ if i = j then 0 else A i j

lemma rademacherQuadratic_eq_trace_add_offDiagonal
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (xi : I → Bool) :
    (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)) =
      (∑ i, A i i) +
        ∑ i, ∑ j, offDiagonal A i j * Fourier.rademacherSign (xi i) *
          Fourier.rademacherSign (xi j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show A i i = ∑ j, if i = j then A i i else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp only [if_pos, offDiagonal, zero_mul]
    rw [show A i i * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi i) =
      A i i * Fourier.rademacherSign (xi i) ^ 2 by ring,
      Fourier.rademacherSign_sq, mul_one, add_zero]
  · simp only [hij, if_false, offDiagonal, zero_add]

lemma abs_trace_le_card_of_entry_le_one
    {I : Type*} [Fintype I]
    (A : I → I → ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    |∑ i, A i i| ≤ (Fintype.card I : ℝ) := by
  calc
    |∑ i, A i i| ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hA i i
    _ = (Fintype.card I : ℝ) := by simp

theorem finExpectation_rademacherQuadratic_sq_indicator_le_sourceScale_general
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i)
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        ((1 / 8 : ℝ) *
          (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))) ^ 2 else 0) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
  let N : ℝ := Fintype.card I
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let D : ℝ := ∑ i, A i i
  let Q : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, offDiagonal A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hNnonneg : 0 ≤ N := hNpos.le
  have htrace : |D| ≤ N := by
    simpa only [D, N] using abs_trace_le_card_of_entry_le_one A hbound
  have htraceSq : D ^ 2 ≤ N ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg D) hNnonneg).mpr htrace
    simpa only [sq_abs] using hs
  have hoffSymm : ∀ i j, offDiagonal A i j = offDiagonal A j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [offDiagonal, hij, if_false, Ne.symm hij]
      exact hA i j
  have hoffDiag : ∀ i, offDiagonal A i i = 0 := by
    intro i
    simp [offDiagonal]
  have hoffBound : ∀ i j, |offDiagonal A i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · simp [offDiagonal, hij]
    · simpa [offDiagonal, hij] using hbound i j
  have hoff := finExpectation_rademacherQuadratic_sq_indicator_le_sourceScale
    beta (offDiagonal A) target q hbeta hoffSymm hoffDiag hoffBound
      hq hq1 hmass hqmass
  have hevent := finExpectation_rademacherLinear_indicator_le_sourceScale
    beta target q hbeta hq hmass hqmass
  have hNpow : N ^ 2 * N ^ (-(1 : ℝ) / 2) = N ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hpoint (xi : I → Bool) :
      (if |L xi - target| ≤ 1 then
          ((1 / 8 : ℝ) * (D + Q xi)) ^ 2 else 0) ≤
        (1 / 32 : ℝ) * D ^ 2 *
            (if |L xi - target| ≤ 1 then 1 else 0) +
          (1 / 32 : ℝ) *
            (if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) := by
    by_cases hx : |L xi - target| ≤ 1
    · simp only [hx, if_true]
      nlinarith [sq_nonneg (D - Q xi)]
    · simp only [hx, if_false]
      positivity
  have hmeanPoint :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then
          ((1 / 8 : ℝ) * (D + Q xi)) ^ 2 else 0) ≤
        Fourier.finExpectation (I → Bool) (fun xi ↦
          (1 / 32 : ℝ) * D ^ 2 *
              (if |L xi - target| ≤ 1 then 1 else 0) +
            (1 / 32 : ℝ) *
              (if |L xi - target| ≤ 1 then Q xi ^ 2 else 0)) := by
    rw [Fourier.finExpectation, Fourier.finExpectation,
      div_le_div_iff_of_pos_right]
    · exact Finset.sum_le_sum fun xi _ ↦ hpoint xi
    · exact_mod_cast Fintype.card_pos
  have hfirst :
      (1 / 32 : ℝ) * D ^ 2 *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then (1 : ℝ) else 0) ≤
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by
    have heventNonneg : 0 ≤
        Fourier.finExpectation (I → Bool) (fun xi ↦
          if |L xi - target| ≤ 1 then (1 : ℝ) else 0) := by
      rw [Fourier.finExpectation]
      positivity
    calc
      (1 / 32 : ℝ) * D ^ 2 *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then (1 : ℝ) else 0) ≤
        (1 / 32 : ℝ) * N ^ 2 *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then (1 : ℝ) else 0) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htraceSq (by norm_num)) heventNonneg
      _ ≤
        (1 / 32 : ℝ) * N ^ 2 *
          (4 * (q / 32) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [L, N] using hevent
        · positivity
      _ = (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by rw [← hNpow]; ring
  have hsecond :
      (1 / 32 : ℝ) *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) ≤
        (45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by
    calc
      (1 / 32 : ℝ) *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) ≤
        (1 / 32 : ℝ) *
          (360 * (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [L, Q, N] using hoff) (by norm_num)
      _ = (45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) *
          N ^ (3 / 2 : ℝ) := by ring
  have hsplit :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        (1 / 32 : ℝ) * D ^ 2 *
              (if |L xi - target| ≤ 1 then 1 else 0) +
            (1 / 32 : ℝ) *
              (if |L xi - target| ≤ 1 then Q xi ^ 2 else 0)) =
        (1 / 32 : ℝ) * D ^ 2 *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then 1 else 0) +
        (1 / 32 : ℝ) *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) := by
    rw [Erdos88.QuadraticCancellation.finExpectation_add_real,
      finExpectation_const_mul_real, finExpectation_const_mul_real]
  have hrewrite (xi : I → Bool) :
      (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi j)) = D + Q xi := by
    simpa only [D, Q] using rademacherQuadratic_eq_trace_add_offDiagonal A xi
  simp_rw [hrewrite]
  exact hmeanPoint.trans_eq hsplit |>.trans <| by
    calc
      (1 / 32 : ℝ) * D ^ 2 *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then 1 else 0) +
        (1 / 32 : ℝ) *
          Fourier.finExpectation (I → Bool) (fun xi ↦
            if |L xi - target| ≤ 1 then Q xi ^ 2 else 0) ≤
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) * N ^ (3 / 2 : ℝ) +
          (45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) * N ^ (3 / 2 : ℝ) :=
        add_le_add hfirst hsecond
      _ = ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2)) *
            (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
        dsimp only [N]
        ring


/-- The fixed-unit-window weighted estimate of Claim 12.2, allowing the
first matrix to have its deterministic Rademacher diagonal. -/
theorem finExpectation_shiftMoment_indicator_le_sourceScale_general
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A B : I → I → ℝ) (target q : ℝ)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i)
    (hAbound : ∀ i j, |A i j| ≤ 1)
    (hBbound : ∀ i j, |B i j| ≤ 1)
    (hBnonneg : ∀ xi : I → Bool,
      0 ≤ ∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi j))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |∑ i, beta i * Fourier.rademacherSign (xi i) - target| ≤ 1 then
        ((1 / 8 : ℝ) *
          (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))) ^ 2 +
        ((Fintype.card I : ℝ) / 16) *
          (∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))
      else 0) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
  let N : ℝ := Fintype.card I
  let L : (I → Bool) → ℝ := fun xi ↦
    ∑ i, beta i * Fourier.rademacherSign (xi i)
  let QA : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  let QB : (I → Bool) → ℝ := fun xi ↦
    ∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
      Fourier.rademacherSign (xi j)
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hNsqrt : N * Real.sqrt N = N ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      N * N ^ (1 / 2 : ℝ) = N ^ (1 : ℝ) * N ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hNpos]
      _ = N ^ (3 / 2 : ℝ) := by congr 1 <;> ring
  have htwo :=
    finExpectation_rademacherQuadratic_sq_indicator_le_sourceScale_general
      beta A target q hbeta hA hAbound hq hq1 hmass hqmass
  have hone := finExpectation_rademacherQuadratic_indicator_le_sourceScale
    beta B target q hbeta hBbound hBnonneg hq hq1 hmass hqmass
  have honeScaled :
      Fourier.finExpectation (I → Bool) (fun xi ↦
        (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) ≤
        3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
    rw [finExpectation_const_mul_real]
    calc
      (N / 16) * Fourier.finExpectation (I → Bool) (fun xi ↦
          if |L xi - target| ≤ 1 then QB xi else 0) ≤
        (N / 16) *
          (48 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [L, QB, N] using hone
        · positivity
      _ = 3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
        rw [show (N / 16) *
          (48 * (q / 32) ^ (-(3 : ℝ) / 2) * Real.sqrt N) =
            3 * (q / 32) ^ (-(3 : ℝ) / 2) *
              (N * Real.sqrt N) by ring, hNsqrt]
  have hsplit : (fun xi : I → Bool ↦
      if |L xi - target| ≤ 1 then
        ((1 / 8 : ℝ) * QA xi) ^ 2 + (N / 16) * QB xi else 0) =
      (fun xi ↦
        (if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) +
          (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) := by
    funext xi
    by_cases hx : |L xi - target| ≤ 1 <;> simp [hx]
  change Fourier.finExpectation (I → Bool) (fun xi ↦
      if |L xi - target| ≤ 1 then
        ((1 / 8 : ℝ) * QA xi) ^ 2 + (N / 16) * QB xi else 0) ≤ _
  rw [hsplit, Erdos88.QuadraticCancellation.finExpectation_add_real]
  calc
    Fourier.finExpectation (I → Bool) (fun xi ↦
        if |L xi - target| ≤ 1 then ((1 / 8 : ℝ) * QA xi) ^ 2 else 0) +
      Fourier.finExpectation (I → Bool) (fun xi ↦
        (N / 16) * (if |L xi - target| ≤ 1 then QB xi else 0)) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2)) *
          N ^ (3 / 2 : ℝ) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2) * N ^ (3 / 2 : ℝ) := by
      exact add_le_add (by simpa only [L, QA, N] using htwo) honeScaled
    _ = ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
      dsimp only [N]
      ring

/-- Claim 12.2 on one fixed window of width `2 * scale`. -/
theorem finExpectation_shiftMoment_fixedWindow_le_sourceScale
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (beta : I → ℝ) (A B : I → I → ℝ)
    (center scale q : ℝ) (hscale : 0 < scale)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hA : ∀ i j, A i j = A j i)
    (hAbound : ∀ i j, |A i j| ≤ 1)
    (hBbound : ∀ i j, |B i j| ≤ 1)
    (hBnonneg : ∀ xi : I → Bool,
      0 ≤ ∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
        Fourier.rademacherSign (xi j))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (Fintype.card I : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (I → Bool) (fun xi ↦
      if |scale * (∑ i, beta i * Fourier.rademacherSign (xi i)) - center| ≤
          scale then
        ((1 / 8 : ℝ) *
          (∑ i, ∑ j, A i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))) ^ 2 +
        ((Fintype.card I : ℝ) / 16) *
          (∑ i, ∑ j, B i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j))
      else 0) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) *
          (Fintype.card I : ℝ) ^ (3 / 2 : ℝ) := by
  have hevent (xi : I → Bool) :
      |∑ i, beta i * Fourier.rademacherSign (xi i) - center / scale| ≤ 1 ↔
        |scale * (∑ i, beta i * Fourier.rademacherSign (xi i)) - center| ≤
          scale := by
    let z : ℝ := ∑ i, beta i * Fourier.rademacherSign (xi i)
    have hid : scale * |z - center / scale| = |scale * z - center| := by
      calc
        scale * |z - center / scale| =
            |scale| * |z - center / scale| := by rw [abs_of_pos hscale]
        _ = |scale * (z - center / scale)| := (abs_mul _ _).symm
        _ = |scale * z - center| := by
          congr 1
          field_simp
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_left h hscale.le
      rw [hid, mul_one] at hm
      exact hm
    · intro h
      apply le_of_mul_le_mul_left _ hscale
      rw [hid, mul_one]
      exact h
  have hunit := finExpectation_shiftMoment_indicator_le_sourceScale_general
    beta A B (center / scale) q hbeta hA hAbound hBbound hBnonneg
      hq hq1 hmass hqmass
  simpa only [hevent] using hunit
end Erdos88.LinearLCDCancellation
