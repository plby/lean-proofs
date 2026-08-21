/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import Mathlib
import ErdosProblems.Erdos88.LinearLCDCancellation
import ErdosProblems.Erdos88.QuadraticCancellation
import ErdosProblems.Erdos88.QuadraticLemma82

/-!
# Erdős Problem 88: the unstructured frequency-band assembly

This file isolates the deterministic assembly in Section 9 of
Kwan--Sah--Sauermann--Sawhney.  The difficult probabilistic estimates are
fields of `FrequencyBandHypotheses`; in particular, this file does not add
them as axioms.  Starting from the exact output shapes of the linear
cancellation, regularized-LCD cancellation, quadratic slice cancellation,
and relative Esseen lemmas, it proves the overlap of the frequency bands,
integrates their common envelope, and obtains upper and lower bounded-window
estimates.
-/

open MeasureTheory Set
open scoped Interval

namespace Erdos88

noncomputable section

/-- The end of the Berry--Esseen/linear-cancellation band. -/
def linearBandEnd (n σ γ : ℝ) : ℝ := n ^ (2 * γ) / σ

/-- The end of the regularized-LCD band in the unstructured case. -/
def lcdBandEnd (n σ γ α : ℝ) : ℝ :=
  α * n ^ ((1 : ℝ) / 2 + γ / 8) / σ

/-- The beginning of the quadratic slice-cancellation band. -/
def sliceBandStart (n γ : ℝ) : ℝ := n ^ (-(1 : ℝ) + γ / 9)

/-- The numerical value fixed in KSSS Section 9. -/
def unstructuredGamma : ℝ := 1 / 10000

lemma unstructuredGamma_pos : 0 < unstructuredGamma := by
  norm_num [unstructuredGamma]

lemma unstructuredGamma_lt_quarter : unstructuredGamma < 1 / 4 := by
  norm_num [unstructuredGamma]

/-- The central-band integral has exponent strictly below `-3/2`. -/
lemma unstructuredGamma_integral_exponent :
    4 * unstructuredGamma - 2 < (-(3 : ℝ) / 2) := by
  norm_num [unstructuredGamma]

/-- The fixed radius used by the reverse relative Esseen inequality.
The cancellation cutoff `ν` depends only on the Ramsey constant, so this
radius is independent of the weight bound and of the bulk parameter. -/
def unstructuredWindowRadius (ν : ℝ) : ℝ := 40000 / ν

/-- Abstract outputs of KSSS Lemmas 7.1, 7.2, and 8.1 on a single graph.

`φX` and `φZ` are the characteristic functions of the target variable and
the matching Gaussian.  The Gaussian tail estimate is elementary once
`φZ` is unfolded, but it is kept explicit here so that the assembly is
independent of any particular probability-space representation.
-/
structure FrequencyBandHypotheses
    (φX φZ : ℝ → ℂ) (n σ γ α ν scaleUpper cLinear cTail : ℝ) : Prop where
  one_lt_n : 1 < n
  sigma_pos : 0 < σ
  gamma_pos : 0 < γ
  alpha_pos : 0 < α
  cutoff_pos : 0 < ν
  scaleUpper_pos : 0 < scaleUpper
  cLinear_nonneg : 0 ≤ cLinear
  cTail_nonneg : 0 ≤ cTail
  sigma_upper : σ ≤ scaleUpper * n ^ ((3 : ℝ) / 2)
  /-- The one scalar large-`n` inequality needed to overlap Lemmas 7.2 and 8.1. -/
  overlap_growth : scaleUpper / α ≤ n ^ (γ / 72)
  linear_le_lcd : linearBandEnd n σ γ ≤ lcdBandEnd n σ γ α
  lcd_le_cutoff : lcdBandEnd n σ γ α ≤ ν
  error_intervalIntegrable :
    IntervalIntegrable (fun t ↦ ‖φX t - φZ t‖) volume (-ν) ν
  /-- KSSS Lemma 7.1 after returning from normalized frequency `t` to `τ=t/σ`. -/
  linear_cancellation : ∀ t : ℝ,
    |t| ≤ linearBandEnd n σ γ →
      ‖φX t - φZ t‖ ≤ cLinear * σ * |t| / n.sqrt
  /-- KSSS Lemma 7.2 in the unstructured (`RLCD ≥ √n`) branch. -/
  lcd_cancellation : ∀ t : ℝ,
    linearBandEnd n σ γ ≤ |t| → |t| ≤ lcdBandEnd n σ γ α →
      ‖φX t‖ ≤ cTail * n ^ (-(5 : ℝ))
  /-- KSSS Lemma 8.1, after the usual conditioning/removal step. -/
  slice_cancellation : ∀ t : ℝ,
    sliceBandStart n γ ≤ |t| → |t| ≤ ν →
      ‖φX t‖ ≤ cTail * n ^ (-(5 : ℝ))
  /-- The matching Gaussian is already negligible outside the central band. -/
  gaussian_tail : ∀ t : ℝ,
    linearBandEnd n σ γ ≤ |t| → |t| ≤ ν →
      ‖φZ t‖ ≤ cTail * n ^ (-(5 : ℝ))

/-- The exponent identity behind the overlap of the LCD and slice bands. -/
lemma overlap_exponent_identity (γ : ℝ) :
    (-(1 : ℝ) + γ / 9) + (3 / 2 : ℝ) + γ / 72 =
      (1 / 2 : ℝ) + γ / 8 := by
  ring

/-- The large-`n` scalar inequality in `FrequencyBandHypotheses` really
implies that the slice band begins before the LCD band ends. -/
lemma sliceBandStart_le_lcdBandEnd
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail) :
    sliceBandStart n γ ≤ lcdBandEnd n σ γ α := by
  have hn : 0 < n := lt_trans (by norm_num) h.one_lt_n
  have hscale : scaleUpper ≤ α * n ^ (γ / 72) := by
    simpa [mul_comm] using (div_le_iff₀ h.alpha_pos).mp h.overlap_growth
  rw [sliceBandStart, lcdBandEnd]
  apply (le_div_iff₀ h.sigma_pos).2
  calc
    n ^ (-(1 : ℝ) + γ / 9) * σ ≤
        n ^ (-(1 : ℝ) + γ / 9) *
          (scaleUpper * n ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left h.sigma_upper (Real.rpow_nonneg hn.le _)
    _ = scaleUpper *
          (n ^ (-(1 : ℝ) + γ / 9) * n ^ ((3 : ℝ) / 2)) := by
      ring
    _ = scaleUpper * n ^ ((-(1 : ℝ) + γ / 9) + (3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hn]
    _ ≤ (α * n ^ (γ / 72)) *
          n ^ ((-(1 : ℝ) + γ / 9) + (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hn.le _)
    _ = α * (n ^ (γ / 72) *
          n ^ ((-(1 : ℝ) + γ / 9) + (3 / 2 : ℝ))) := by ring
    _ = α * n ^ ((γ / 72) +
          ((-(1 : ℝ) + γ / 9) + (3 / 2 : ℝ))) := by
      rw [← Real.rpow_add hn]
    _ = α * n ^ ((1 / 2 : ℝ) + γ / 8) := by
      congr 2
      ring

lemma linearBandEnd_pos
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail) :
    0 < linearBandEnd n σ γ := by
  exact div_pos (Real.rpow_pos_of_pos (lt_trans (by norm_num) h.one_lt_n) _) h.sigma_pos

lemma linearBandEnd_le_cutoff
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail) :
    linearBandEnd n σ γ ≤ ν :=
  h.linear_le_lcd.trans h.lcd_le_cutoff

/-- Once the numerical overlap is known, the LCD and quadratic estimates
give one common estimate everywhere outside the central band. -/
lemma tail_fourier_error_bound
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail)
    {t : ℝ} (hcentral : linearBandEnd n σ γ ≤ |t|) (hcutoff : |t| ≤ ν) :
    ‖φX t - φZ t‖ ≤ 2 * cTail * n ^ (-(5 : ℝ)) := by
  have hX : ‖φX t‖ ≤ cTail * n ^ (-(5 : ℝ)) := by
    by_cases hlcd : |t| ≤ lcdBandEnd n σ γ α
    · exact h.lcd_cancellation t hcentral hlcd
    · apply h.slice_cancellation t
      · exact (sliceBandStart_le_lcdBandEnd h).trans (le_of_not_ge hlcd)
      · exact hcutoff
  calc
    ‖φX t - φZ t‖ ≤ ‖φX t‖ + ‖φZ t‖ := norm_sub_le _ _
    _ ≤ cTail * n ^ (-(5 : ℝ)) + cTail * n ^ (-(5 : ℝ)) :=
      add_le_add hX (h.gaussian_tail t hcentral hcutoff)
    _ = 2 * cTail * n ^ (-(5 : ℝ)) := by ring

/-- The Fourier `L¹` error on the cancellation interval. -/
def fourierL1Error (φX φZ : ℝ → ℂ) (ν : ℝ) : ℝ :=
  ∫ t in -ν..ν, ‖φX t - φZ t‖

/-- The central band contributes its length times the endpoint value, while
the two outer bands contribute at most their total length times `2 n⁻⁵`.
This is the integrated estimate (4.41), before substituting the scale of
`linearBandEnd`. -/
lemma fourierL1Error_le
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail) :
    fourierL1Error φX φZ ν ≤
      2 * (cLinear * σ / n.sqrt) * (linearBandEnd n σ γ) ^ 2 +
        4 * ν * cTail * n ^ (-(5 : ℝ)) := by
  let e : ℝ → ℝ := fun t ↦ ‖φX t - φZ t‖
  let l : ℝ := linearBandEnd n σ γ
  have hl : 0 ≤ l := (linearBandEnd_pos h).le
  have hlν : l ≤ ν := linearBandEnd_le_cutoff h
  have hν : 0 ≤ ν := h.cutoff_pos.le
  have hn : 0 < n := lt_trans (by norm_num) h.one_lt_n
  have hsqrt : 0 < n.sqrt := Real.sqrt_pos.2 hn
  have hleft : IntervalIntegrable e volume (-ν) (-l) := by
    apply h.error_intervalIntegrable.mono_set
    rw [Set.uIcc_of_le (neg_le_neg hlν), Set.uIcc_of_le (by linarith : -ν ≤ ν)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hmiddle : IntervalIntegrable e volume (-l) l := by
    apply h.error_intervalIntegrable.mono_set
    rw [Set.uIcc_of_le (by linarith : -l ≤ l),
      Set.uIcc_of_le (by linarith : -ν ≤ ν)]
    exact Icc_subset_Icc (by linarith) hlν
  have hright : IntervalIntegrable e volume l ν := by
    apply h.error_intervalIntegrable.mono_set
    rw [Set.uIcc_of_le hlν, Set.uIcc_of_le (by linarith : -ν ≤ ν)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hleft_bound :
      (∫ t in -ν..-l, e t) ≤
        ∫ _t in -ν..-l, 2 * cTail * n ^ (-(5 : ℝ)) := by
    apply intervalIntegral.integral_mono_on (neg_le_neg hlν) hleft
      intervalIntegrable_const
    intro t ht
    have ht0 : t ≤ 0 := ht.2.trans (by linarith)
    apply tail_fourier_error_bound h
    · have hneg := neg_le_neg ht.2
      have hlt : l ≤ -t := by simpa only [neg_neg] using hneg
      simpa [l, abs_of_nonpos ht0] using hlt
    · have hneg := neg_le_neg ht.1
      have htnu : -t ≤ ν := by simpa only [neg_neg] using hneg
      simpa [abs_of_nonpos ht0] using htnu
  have hmiddle_bound :
      (∫ t in -l..l, e t) ≤
        ∫ _t in -l..l, cLinear * σ * l / n.sqrt := by
    apply intervalIntegral.integral_mono_on (by linarith) hmiddle
      intervalIntegrable_const
    intro t ht
    have habs : |t| ≤ l := (abs_le).2 ⟨ht.1, ht.2⟩
    calc
      e t ≤ cLinear * σ * |t| / n.sqrt := h.linear_cancellation t (by simpa [l] using habs)
      _ ≤ cLinear * σ * l / n.sqrt := by
        exact (div_le_div_iff_of_pos_right hsqrt).2
          (mul_le_mul_of_nonneg_left habs
            (mul_nonneg h.cLinear_nonneg h.sigma_pos.le))
  have hright_bound :
      (∫ t in l..ν, e t) ≤
        ∫ _t in l..ν, 2 * cTail * n ^ (-(5 : ℝ)) := by
    apply intervalIntegral.integral_mono_on hlν hright intervalIntegrable_const
    intro t ht
    have ht0 : 0 ≤ t := hl.trans ht.1
    apply tail_fourier_error_bound h
    · simpa [l, abs_of_nonneg ht0] using ht.1
    · simpa [abs_of_nonneg ht0] using ht.2
  have hsplit_left := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hsplit_all :=
    intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  have hpow : 0 ≤ n ^ (-(5 : ℝ)) := Real.rpow_nonneg hn.le _
  rw [fourierL1Error]
  calc
    (∫ t in -ν..ν, e t) =
        ((∫ t in -ν..-l, e t) + ∫ t in -l..l, e t) + ∫ t in l..ν, e t := by
      rw [hsplit_left, hsplit_all]
    _ ≤ ((∫ _t in -ν..-l, 2 * cTail * n ^ (-(5 : ℝ))) +
          ∫ _t in -l..l, cLinear * σ * l / n.sqrt) +
          ∫ _t in l..ν, 2 * cTail * n ^ (-(5 : ℝ)) := by
      gcongr
    _ ≤ 2 * (cLinear * σ / n.sqrt) * l ^ 2 +
        4 * ν * cTail * n ^ (-(5 : ℝ)) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hcσ : 0 ≤ cLinear * σ / n.sqrt :=
        div_nonneg (mul_nonneg h.cLinear_nonneg h.sigma_pos.le) hsqrt.le
      have htail : 0 ≤ cTail * n ^ (-(5 : ℝ)) :=
        mul_nonneg h.cTail_nonneg hpow
      rw [show cLinear * σ * l / n.sqrt = (cLinear * σ / n.sqrt) * l by ring]
      nlinarith
    _ = 2 * (cLinear * σ / n.sqrt) * (linearBandEnd n σ γ) ^ 2 +
        4 * ν * cTail * n ^ (-(5 : ℝ)) := by rfl

lemma centralBand_term_eq
    {n σ γ cLinear : ℝ} (hn : 0 < n) (hσ : 0 < σ) :
    2 * (cLinear * σ / n.sqrt) * (linearBandEnd n σ γ) ^ 2 =
      2 * cLinear * n ^ (4 * γ) / (n.sqrt * σ) := by
  rw [linearBandEnd]
  have hsqrt : n.sqrt ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hpow : (n ^ (2 * γ)) ^ 2 = n ^ (4 * γ) := by
    calc
      (n ^ (2 * γ)) ^ 2 = n ^ ((2 * γ) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hn.le (2 * γ) 2).symm
      _ = n ^ (4 * γ) := by
        apply congrArg (fun x : ℝ ↦ n ^ x)
        norm_num
        ring
  rw [div_pow, hpow]
  field_simp

lemma centralBand_term_le_scaled
    {n σ γ cLinear scaleLower : ℝ}
    (hn : 0 < n) (hσ : 0 < σ) (hc : 0 ≤ cLinear)
    (hscale : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ) :
    2 * (cLinear * σ / n.sqrt) * (linearBandEnd n σ γ) ^ 2 ≤
      (2 * cLinear / scaleLower) * n ^ (4 * γ - 2) := by
  rw [centralBand_term_eq hn hσ]
  have hsqrt : 0 < n.sqrt := Real.sqrt_pos.2 hn
  have hbase : 0 < scaleLower * n ^ ((3 : ℝ) / 2) :=
    mul_pos hscale (Real.rpow_pos_of_pos hn _)
  have hden : n.sqrt * (scaleLower * n ^ ((3 : ℝ) / 2)) ≤ n.sqrt * σ :=
    mul_le_mul_of_nonneg_left hσlower hsqrt.le
  have hnum : 0 ≤ 2 * cLinear * n ^ (4 * γ) := by positivity
  calc
    2 * cLinear * n ^ (4 * γ) / (n.sqrt * σ) ≤
        2 * cLinear * n ^ (4 * γ) /
          (n.sqrt * (scaleLower * n ^ ((3 : ℝ) / 2))) := by
      apply (div_le_div_iff₀ (mul_pos hsqrt hσ) (mul_pos hsqrt hbase)).2
      exact mul_le_mul_of_nonneg_left hden hnum
    _ = (2 * cLinear / scaleLower) * n ^ (4 * γ - 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_sub hn]
      have hadd : n ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 2) = n ^ (2 : ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      have hdeneq : n ^ ((1 : ℝ) / 2) *
          (scaleLower * n ^ ((3 : ℝ) / 2)) = scaleLower * n ^ (2 : ℝ) := by
        rw [mul_left_comm, hadd]
      rw [hdeneq]
      field_simp

/-- Substituting `σ ≳ n^(3/2)` into `fourierL1Error_le` gives the numerical
form used in the relative Esseen step. -/
lemma fourierL1Error_le_scaled
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail scaleLower : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail)
    (hscale : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ) :
    fourierL1Error φX φZ ν ≤
      (2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
        4 * ν * cTail * n ^ (-(5 : ℝ)) := by
  exact (fourierL1Error_le h).trans
    (add_le_add
      (centralBand_term_le_scaled (γ := γ)
        (lt_trans (show (0 : ℝ) < 1 by norm_num) h.one_lt_n)
        h.sigma_pos h.cLinear_nonneg
        hscale hσlower)
      (le_refl (4 * ν * cTail * n ^ (-(5 : ℝ)))))

/-- The Fourier error on the interval appearing in Esseen's inequality at
radius `r`. -/
def fourierErrorAtRadius (φX φZ : ℝ → ℂ) (r : ℝ) : ℝ :=
  ∫ t in -(2 / r)..(2 / r), ‖φX t - φZ t‖

/-- Restricting the frequency interval can only decrease the integral of
the nonnegative Fourier error. -/
lemma fourierErrorAtRadius_le_full
    {φX φZ : ℝ → ℂ} {ν r : ℝ}
    (hν : 0 ≤ ν) (hr : 0 < r) (hcut : 2 / r ≤ ν)
    (hint : IntervalIntegrable (fun t ↦ ‖φX t - φZ t‖) volume (-ν) ν) :
    fourierErrorAtRadius φX φZ r ≤ fourierL1Error φX φZ ν := by
  rw [fourierErrorAtRadius, fourierL1Error]
  apply intervalIntegral.integral_mono_interval
  · exact neg_le_neg hcut
  · linarith [div_pos (show (0 : ℝ) < 2 by norm_num) hr]
  · exact hcut
  · filter_upwards [] with t
    exact norm_nonneg _
  · exact hint

/-- Exact abstract inputs from KSSS Lemmas 6.1 and 6.3, together with the
elementary Gaussian small-ball bounds to which they are applied.

`smallBallX r x` denotes `P(|X-x| ≤ r)`.  `Bulk x` is the desired central
range (in the application, `|x-EX| ≤ A n^(3/2)`).  All probability and
density facts are parameters of this structure, not declarations of this
development.
-/
structure RelativeEsseenHypotheses
    (φX φZ : ℝ → ℂ) (smallBallX smallBallZ : ℝ → ℝ → ℝ)
    (concentrationZ : ℝ → ℝ) (Bulk : ℝ → Prop)
    (σ ν cEsseen gaussianUpper gaussianLower R : ℝ) : Prop where
  sigma_pos : 0 < σ
  cutoff_pos : 0 < ν
  cEsseen_nonneg : 0 ≤ cEsseen
  gaussianUpper_nonneg : 0 ≤ gaussianUpper
  gaussianLower_pos : 0 < gaussianLower
  R_pos : 0 < R
  /-- KSSS Lemma 6.1, with its exact radius-dependent Fourier interval. -/
  relative_upper : ∀ (r : ℝ), 0 < r → ∀ x : ℝ,
    smallBallX r x ≤ cEsseen *
      (smallBallZ r x + r * fourierErrorAtRadius φX φZ r)
  gaussian_upper : ∀ (r : ℝ), 0 < r → ∀ x : ℝ,
    smallBallZ r x ≤ gaussianUpper * r / σ
  concentration_upper : ∀ (r : ℝ), 0 < r →
    concentrationZ r ≤ gaussianUpper * r / σ
  /-- The Gaussian density lower bound in the prescribed bulk. -/
  gaussian_lower : ∀ x : ℝ, Bulk x →
    gaussianLower * (2 / ν) / σ ≤ smallBallZ (2 / ν) x
  /-- KSSS Lemma 6.3 with density-ratio constant `K=2`; hence the output
  radius is `2 * 10^4 * (2/ν) = 40000/ν`. -/
  relative_lower : ∀ x : ℝ, Bulk x →
    (1 / 8 : ℝ) * smallBallZ (2 / ν) x -
        cEsseen * ((concentrationZ (2 / ν)) / R +
          (2 / ν) * fourierErrorAtRadius φX φZ (2 / ν)) ≤
      smallBallX (unstructuredWindowRadius ν) x

/-- `B=40000/ν` is positive and its Esseen frequency interval lies inside
the cancellation interval `[-ν,ν]`. -/
lemma windowRadius_pos_and_cutoff {ν : ℝ} (hν : 0 < ν) :
    0 < unstructuredWindowRadius ν ∧
      2 / unstructuredWindowRadius ν ≤ ν := by
  constructor
  · exact div_pos (by norm_num) hν
  · rw [unstructuredWindowRadius]
    calc
      2 / (40000 / ν) = ν / 20000 := by
        field_simp [hν.ne']
        norm_num
      _ ≤ ν := by
        apply (div_le_iff₀ (show (0 : ℝ) < 20000 by norm_num)).2
        nlinarith

/-- The complete unstructured relative-Esseen assembly.  The scalar
`ηFourier` records how small the already-proved integrated Fourier bound is
relative to `1/σ`; in the graph application this follows for all sufficiently
large `n` from `fourierL1Error_le_scaled` and `γ=10⁻⁴`.

The output radius is definitionally `40000/ν`, and therefore depends only on
the quadratic-cancellation cutoff (hence only on the Ramsey constant), not on
the weight bound or on the bulk range.
-/
theorem unstructured_bounded_window
    {φX φZ : ℝ → ℂ} {smallBallX smallBallZ : ℝ → ℝ → ℝ}
    {concentrationZ : ℝ → ℝ} {Bulk : ℝ → Prop}
    {σ ν cEsseen gaussianUpper gaussianLower R ηFourier : ℝ}
    (hint : IntervalIntegrable (fun t ↦ ‖φX t - φZ t‖) volume (-ν) ν)
    (hFourier : fourierL1Error φX φZ ν ≤ ηFourier / σ)
    (hE : RelativeEsseenHypotheses φX φZ smallBallX smallBallZ
      concentrationZ Bulk σ ν cEsseen gaussianUpper gaussianLower R)
    (hmargin : 0 < gaussianLower / 8 -
      cEsseen * (gaussianUpper / R + ηFourier)) :
    (∀ x : ℝ,
      smallBallX (unstructuredWindowRadius ν) x ≤
        (cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / σ) ∧
    (∀ x : ℝ, Bulk x →
      ((2 / ν) * (gaussianLower / 8 -
        cEsseen * (gaussianUpper / R + ηFourier))) / σ ≤
        smallBallX (unstructuredWindowRadius ν) x) := by
  have hB := windowRadius_pos_and_cutoff hE.cutoff_pos
  have hε : 0 < 2 / ν := div_pos (by norm_num) hE.cutoff_pos
  have hrestrictedB :
      fourierErrorAtRadius φX φZ (unstructuredWindowRadius ν) ≤
        ηFourier / σ :=
    (fourierErrorAtRadius_le_full hE.cutoff_pos.le hB.1 hB.2 hint).trans hFourier
  have hrestrictedε :
      fourierErrorAtRadius φX φZ (2 / ν) ≤ ηFourier / σ := by
    have hcutε : 2 / (2 / ν) ≤ ν := by
      calc
        2 / (2 / ν) = ν := by field_simp [hE.cutoff_pos.ne']
        _ ≤ ν := le_rfl
    exact (fourierErrorAtRadius_le_full hE.cutoff_pos.le hε hcutε hint).trans hFourier
  constructor
  · intro x
    calc
      smallBallX (unstructuredWindowRadius ν) x ≤
          cEsseen * (smallBallZ (unstructuredWindowRadius ν) x +
            unstructuredWindowRadius ν *
              fourierErrorAtRadius φX φZ (unstructuredWindowRadius ν)) :=
        hE.relative_upper _ hB.1 x
      _ ≤ cEsseen *
          (gaussianUpper * unstructuredWindowRadius ν / σ +
            unstructuredWindowRadius ν * (ηFourier / σ)) := by
        apply mul_le_mul_of_nonneg_left _ hE.cEsseen_nonneg
        exact add_le_add (hE.gaussian_upper _ hB.1 x)
          (mul_le_mul_of_nonneg_left hrestrictedB hB.1.le)
      _ = (cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / σ := by ring
  · intro x hx
    have hZ := hE.gaussian_lower x hx
    have hconc := hE.concentration_upper (2 / ν) hε
    have hconcDiv : concentrationZ (2 / ν) / R ≤
        (gaussianUpper * (2 / ν) / σ) / R :=
      (div_le_div_iff_of_pos_right hE.R_pos).2 hconc
    have herrMul : (2 / ν) * fourierErrorAtRadius φX φZ (2 / ν) ≤
        (2 / ν) * (ηFourier / σ) :=
      mul_le_mul_of_nonneg_left hrestrictedε hε.le
    have hnuisance : concentrationZ (2 / ν) / R +
          (2 / ν) * fourierErrorAtRadius φX φZ (2 / ν) ≤
        (gaussianUpper * (2 / ν) / σ) / R +
          (2 / ν) * (ηFourier / σ) :=
      add_le_add hconcDiv herrMul
    have hpositive : (1 / 8 : ℝ) * (gaussianLower * (2 / ν) / σ) ≤
        (1 / 8 : ℝ) * smallBallZ (2 / ν) x :=
      mul_le_mul_of_nonneg_left hZ (by norm_num)
    have hnuisanceMul : cEsseen *
          (concentrationZ (2 / ν) / R +
            (2 / ν) * fourierErrorAtRadius φX φZ (2 / ν)) ≤
        cEsseen * ((gaussianUpper * (2 / ν) / σ) / R +
          (2 / ν) * (ηFourier / σ)) :=
      mul_le_mul_of_nonneg_left hnuisance hE.cEsseen_nonneg
    calc
      ((2 / ν) * (gaussianLower / 8 -
          cEsseen * (gaussianUpper / R + ηFourier))) / σ =
          (1 / 8 : ℝ) * (gaussianLower * (2 / ν) / σ) -
            cEsseen * ((gaussianUpper * (2 / ν) / σ) / R +
              (2 / ν) * (ηFourier / σ)) := by ring
      _ ≤ (1 / 8 : ℝ) * smallBallZ (2 / ν) x -
          cEsseen * (concentrationZ (2 / ν) / R +
            (2 / ν) * fourierErrorAtRadius φX φZ (2 / ν)) := by
        linarith
      _ ≤ smallBallX (unstructuredWindowRadius ν) x := hE.relative_lower x hx

/-- A convenient scalar criterion for turning the integrated band estimate
into the `η/σ` input of `unstructured_bounded_window`. -/
lemma fourierL1Error_le_div_of_scaled_bound
    {φX φZ : ℝ → ℂ} {n σ γ α ν scaleUpper cLinear cTail scaleLower η : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail)
    (hscale : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ)
    (habsorb : σ * ((2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
      4 * ν * cTail * n ^ (-(5 : ℝ))) ≤ η) :
    fourierL1Error φX φZ ν ≤ η / σ := by
  apply (le_div_iff₀ h.sigma_pos).2
  calc
    fourierL1Error φX φZ ν * σ ≤
        ((2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
          4 * ν * cTail * n ^ (-(5 : ℝ))) * σ :=
      mul_le_mul_of_nonneg_right (fourierL1Error_le_scaled h hscale hσlower)
        h.sigma_pos.le
    _ = σ * ((2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
          4 * ν * cTail * n ^ (-(5 : ℝ))) := by ring
    _ ≤ η := habsorb

/-- The frequency-band hypotheses and one explicit large-`n` absorption
inequality imply the bounded-window theorem directly. -/
theorem unstructured_bounded_window_of_bands
    {φX φZ : ℝ → ℂ} {smallBallX smallBallZ : ℝ → ℝ → ℝ}
    {concentrationZ : ℝ → ℝ} {Bulk : ℝ → Prop}
    {n σ γ α ν scaleUpper cLinear cTail scaleLower : ℝ}
    {cEsseen gaussianUpper gaussianLower R ηFourier : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail)
    (hscale : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ)
    (habsorb : σ * ((2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
      4 * ν * cTail * n ^ (-(5 : ℝ))) ≤ ηFourier)
    (hE : RelativeEsseenHypotheses φX φZ smallBallX smallBallZ
      concentrationZ Bulk σ ν cEsseen gaussianUpper gaussianLower R)
    (hmargin : 0 < gaussianLower / 8 -
      cEsseen * (gaussianUpper / R + ηFourier)) :
    (∀ x : ℝ,
      smallBallX (unstructuredWindowRadius ν) x ≤
        (cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / σ) ∧
    (∀ x : ℝ, Bulk x →
      ((2 / ν) * (gaussianLower / 8 -
        cEsseen * (gaussianUpper / R + ηFourier))) / σ ≤
        smallBallX (unstructuredWindowRadius ν) x) :=
  unstructured_bounded_window h.error_intervalIntegrable
    (fourierL1Error_le_div_of_scaled_bound h hscale hσlower habsorb) hE hmargin

lemma one_div_sigma_le_rpow
    {n σ scaleLower : ℝ} (hn : 0 < n) (hσ : 0 < σ)
    (hscale : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ) :
    1 / σ ≤ (1 / scaleLower) * n ^ (-(3 : ℝ) / 2) := by
  calc
    1 / σ ≤ 1 / (scaleLower * n ^ ((3 : ℝ) / 2)) :=
      one_div_le_one_div_of_le
        (mul_pos hscale (Real.rpow_pos_of_pos hn _)) hσlower
    _ = (1 / scaleLower) * n ^ (-(3 : ℝ) / 2) := by
      rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring,
        Real.rpow_neg hn.le]
      field_simp

lemma rpow_le_one_div_sigma
    {n σ scaleUpper : ℝ} (hn : 0 < n) (hσ : 0 < σ)
    (hscale : 0 < scaleUpper)
    (hσupper : σ ≤ scaleUpper * n ^ ((3 : ℝ) / 2)) :
    (1 / scaleUpper) * n ^ (-(3 : ℝ) / 2) ≤ 1 / σ := by
  calc
    (1 / scaleUpper) * n ^ (-(3 : ℝ) / 2) =
        1 / (scaleUpper * n ^ ((3 : ℝ) / 2)) := by
      rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring,
        Real.rpow_neg hn.le]
      field_simp
    _ ≤ 1 / σ := one_div_le_one_div_of_le hσ hσupper

/-- The same result in the conventional `n⁻³ᐟ²` normalization.  Its upper
constant may depend on the weight bound through the supplied analytic
constants, and its lower constant may depend on the bulk range, while the
window radius remains `40000/ν` and depends on neither. -/
theorem unstructured_bounded_window_n_scale
    {φX φZ : ℝ → ℂ} {smallBallX smallBallZ : ℝ → ℝ → ℝ}
    {concentrationZ : ℝ → ℝ} {Bulk : ℝ → Prop}
    {n σ γ α ν scaleUpper cLinear cTail scaleLower : ℝ}
    {cEsseen gaussianUpper gaussianLower R ηFourier : ℝ}
    (h : FrequencyBandHypotheses φX φZ n σ γ α ν scaleUpper cLinear cTail)
    (hscaleLower : 0 < scaleLower)
    (hσlower : scaleLower * n ^ ((3 : ℝ) / 2) ≤ σ)
    (habsorb : σ * ((2 * cLinear / scaleLower) * n ^ (4 * γ - 2) +
      4 * ν * cTail * n ^ (-(5 : ℝ))) ≤ ηFourier)
    (hE : RelativeEsseenHypotheses φX φZ smallBallX smallBallZ
      concentrationZ Bulk σ ν cEsseen gaussianUpper gaussianLower R)
    (hη : 0 ≤ ηFourier)
    (hmargin : 0 < gaussianLower / 8 -
      cEsseen * (gaussianUpper / R + ηFourier)) :
    (∀ x : ℝ,
      smallBallX (unstructuredWindowRadius ν) x ≤
        ((cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / scaleLower) *
            n ^ (-(3 : ℝ) / 2)) ∧
    (∀ x : ℝ, Bulk x →
      (((2 / ν) * (gaussianLower / 8 -
        cEsseen * (gaussianUpper / R + ηFourier))) / scaleUpper) *
          n ^ (-(3 : ℝ) / 2) ≤
        smallBallX (unstructuredWindowRadius ν) x) := by
  have hresult := unstructured_bounded_window_of_bands h hscaleLower hσlower
    habsorb hE hmargin
  have hn : 0 < n := lt_trans (by norm_num) h.one_lt_n
  have hinvUpper := one_div_sigma_le_rpow hn h.sigma_pos hscaleLower hσlower
  have hinvLower := rpow_le_one_div_sigma hn h.sigma_pos h.scaleUpper_pos h.sigma_upper
  have hBpos := (windowRadius_pos_and_cutoff h.cutoff_pos).1
  have hUpperConst : 0 ≤ cEsseen *
      (gaussianUpper * unstructuredWindowRadius ν +
        unstructuredWindowRadius ν * ηFourier) := by
    exact mul_nonneg hE.cEsseen_nonneg
      (add_nonneg
        (mul_nonneg hE.gaussianUpper_nonneg hBpos.le)
        (mul_nonneg hBpos.le hη))
  have hLowerConst : 0 ≤ (2 / ν) * (gaussianLower / 8 -
      cEsseen * (gaussianUpper / R + ηFourier)) :=
    (mul_pos (div_pos (by norm_num) h.cutoff_pos) hmargin).le
  constructor
  · intro x
    refine (hresult.1 x).trans ?_
    calc
      (cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / σ =
          cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
            unstructuredWindowRadius ν * ηFourier) * (1 / σ) := by ring
      _ ≤
          cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
            unstructuredWindowRadius ν * ηFourier) *
              ((1 / scaleLower) * n ^ (-(3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hinvUpper hUpperConst
      _ = ((cEsseen * (gaussianUpper * unstructuredWindowRadius ν +
          unstructuredWindowRadius ν * ηFourier)) / scaleLower) *
            n ^ (-(3 : ℝ) / 2) := by ring
  · intro x hx
    refine le_trans ?_ (hresult.2 x hx)
    calc
      (((2 / ν) * (gaussianLower / 8 -
          cEsseen * (gaussianUpper / R + ηFourier))) / scaleUpper) *
            n ^ (-(3 : ℝ) / 2) =
          (2 / ν) * (gaussianLower / 8 -
            cEsseen * (gaussianUpper / R + ηFourier)) *
              ((1 / scaleUpper) * n ^ (-(3 : ℝ) / 2)) := by ring
      _ ≤ (2 / ν) * (gaussianLower / 8 -
          cEsseen * (gaussianUpper / R + ηFourier)) * (1 / σ) :=
        mul_le_mul_of_nonneg_left hinvLower hLowerConst
      _ = ((2 / ν) * (gaussianLower / 8 -
          cEsseen * (gaussianUpper / R + ηFourier))) / σ := by ring

open LinearLCDCancellation GraphQuadratic

/-- Exact Section 9 band supplied by Lemma 7.2 in the additively
unstructured branch. -/
def KSSSLemma72UnstructuredBand : Prop :=
  ∀ C H gamma : ℝ, 0 < C → 0 ≤ H → 0 < gamma → gamma < 1 / 4 →
    let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
    ∃ alpha cTail : ℝ, 0 < alpha ∧ 0 ≤ cTail ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD L gamma
              (GraphQuadratic.graphEffectiveLinear G c) →
          ∀ tau : ℝ,
            linearBandEnd n (graphPerturbedSigma G e₀ c) gamma ≤ |tau| →
            |tau| ≤ lcdBandEnd n (graphPerturbedSigma G e₀ c) gamma alpha →
            ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c tau‖ ≤
              cTail * (n : ℝ) ^ (-(5 : ℝ))

theorem ksssLemma72_unstructuredBand : KSSSLemma72UnstructuredBand := by
  intro C H gamma hC hH hgamma hgammaUpper
  dsimp only
  obtain ⟨alpha, cTail, halpha, hcTail, hraw⟩ :=
    LinearLCDCancellation.ksssLemma72_raw_unstructured
      C H gamma hC hH hgamma hgammaUpper
  refine ⟨alpha, cTail, halpha, hcTail, ?_⟩
  filter_upwards [hraw] with n hrawN
  intro G e₀ c hG hc hlcd tau htLower htUpper
  apply hrawN G e₀ c hG hc hlcd tau
  · change BooleanSlices.scale n (2 * gamma) /
      graphPerturbedSigma G e₀ c ≤ |tau| at htLower
    exact htLower
  · change |tau| ≤ alpha * BooleanSlices.scale n
      (1 / 2 + gamma / 8) / graphPerturbedSigma G e₀ c at htUpper
    exact htUpper

end

end Erdos88
