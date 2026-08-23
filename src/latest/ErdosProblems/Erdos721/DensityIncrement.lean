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

import ErdosProblems.Erdos721.RelativeAlmostPeriodicity
import ErdosProblems.Erdos721.AlmostPeriodicity

/-!
# Cyclic smoothing and density increments

This file records the exact finite identities which turn the complex Fourier
smoothing output into a relative-density statement on a translate of a Bohr
set.  It also supplies the finite triangle inequality needed to pass from a
uniform smoothing estimate to a correlation estimate over an arbitrary test
set.
-/

namespace Erdos721

open Finset
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicDensityIncrement

variable {N : ℕ} [NeZero N]

open CyclicBohr CyclicFourier CyclicSpectralSmoothing

/-- The complex and real finite-set probability weights agree after the
canonical embedding of the reals into the complexes. -/
lemma probabilityWeight_eq_ofReal_uniformWeight
    (S : Finset (ZMod N)) (x : ZMod N) :
    probabilityWeight S x = (CyclicBohr.uniformWeight S x : ℂ) := by
  by_cases hx : x ∈ S
  · simp [probabilityWeight, CyclicBohr.uniformWeight, hx]
  · simp [probabilityWeight, CyclicBohr.uniformWeight, hx]

/-- Complex convolution of an indicator with a finite probability weight is
the relative cardinality of the corresponding reflected translate. -/
lemma convolution_indicator_probabilityWeight
    (A S : Finset (ZMod N)) (hS : S.Nonempty) (x : ZMod N) :
    convolution (indicator A) (probabilityWeight S) x =
      (((CyclicBohr.translatedSlice A S x).card / (S.card : ℝ)) : ℂ) := by
  let T := CyclicBohr.translatedSlice A S x
  have hpoint (y : ZMod N) :
      indicator A y * probabilityWeight S (x - y) =
        if y ∈ T then (N : ℂ) / S.card else 0 := by
    by_cases hyA : y ∈ A <;> by_cases hyS : x - y ∈ S <;>
      simp [indicator, probabilityWeight, T, CyclicBohr.translatedSlice, hyA, hyS]
  have hsum :
      ∑ y : ZMod N, indicator A y * probabilityWeight S (x - y) =
        T.card * ((N : ℂ) / S.card) := by
    simp_rw [hpoint]
    rw [← Finset.sum_filter]
    simp
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  unfold CyclicFourier.convolution CyclicFourier.average
  rw [hsum]
  dsimp only [T]
  push_cast
  field_simp

/-- The same identity with the probability weight in the first convolution
slot. -/
lemma probabilityWeight_convolution_indicator
    (A S : Finset (ZMod N)) (hS : S.Nonempty) (x : ZMod N) :
    convolution (probabilityWeight S) (indicator A) x =
      (((CyclicBohr.translatedSlice A S x).card / (S.card : ℝ)) : ℂ) := by
  rw [convolution_comm]
  exact convolution_indicator_probabilityWeight A S hS x

/-- A lower bound on a smoothed indicator is literally a relative-density
lower bound on the corresponding translated slice. -/
theorem density_increment_of_norm_probabilityWeight_convolution_indicator
    (A S : Finset (ZMod N)) (hS : S.Nonempty) (x : ZMod N)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hlarge : beta ≤ ‖convolution (probabilityWeight S) (indicator A) x‖) :
    beta ≤ (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) := by
  have hden : ‖(((S.card : ℝ) : ℂ))‖ = (S.card : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity
  rw [probabilityWeight_convolution_indicator A S hS x,
    norm_div, Complex.norm_natCast, hden] at hlarge
  exact hlarge

/-- APAP's real discrete convolution has the same translated-slice
interpretation.  Unlike the cyclic-average formulation above, the factor
`N` is already absorbed into `μ S`. -/
lemma indicator_ddconv_mu_apply_eq_translatedSlice
    (A S : Finset (ZMod N)) (hS : S.Nonempty) (x : ZMod N) :
    (𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] S) x =
      (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) := by
  let T := CyclicBohr.translatedSlice A S x
  have hpoint (y : ZMod N) :
      𝟭_[(A : Set (ZMod N)), ℝ] y * μ_[ℝ] S (x - y) =
        if y ∈ T then (S.card : ℝ)⁻¹ else 0 := by
    by_cases hyA : y ∈ A <;> by_cases hyS : x - y ∈ S <;>
      simp [mu_apply, T, CyclicBohr.translatedSlice, hyA, hyS]
  rw [ddconv_eq_sum_sub']
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  dsimp only [T]
  field_simp
  simp

/-- A lower bound for the discrete `L∞` norm is attained at a translate, and
therefore gives a genuinely denser translated slice. -/
theorem exists_translatedSlice_of_dLinfty_increment
    (A S : Finset (ZMod N)) (hS : S.Nonempty) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hlarge : beta ≤ ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] S‖_[∞]) :
    ∃ x : ZMod N,
      beta ≤ (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) := by
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm,
    ← Finset.sup'_univ_eq_ciSup, Finset.le_sup'_iff] at hlarge
  obtain ⟨x, _hx, hx⟩ := hlarge
  refine ⟨x, ?_⟩
  rw [indicator_ddconv_mu_apply_eq_translatedSlice A S hS x] at hx
  rwa [Real.norm_of_nonneg (by positivity)] at hx

/-- The translated slice is contained in the original set. -/
lemma translatedSlice_subset_left (A S : Finset (ZMod N)) (x : ZMod N) :
    CyclicBohr.translatedSlice A S x ⊆ A := by
  intro y hy
  rw [CyclicBohr.translatedSlice, Finset.mem_filter] at hy
  exact hy.1

/-- The translate-reflection of a slice, written as a subset of its Bohr
carrier.  This is the set passed to the next density-increment stage. -/
def normalizedSlice (A S : Finset (ZMod N)) (x : ZMod N) : Finset (ZMod N) :=
  S.filter fun z ↦ x - z ∈ A

lemma normalizedSlice_subset_right (A S : Finset (ZMod N)) (x : ZMod N) :
    normalizedSlice A S x ⊆ S := by
  intro z hz
  exact (Finset.mem_filter.1 hz).1

/-- Reflection in `x` is a bijection between the two descriptions of a
translated slice. -/
lemma card_normalizedSlice_eq_card_translatedSlice
    (A S : Finset (ZMod N)) (x : ZMod N) :
    (normalizedSlice A S x).card =
      (CyclicBohr.translatedSlice A S x).card := by
  have himage :
      normalizedSlice A S x =
        (CyclicBohr.translatedSlice A S x).image (fun y ↦ x - y) := by
    ext z
    simp only [normalizedSlice, CyclicBohr.translatedSlice, Finset.mem_filter,
      Finset.mem_image]
    constructor
    · rintro ⟨hzS, hzxA⟩
      refine ⟨x - z, ⟨hzxA, ?_⟩, ?_⟩ <;> simp [hzS]
    · rintro ⟨y, ⟨hyA, hyS⟩, rfl⟩
      simp [hyS, hyA]
  rw [himage, Finset.card_image_iff.mpr]
  intro a _ha b _hb hab
  simpa using hab

/-- Translation and reflection preserve the absence of nonconstant
three-term arithmetic progressions. -/
lemma threeAPFree_normalizedSlice
    (A S : Finset (ZMod N)) (x : ZMod N)
    (hA : ThreeAPFree (A : Set (ZMod N))) :
    ThreeAPFree (normalizedSlice A S x : Set (ZMod N)) := by
  intro a ha b hb c hc habc
  have haA : x - a ∈ A := (Finset.mem_filter.1 ha).2
  have hbA : x - b ∈ A := (Finset.mem_filter.1 hb).2
  have hcA : x - c ∈ A := (Finset.mem_filter.1 hc).2
  have hsum : (x - a) + (x - c) = (x - b) + (x - b) := by
    calc
      (x - a) + (x - c) = (x + x) - (a + c) := by abel
      _ = (x + x) - (b + b) := by rw [habc]
      _ = (x - b) + (x - b) := by abel
  have hsub := hA haA hbA hcA hsum
  simpa using hsub

/-! ## Conversion of the boosted convolution to a tested correlation -/

/-- Evaluating the triple convolution with the negative test-set indicator at
zero is the sum of the ordinary convolution over the test set. -/
lemma triple_indicator_neg_apply_zero_eq_sum
    (A₁ A₂ U : Finset (ZMod N)) :
    (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂) 0 =
      ∑ x ∈ U, (μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x := by
  have hsum :
      ∑ x ∈ U, (μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x =
        ((μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) ○ᵈ 𝟭_[U]) 0 := by
    simp [dddconv_indicator_one_eq_sum]
  rw [hsum, dddconv_indicator_one, ddconv_right_comm]

/-- The preceding identity remains exact after adjoining a smoothing
probability measure. -/
lemma mu_triple_indicator_neg_apply_zero_eq_sum
    (C A₁ A₂ U : Finset (ZMod N)) :
    (μ_[ℂ] C ∗ᵈ (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂)) 0 =
      ∑ x ∈ U, (μ_[ℂ] C ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x := by
  have hsum :
      ∑ x ∈ U, (μ_[ℂ] C ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x =
        ((μ_[ℂ] C ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) ○ᵈ 𝟭_[U]) 0 := by
    simp [dddconv_indicator_one_eq_sum]
  rw [hsum, dddconv_indicator_one]
  rw [ddconv_right_comm (μ_[ℂ] C ∗ᵈ μ_[ℂ] A₁)]
  simp only [ddconv_assoc]

/-- Complexification commutes with a finite probability weight. -/
lemma ofReal_comp_mu (A : Finset (ZMod N)) :
    Complex.ofReal ∘ μ_[ℝ] A = μ_[ℂ] A := by
  funext x
  exact map_mu Complex.ofRealHom A x

/-- Complexification commutes with a convolution of two finite probability
weights. -/
lemma complex_mu_ddconv_mu_apply (A B : Finset (ZMod N)) (x : ZMod N) :
    (μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x =
      (((μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x : ℝ) : ℂ) := by
  rw [← ofReal_comp_mu A, ← ofReal_comp_mu B,
    ← Complex.ofReal_comp_ddconv]
  rfl

/-- Complexification commutes with a convolution of three finite probability
weights. -/
lemma complex_mu_ddconv_mu_ddconv_mu_apply
    (C A B : Finset (ZMod N)) (x : ZMod N) :
    (μ_[ℂ] C ∗ᵈ μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x =
      (((μ_[ℝ] C ∗ᵈ μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x : ℝ) : ℂ) := by
  rw [← ofReal_comp_mu C, ← ofReal_comp_mu A, ← ofReal_comp_mu B,
    ← Complex.ofReal_comp_ddconv, ← Complex.ofReal_comp_ddconv]
  rfl

/-- Consequently, the norm of a tested complex convolution difference is the
absolute value of the corresponding real difference. -/
lemma norm_complex_tested_convolution_sub_eq_abs_real
    (C A B U : Finset (ZMod N)) :
    ‖(∑ x ∈ U, (μ_[ℂ] C ∗ᵈ μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x) -
        ∑ x ∈ U, (μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x‖ =
      |(∑ x ∈ U, (μ_[ℝ] C ∗ᵈ μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x) -
        ∑ x ∈ U, (μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x| := by
  simp only [complex_mu_ddconv_mu_ddconv_mu_apply,
    complex_mu_ddconv_mu_apply]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-- Summing pointwise complex errors over a finite test set costs at most its
cardinality times the uniform error. -/
lemma norm_sum_sub_sum_le_card_mul
    (P : Finset (ZMod N)) (F G : ZMod N → ℂ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (h : ∀ x ∈ P, ‖F x - G x‖ ≤ epsilon) :
    ‖(∑ x ∈ P, F x) - ∑ x ∈ P, G x‖ ≤ P.card * epsilon := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ x ∈ P, (F x - G x)‖ ≤ ∑ x ∈ P, ‖F x - G x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x ∈ P, epsilon := by
      exact Finset.sum_le_sum fun x hx ↦ h x hx
    _ = P.card * epsilon := by simp

/-- Uniform Bohr smoothing controls its correlation with every finite test
set. -/
theorem norm_testSet_sum_smoothing_sub_le
    (C P : Finset (ZMod N)) (hC : C.Nonempty) (F : ZMod N → ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmooth : ∀ x,
      ‖convolution (probabilityWeight C) F x - F x‖ ≤ epsilon) :
    ‖(∑ x ∈ P, convolution (probabilityWeight C) F x) -
        ∑ x ∈ P, F x‖ ≤ P.card * epsilon := by
  exact norm_sum_sub_sum_le_card_mul P _ _ hepsilon fun x _hx ↦ hsmooth x

/-- Correlation form of the localized Croot--Sisask--Chang package.  Besides
the pointwise estimate, it records in one theorem the estimate obtained after
testing against an arbitrary finite set `U`; this is the exact shape consumed
by the subsequent density-increment dichotomy. -/
theorem exists_local_bohr_correlation_smoothing
    (B : CyclicBohr.Set N) (A P Q U : Finset (ZMod N))
    {t delta alpha epsilon eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      (∀ x,
        ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N))) ∧
      ‖(∑ x ∈ U,
          CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x) -
          ∑ x ∈ U, (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        U.card *
          (2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho +
              2 * eta ^ k) *
                (Real.sqrt ((N : ℝ) / A.card) *
                  Real.sqrt ((P.card : ℝ) / N))) := by
  obtain ⟨T, C, hT, hCrank, hCsub, hsmooth⟩ :=
    CyclicRelativeAlmostPeriodicity.exists_local_bohr_smoothing
      B A P Q k halpha0 halphahalf hdelta hdeltat hAinner hAdense hregular
        hepsilon0 hepsilon1 hk hA hP hQ heta hrho
  refine ⟨T, C, hT, hCrank, hCsub, hsmooth, ?_⟩
  apply norm_testSet_sum_smoothing_sub_le C.carrier U C.carrier_nonempty _
  · positivity
  · exact hsmooth

/-- Tested-convolution form of local almost-periodicity.  This is the cyclic
Bohr replacement for the exact-subspace averaging lemma in the finite-field
density-increment proof. -/
theorem exists_local_bohr_tested_convolution
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    {t delta alpha epsilon eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      ‖(∑ x ∈ U, (μ_[ℂ] C.carrier ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x) -
          ∑ x ∈ U, (μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  obtain ⟨T, C, hT, hCrank, hCsub, hsmooth⟩ :=
    CyclicRelativeAlmostPeriodicity.exists_local_bohr_smoothing
      B A₁ (-U) A₂ k halpha0 halphahalf hdelta hdeltat hAinner hAdense
        hregular hepsilon0 hepsilon1 hk hA₁ (by simpa using hU) hA₂ heta hrho
  refine ⟨T, C, ?_, hCrank, hCsub, ?_⟩
  · simpa using hT
  · have hzero := hsmooth 0
    rw [Finset.coe_neg] at hzero
    rw [← congrFun
      (CyclicBoostedAlmostPeriodicity.mu_ddconv_eq_probabilityWeight_convolution
        C.carrier_nonempty (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂)) 0] at hzero
    rw [mu_triple_indicator_neg_apply_zero_eq_sum,
      triple_indicator_neg_apply_zero_eq_sum] at hzero
    simpa using hzero

/-- Real-valued form of `exists_local_bohr_tested_convolution`, matching the
correlation inequalities used by the unbalancing and sifting argument. -/
theorem exists_local_bohr_tested_convolution_real
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    {t delta alpha epsilon eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  obtain ⟨T, C, hT, hCrank, hCsub, hcomplex⟩ :=
    exists_local_bohr_tested_convolution B A₁ A₂ U k halpha0 halphahalf
      hdelta hdeltat hAinner hAdense hregular hepsilon0 hepsilon1 hk hA₁ hA₂
        hU heta hrho
  refine ⟨T, C, hT, hCrank, hCsub, ?_⟩
  rwa [norm_complex_tested_convolution_sub_eq_abs_real] at hcomplex

/-- Difference-convolution (correlation) form of local almost-periodicity.
This is obtained from the ordinary-convolution form by reflecting the second
set.  It is the form appearing in the density-increment argument. -/
theorem exists_local_bohr_tested_correlation_real
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    {t delta alpha epsilon eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  simpa [← conjneg_mu] using
    (exists_local_bohr_tested_convolution_real B A₁ (-A₂) U k halpha0
      halphahalf hdelta hdeltat hAinner hAdense hregular hepsilon0 hepsilon1
      hk hA₁ (by simpa using hA₂) hU heta hrho)

/-- Adaptive positive-radius version of the tested real convolution estimate.
It exposes the exact radius and inherited rank needed by the next iteration. -/
theorem exists_local_bohr_tested_convolution_real_adaptive
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  obtain ⟨T, C, hT, hCradius, hBrank, hCrank, hCsub, hsmooth⟩ :=
    CyclicRelativeAlmostPeriodicity.exists_local_bohr_smoothing_adaptive
      B A₁ (-U) A₂ rho k halpha0 halphahalf hdelta hdeltat hAinner
      hAdense hregular hepsilon0 hepsilon1 hk hA₁ (by simpa using hU) hA₂
      heta hrho
  refine ⟨T, C, ?_, hCradius, hBrank, hCrank, hCsub, ?_⟩
  · simpa using hT
  · have hzero := hsmooth 0
    rw [Finset.coe_neg] at hzero
    rw [← congrFun
      (CyclicBoostedAlmostPeriodicity.mu_ddconv_eq_probabilityWeight_convolution
        C.carrier_nonempty (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂)) 0] at hzero
    rw [mu_triple_indicator_neg_apply_zero_eq_sum,
      triple_indicator_neg_apply_zero_eq_sum] at hzero
    rw [norm_complex_tested_convolution_sub_eq_abs_real] at hzero
    simpa using hzero

/-- Adaptive positive-radius difference-convolution form. -/
theorem exists_local_bohr_tested_correlation_real_adaptive
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  simpa [← conjneg_mu] using
    (exists_local_bohr_tested_convolution_real_adaptive
      B A₁ (-A₂) U rho k halpha0 halphahalf hdelta hdeltat hAinner hAdense
      hregular hepsilon0 hepsilon1 hk hA₁ (by simpa using hA₂) hU heta hrho)

/-- Adaptive tested convolution with its smoothing carrier selected at a
fine regular scale. -/
theorem exists_local_regular_bohr_tested_convolution_real_adaptive
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k m : ℕ)
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank) (hm : 0 < m)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 < delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N) (u zeta : ℝ),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      0 < C.radius ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      1 / 2 ≤ u ∧ u ≤ 1 ∧
      zeta = (400 * (m : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < zeta ∧ zeta < u ∧
      (10 * m) * (C.dilate (u + zeta)).carrier.card ≤
        (10 * m + 1) * (C.dilate (u - zeta)).carrier.card ∧
      (C.dilate u).carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] (C.dilate u).carrier ∗ᵈ μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  obtain ⟨T, C, u, zeta, hT, hCradius, hCpos, hBrankC, hCrank,
      hulow, huhigh, hzetaFormula, hzeta, hzetau, hregularC, hCsub,
      hsmooth⟩ :=
    CyclicRelativeAlmostPeriodicity.exists_local_regular_bohr_smoothing_adaptive
      B A₁ (-U) A₂ rho k m hBradius hBrank hm halpha0 halphahalf
      hdelta hdeltat hAinner hAdense hregular hepsilon0 hepsilon1 hk hA₁
      (by simpa using hU) hA₂ heta hrho
  refine ⟨T, C, u, zeta, ?_, hCradius, hCpos, hBrankC, hCrank, hulow,
    huhigh, hzetaFormula, hzeta, hzetau, hregularC, hCsub, ?_⟩
  · simpa using hT
  · have hzero := hsmooth 0
    rw [Finset.coe_neg] at hzero
    rw [← congrFun
      (CyclicBoostedAlmostPeriodicity.mu_ddconv_eq_probabilityWeight_convolution
        (C.dilate u).carrier_nonempty
          (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂)) 0] at hzero
    rw [mu_triple_indicator_neg_apply_zero_eq_sum,
      triple_indicator_neg_apply_zero_eq_sum] at hzero
    rw [norm_complex_tested_convolution_sub_eq_abs_real] at hzero
    simpa using hzero

/-- Difference-convolution form of the regularized adaptive estimate. -/
theorem exists_local_regular_bohr_tested_correlation_real_adaptive
    (B : CyclicBohr.Set N) (A₁ A₂ U : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ)
    {t delta alpha epsilon eta : ℝ} (k m : ℕ)
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank) (hm : 0 < m)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 < delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N) (u zeta : ℝ),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius (rho T) ∧
      0 < C.radius ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      1 / 2 ≤ u ∧ u ≤ 1 ∧
      zeta = (400 * (m : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < zeta ∧ zeta < u ∧
      (10 * m) * (C.dilate (u + zeta)).carrier.card ≤
        (10 * m + 1) * (C.dilate (u - zeta)).carrier.card ∧
      (C.dilate u).carrier ⊆ (B.dilate delta).carrier ∧
      |(∑ x ∈ U,
          (μ_[ℝ] (C.dilate u).carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) := by
  simpa [← conjneg_mu] using
    (exists_local_regular_bohr_tested_convolution_real_adaptive
      B A₁ (-A₂) U rho k m hBradius hBrank hm halpha0 halphahalf
      hdelta hdeltat hAinner hAdense hregular hepsilon0 hepsilon1 hk hA₁
      (by simpa using hA₂) hU heta hrho)

end CyclicDensityIncrement
end Erdos721
