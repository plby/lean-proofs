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

import ErdosProblems.Erdos721.SpectralSmoothing
import ErdosProblems.Erdos721.Regularity
import APAP.Physics.AlmostPeriodicity

/-!
# Boosted cyclic almost-periodicity

This file connects the clean finite Croot--Sisask theorem in LeanAPAP to the
cyclic Fourier and Bohr-set normalization used for Erdős Problem 721.  The
key normalization identity says that unnormalized discrete convolution by
APAP's probability measure `mu T` is exactly normalized cyclic convolution
by `probabilityWeight T`.
-/

namespace Erdos721

open Finset Fintype
open scoped BigOperators ENNReal Indicator mu NNReal

namespace CyclicBoostedAlmostPeriodicity

variable {N : ℕ} [NeZero N]

open CyclicFourier CyclicSpectralSmoothing

/-! ## Translation between the two convolution normalizations -/

/-- APAP's unnormalized convolution by its normalized indicator is exactly
our normalized cyclic convolution by the average-one probability weight. -/
lemma mu_ddconv_eq_probabilityWeight_convolution
    {S : Finset (ZMod N)} (hS : S.Nonempty) (f : ZMod N → ℂ) :
    μ_[ℂ] S ∗ᵈ f =
      CyclicFourier.convolution (probabilityWeight S) f := by
  funext x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [ddconv_eq_sum_sub']
  unfold CyclicFourier.convolution CyclicFourier.average probabilityWeight
  simp_rw [mu_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  calc
    (∑ y : ZMod N,
      (if y ∈ S then (S.card : ℂ)⁻¹ * f (x - y) else 0)) =
        (S.card : ℂ)⁻¹ * ∑ y ∈ S, f (x - y) := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = (N : ℂ)⁻¹ *
        ∑ y : ZMod N,
          (if y ∈ S then (N : ℂ) / S.card * f (x - y) else 0) := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← Finset.mul_sum]
      field_simp

/-- The local Fourier transform of the APAP convolution power is the
corresponding power of the probability-weight Fourier multiplier. -/
theorem fourier_mu_iterConv_ddconv
    {T : Finset (ZMod N)} (hT : T.Nonempty) (F : ZMod N → ℂ) :
    ∀ k r,
      CyclicFourier.fourier (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) r =
        CyclicFourier.fourier (probabilityWeight T) r ^ k *
          CyclicFourier.fourier F r
  | 0, r => by simp
  | k + 1, r => by
      rw [iterConv_succ', ddconv_assoc,
        mu_ddconv_eq_probabilityWeight_convolution hT,
        CyclicFourier.fourier_convolution,
        fourier_mu_iterConv_ddconv hT F k r, pow_succ]
      ring

/-! ## Spectral smoothing for a boosted approximation -/

/-- A uniform approximation by an APAP convolution power may be smoothed by
any cyclic Bohr set controlling the relative large spectrum of the sampling
set. -/
theorem norm_probabilityWeight_convolution_sub_le_of_boosted
    {T B : Finset (ZMod N)} (hT : T.Nonempty) (hB : B.Nonempty)
    (F : ZMod N → ℂ) (k : ℕ) {eta delta epsilon L : ℝ}
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ delta)
    (happrox : ∀ x,
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∀ x,
      ‖CyclicFourier.convolution (probabilityWeight B) F x - F x‖ ≤
        2 * epsilon + (delta + 2 * eta ^ k) * L := by
  apply norm_probabilityWeight_convolution_sub_le_of_fourier_decay
    hT hB F (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) k heta hdelta hepsilon hcontrol
  · intro r hr
    have hr' : r ∉ CyclicFourier.largeSpectrum (probabilityWeight T) eta := by
      rwa [largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum hT]
    exact le_of_lt (by simpa only [CyclicFourier.mem_largeSpectrum, not_le] using hr')
  · exact fun r ↦ fourier_mu_iterConv_ddconv hT F k r
  · exact happrox
  · exact hFourierL1

/-- Chang's lemma supplies the Bohr set required by the boosted smoothing
argument, with the exact local rank bound. -/
theorem exists_bohr_smoothing_of_boosted
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k : ℕ) {eta rho epsilon L : ℝ}
    (heta : 0 < eta) (hrho : 0 ≤ rho) (hepsilon : 0 ≤ epsilon)
    (happrox : ∀ x,
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ B : CyclicBohr.Set N,
      B.rank ≤ CyclicChang.changRankBound T eta ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight B.carrier) F x - F x‖ ≤
          2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho +
              2 * eta ^ k) * L := by
  obtain ⟨B, _hfreq, hrank, hcontrol⟩ :=
    CyclicChang.exists_bohr_controlling_relativeLargeSpectrum
      T hT heta hrho
  refine ⟨B, hrank, ?_⟩
  apply norm_probabilityWeight_convolution_sub_le_of_boosted
    hT B.carrier_nonempty F k heta.le (mul_nonneg (Nat.cast_nonneg _) hrho)
      hepsilon
  · intro r hr x hx
    exact hcontrol r hr x hx
  · exact happrox
  · exact hFourierL1

/-- A localized version of spectral smoothing: adjoining the frequencies of
an ambient Bohr set preserves the smoothing estimate, refines that ambient
set, and costs only the sum of the two ranks. -/
theorem exists_refined_bohr_smoothing_of_boosted
    (R : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k : ℕ) {eta rho epsilon L : ℝ}
    (heta : 0 < eta) (hrho : 0 ≤ rho) (hepsilon : 0 ≤ epsilon)
    (happrox : ∀ x,
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ D : CyclicBohr.Set N,
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      D.carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight D.carrier) F x - F x‖ ≤
          2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho +
              2 * eta ^ k) * L := by
  obtain ⟨B, _hfreq, hrank, hcontrol⟩ :=
    CyclicChang.exists_bohr_controlling_relativeLargeSpectrum
      T hT heta hrho
  let D := R.meet B
  refine ⟨D, ?_, CyclicBohr.Set.carrier_meet_subset_left R B, ?_⟩
  · exact (CyclicBohr.Set.rank_meet_le R B).trans
      (Nat.add_le_add_left hrank R.rank)
  · apply norm_probabilityWeight_convolution_sub_le_of_boosted
      hT D.carrier_nonempty F k heta.le
        (mul_nonneg (Nat.cast_nonneg _) hrho) hepsilon
    · intro r hr x hx
      exact hcontrol r hr x (CyclicBohr.Set.carrier_meet_subset_right R B hx)
    · exact happrox
    · exact hFourierL1

/-- Radius-preserving form of localized spectral smoothing.  The Croot--
Sisask shift set is already fixed, so the spectral radius may be chosen as a
positive function of its explicit Chang rank bound. -/
theorem exists_refined_bohr_smoothing_of_boosted_sharp
    (R : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k : ℕ) {eta rho epsilon L : ℝ}
    (heta : 0 < eta) (hrho : 0 ≤ rho) (hepsilon : 0 ≤ epsilon)
    (happrox : ∀ x,
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ D : CyclicBohr.Set N,
      D.radius = min R.radius rho ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      D.carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight D.carrier) F x - F x‖ ≤
          2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho +
              2 * eta ^ k) * L := by
  obtain ⟨B, hBradius, _hfreq, hBrank, hcontrol⟩ :=
    CyclicChang.exists_bohr_controlling_relativeLargeSpectrum_sharp
      T hT heta hrho
  let D := R.meet B
  refine ⟨D, ?_, ?_, ?_, CyclicBohr.Set.carrier_meet_subset_left R B, ?_⟩
  · simpa [D] using congrArg (fun x : ℝ ↦ min R.radius x) hBradius
  · exact Finset.card_le_card Finset.subset_union_left
  · exact (CyclicBohr.Set.rank_meet_le R B).trans
      (Nat.add_le_add_left hBrank R.rank)
  · apply norm_probabilityWeight_convolution_sub_le_of_boosted
      hT D.carrier_nonempty F k heta.le
        (mul_nonneg (Nat.cast_nonneg _) hrho) hepsilon
    · intro r hr x hx
      calc
        ‖1 - CyclicBohr.character r x‖ ≤ (B.rank : ℝ) * rho :=
          hcontrol r hr x (CyclicBohr.Set.carrier_meet_subset_right R B hx)
        _ ≤ (CyclicChang.changRankBound T eta : ℝ) * rho := by
          gcongr
    · exact happrox
    · exact hFourierL1

/-- Radius-preserving localized smoothing whose actual averaging carrier is
chosen at a fine regular scale.  The base Bohr set `D` retains the exact
spectral radius and rank bounds, while `D_t` is the carrier passed to the
next density-increment stage. -/
theorem exists_regular_refined_bohr_smoothing_of_boosted_sharp
    (R : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k m : ℕ) {eta rho epsilon L : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (heta : 0 < eta) (hrho : 0 < rho) (hepsilon : 0 ≤ epsilon)
    (happrox : ∀ x,
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ (D : CyclicBohr.Set N) (t delta : ℝ),
      D.radius = min R.radius rho ∧
      0 < D.radius ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      (10 * m) * (D.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (D.dilate (t - delta)).carrier.card ∧
      (D.dilate t).carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
              (probabilityWeight (D.dilate t).carrier) F x - F x‖ ≤
          2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho +
              2 * eta ^ k) * L := by
  obtain ⟨B, hBradius, _hfreq, hBrank, hcontrol⟩ :=
    CyclicChang.exists_bohr_controlling_relativeLargeSpectrum_sharp
      T hT heta hrho.le
  let D : CyclicBohr.Set N := R.meet B
  have hDradius : D.radius = min R.radius rho := by
    simpa [D] using congrArg (fun x : ℝ ↦ min R.radius x) hBradius
  have hDpos : 0 < D.radius := by rw [hDradius]; exact lt_min hRradius hrho
  have hRD : R.rank ≤ D.rank := Finset.card_le_card Finset.subset_union_left
  have hDrank :
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta :=
    (CyclicBohr.Set.rank_meet_le R B).trans
      (Nat.add_le_add_left hBrank R.rank)
  have hD0 : 0 < D.rank := hRrank.trans_le hRD
  obtain ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
      hregular⟩ :=
    CyclicBohr.exists_fixed_regular_scale_fine D m hDpos hD0 hm
  have hDtD : (D.dilate t).carrier ⊆ D.carrier := by
    have hmono := CyclicBohr.Set.dilate_mono D (by linarith : 0 ≤ t) hthigh
    simpa only [CyclicBohr.carrier_dilate_one] using hmono
  refine ⟨D, t, delta, hDradius, hDpos, hRD, hDrank, htlow, hthigh,
    hdeltaFormula, hdelta, hdeltat, hregular, ?_, ?_⟩
  · exact hDtD.trans (CyclicBohr.Set.carrier_meet_subset_left R B)
  · intro x
    apply norm_probabilityWeight_convolution_sub_le_of_boosted
      hT (D.dilate t).carrier_nonempty F k heta.le
        (mul_nonneg (Nat.cast_nonneg _) hrho.le) hepsilon
    · intro r hr y hy
      calc
        ‖1 - CyclicBohr.character r y‖ ≤ (B.rank : ℝ) * rho :=
          hcontrol r hr y
            (CyclicBohr.Set.carrier_meet_subset_right R B (hDtD hy))
        _ ≤ (CyclicChang.changRankBound T eta : ℝ) * rho := by
          gcongr
    · exact happrox
    · exact hFourierL1

/-! ## The Fourier `L¹` input -/

/-- APAP's complex indicator notation agrees with the local cyclic indicator. -/
lemma indicatorOne_eq_cyclicIndicator (P : Finset (ZMod N)) :
    (𝟭_[P] : ZMod N → ℂ) = CyclicFourier.indicator P := by
  funext x
  by_cases hx : x ∈ P <;> simp [CyclicFourier.indicator, hx]

/-- Parseval for the local finite-set probability weight. -/
lemma sum_norm_sq_fourier_probabilityWeight
    {A : Finset (ZMod N)} (hA : A.Nonempty) :
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier (probabilityWeight A) r‖ ^ 2 =
      (N : ℝ) / A.card := by
  have hdensity : 0 < CyclicChang.density A := CyclicChang.density_pos hA
  have hparseval :
      ∑ r : ZMod N,
          ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ ^ 2 =
        CyclicChang.density A := by
    rw [← CyclicFourier.parseval_norm_sq_real,
      CyclicFourier.sum_norm_sq_indicator]
    unfold CyclicChang.density
    ring
  calc
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier (probabilityWeight A) r‖ ^ 2 =
      ∑ r : ZMod N,
        (‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ /
          CyclicChang.density A) ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [norm_fourier_probabilityWeight_eq_div_density hA]
    _ = (CyclicChang.density A)⁻¹ ^ 2 *
        ∑ r : ZMod N,
          ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      field_simp
    _ = (CyclicChang.density A)⁻¹ := by
      rw [hparseval]
      field_simp
    _ = (N : ℝ) / A.card := by
      unfold CyclicChang.density
      have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      have hcard : (A.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr hA
      field_simp

/-- Parseval for the ordinary cyclic indicator. -/
lemma sum_norm_sq_fourier_indicator (P : Finset (ZMod N)) :
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier (CyclicFourier.indicator P) r‖ ^ 2 =
      (P.card : ℝ) / N := by
  rw [← CyclicFourier.parseval_norm_sq_real,
    CyclicFourier.sum_norm_sq_indicator]
  ring

/-- The APAP triple convolution is the corresponding iterated local cyclic
convolution. -/
lemma triple_ddconv_eq_probabilityWeight_convolutions
    {A Q : Finset (ZMod N)} (hA : A.Nonempty) (hQ : Q.Nonempty)
    (P : Finset (ZMod N)) :
    μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q =
      CyclicFourier.convolution (probabilityWeight Q)
        (CyclicFourier.convolution (probabilityWeight A)
          (CyclicFourier.indicator P)) := by
  calc
    μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q =
        μ_[ℂ] Q ∗ᵈ (μ_[ℂ] A ∗ᵈ 𝟭_[P]) := by
      rw [ddconv_comm]
    _ = CyclicFourier.convolution (probabilityWeight Q)
        (μ_[ℂ] A ∗ᵈ 𝟭_[P]) :=
      mu_ddconv_eq_probabilityWeight_convolution hQ _
    _ = CyclicFourier.convolution (probabilityWeight Q)
        (CyclicFourier.convolution (probabilityWeight A)
          (CyclicFourier.indicator P)) := by
      rw [mu_ddconv_eq_probabilityWeight_convolution hA,
        indicatorOne_eq_cyclicIndicator]

/-- The Fourier `L¹` norm of `mu A * 1_P * mu Q` is bounded by the geometric
mean of the probability and indicator `L²` norms. -/
theorem sum_norm_fourier_triple_ddconv_le
    {A Q : Finset (ZMod N)} (hA : A.Nonempty) (hQ : Q.Nonempty)
    (P : Finset (ZMod N)) :
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) r‖ ≤
      Real.sqrt ((N : ℝ) / A.card) *
        Real.sqrt ((P.card : ℝ) / N) := by
  have hpoint (r : ZMod N) :
      ‖CyclicFourier.fourier (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) r‖ ≤
        ‖CyclicFourier.fourier (probabilityWeight A) r‖ *
          ‖CyclicFourier.fourier (CyclicFourier.indicator P) r‖ := by
    rw [triple_ddconv_eq_probabilityWeight_convolutions hA hQ P,
      CyclicFourier.fourier_convolution, CyclicFourier.fourier_convolution,
      norm_mul, norm_mul]
    have hQone := norm_fourier_probabilityWeight_le_one hQ r
    exact mul_le_of_le_one_left
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hQone
  calc
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) r‖ ≤
      ∑ r : ZMod N,
        ‖CyclicFourier.fourier (probabilityWeight A) r‖ *
          ‖CyclicFourier.fourier (CyclicFourier.indicator P) r‖ :=
      Finset.sum_le_sum fun r _ ↦ hpoint r
    _ ≤ Real.sqrt
          (∑ r : ZMod N,
            ‖CyclicFourier.fourier (probabilityWeight A) r‖ ^ 2) *
        Real.sqrt
          (∑ r : ZMod N,
            ‖CyclicFourier.fourier (CyclicFourier.indicator P) r‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt ((N : ℝ) / A.card) *
        Real.sqrt ((P.card : ℝ) / N) := by
      rw [sum_norm_sq_fourier_probabilityWeight hA,
        sum_norm_sq_fourier_indicator]

/-! ## The quantitative Croot--Sisask--Chang package -/

/-- The clean boosted Croot--Sisask theorem, followed by the cyclic Chang and
Fourier-tail steps.  This is the cyclic Bohr-set analogue of the subspace
almost-periodicity lemma in the finite-field proof. -/
theorem exists_large_set_and_bohr_smoothing
    (A S P Q : Finset (ZMod N)) {K epsilon eta rho L : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hS : S.Nonempty) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho)
    (hFourierL1 :
      ∑ r : ZMod N,
        ‖CyclicFourier.fourier
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) r‖ ≤ L) :
    ∃ (T : Finset (ZMod N)) (B : CyclicBohr.Set N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      B.rank ≤ CyclicChang.changRankBound T eta ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight B.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) * L := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let F : ZMod N → ℂ := μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q
  obtain ⟨T, hTcard, hTapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted
      epsilon hepsilon0 hepsilon1 k hk hK2 hK hS P Q hP hQ
  have hTpos : (0 : ℝ) < T.card := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
    have hScardpos : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr hS
    exact (mul_pos (Real.rpow_pos_of_pos hKpos _) hScardpos).trans_le hTcard
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hTpos
  have happrox (x : ZMod N) :
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon := by
    calc
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ =
          ‖((μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F) x‖ := rfl
      _ ≤ ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F‖_[∞] :=
        MeasureTheory.norm_le_dLinftyNorm
      _ ≤ epsilon := by simpa only [F] using hTapprox
  obtain ⟨B, hrank, hsmooth⟩ :=
    exists_bohr_smoothing_of_boosted hT F k heta hrho hepsilon0.le
      happrox (by simpa only [F] using hFourierL1)
  exact ⟨T, B, by simpa using hTcard, hrank, by simpa only [F] using hsmooth⟩

/-- Fully explicit form of the preceding package, with the Fourier `L¹`
input discharged by Parseval and Cauchy--Schwarz. -/
theorem exists_large_set_and_bohr_smoothing_explicit
    (A S P Q : Finset (ZMod N)) {K epsilon eta rho : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (B : CyclicBohr.Set N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      B.rank ≤ CyclicChang.changRankBound T eta ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight B.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  apply exists_large_set_and_bohr_smoothing A S P Q k hepsilon0 hepsilon1
    hk hK2 hK hS hP hQ heta hrho
  exact sum_norm_fourier_triple_ddconv_le hA hQ P

/-- Localized quantitative package.  The resulting spectral Bohr set is
refined by an arbitrary ambient Bohr set `R`. -/
theorem exists_large_set_and_refined_bohr_smoothing
    (R : CyclicBohr.Set N) (A S P Q : Finset (ZMod N))
    {K epsilon eta rho L : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hS : S.Nonempty) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho)
    (hFourierL1 :
      ∑ r : ZMod N,
        ‖CyclicFourier.fourier
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) r‖ ≤ L) :
    ∃ (T : Finset (ZMod N)) (D : CyclicBohr.Set N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      D.carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight D.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) * L := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let F : ZMod N → ℂ := μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q
  obtain ⟨T, hTcard, hTapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted
      epsilon hepsilon0 hepsilon1 k hk hK2 hK hS P Q hP hQ
  have hTpos : (0 : ℝ) < T.card := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
    have hScardpos : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr hS
    exact (mul_pos (Real.rpow_pos_of_pos hKpos _) hScardpos).trans_le hTcard
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hTpos
  have happrox (x : ZMod N) :
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon := by
    calc
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ =
          ‖((μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F) x‖ := rfl
      _ ≤ ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F‖_[∞] :=
        MeasureTheory.norm_le_dLinftyNorm
      _ ≤ epsilon := by simpa only [F] using hTapprox
  obtain ⟨D, hrank, hDR, hsmooth⟩ :=
    exists_refined_bohr_smoothing_of_boosted R hT F k heta hrho
      hepsilon0.le happrox (by simpa only [F] using hFourierL1)
  exact ⟨T, D, by simpa using hTcard, hrank, hDR,
    by simpa only [F] using hsmooth⟩

/-- Fully explicit localized package, with its Fourier `L¹` input discharged
by Parseval and Cauchy--Schwarz. -/
theorem exists_large_set_and_refined_bohr_smoothing_explicit
    (R : CyclicBohr.Set N) (A S P Q : Finset (ZMod N))
    {K epsilon eta rho : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho) :
    ∃ (T : Finset (ZMod N)) (D : CyclicBohr.Set N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      D.carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight D.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  apply exists_large_set_and_refined_bohr_smoothing
    R A S P Q k hepsilon0 hepsilon1 hk hK2 hK hS hP hQ heta hrho
  exact sum_norm_fourier_triple_ddconv_le hA hQ P

/-- Localized smoothing with a positive spectral radius chosen after the
Croot--Sisask shift set has been produced.  This retains the exact radius of
the refined Bohr set for subsequent quantitative iteration. -/
theorem exists_large_set_and_refined_bohr_smoothing_explicit_adaptive
    (R : CyclicBohr.Set N) (A S P Q : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ) {K epsilon eta : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (D : CyclicBohr.Set N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      D.radius = min R.radius (rho T) ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      D.carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution (probabilityWeight D.carrier)
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
          (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
        2 * epsilon +
          ((CyclicChang.changRankBound T eta : ℝ) * rho T +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A.card) *
                Real.sqrt ((P.card : ℝ) / N)) := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let F : ZMod N → ℂ := μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q
  obtain ⟨T, hTcard, hTapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted
      epsilon hepsilon0 hepsilon1 k hk hK2 hK hS P Q hP hQ
  have hTpos : (0 : ℝ) < T.card := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
    have hScardpos : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr hS
    exact (mul_pos (Real.rpow_pos_of_pos hKpos _) hScardpos).trans_le hTcard
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hTpos
  have happrox (x : ZMod N) :
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon := by
    calc
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ =
          ‖((μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F) x‖ := rfl
      _ ≤ ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F‖_[∞] :=
        MeasureTheory.norm_le_dLinftyNorm
      _ ≤ epsilon := by simpa only [F] using hTapprox
  obtain ⟨D, hDradius, hRrank, hDrank, hDR, hsmooth⟩ :=
    exists_refined_bohr_smoothing_of_boosted_sharp R hT F k heta
      (hrho T hT).le hepsilon0.le happrox (by
        simpa only [F] using sum_norm_fourier_triple_ddconv_le hA hQ P)
  exact ⟨T, D, by simpa using hTcard, hDradius, hRrank, hDrank, hDR,
    by simpa only [F] using hsmooth⟩

/-- Adaptive localized smoothing with fine regularization performed before
the smoothing kernel is used.  This is the iteration-facing variant of
`exists_large_set_and_refined_bohr_smoothing_explicit_adaptive`. -/
theorem exists_large_set_and_regular_refined_bohr_smoothing_explicit_adaptive
    (R : CyclicBohr.Set N) (A S P Q : Finset (ZMod N))
    (rho : Finset (ZMod N) → ℝ) {K epsilon eta : ℝ} (k m : ℕ)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (heta : 0 < eta) (hrho : ∀ T, T.Nonempty → 0 < rho T) :
    ∃ (T : Finset (ZMod N)) (D : CyclicBohr.Set N) (t delta : ℝ),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      D.radius = min R.radius (rho T) ∧
      0 < D.radius ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound T eta ∧
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      (10 * m) * (D.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (D.dilate (t - delta)).carrier.card ∧
      (D.dilate t).carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
              (probabilityWeight (D.dilate t).carrier)
              (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x -
            (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) x‖ ≤
          2 * epsilon +
            ((CyclicChang.changRankBound T eta : ℝ) * rho T +
              2 * eta ^ k) *
                (Real.sqrt ((N : ℝ) / A.card) *
                  Real.sqrt ((P.card : ℝ) / N)) := by
  letI : MeasurableSpace (ZMod N) := ⊤
  let F : ZMod N → ℂ := μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q
  obtain ⟨T, hTcard, hTapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted
      epsilon hepsilon0 hepsilon1 k hk hK2 hK hS P Q hP hQ
  have hTpos : (0 : ℝ) < T.card := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
    have hScardpos : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr hS
    exact (mul_pos (Real.rpow_pos_of_pos hKpos _) hScardpos).trans_le hTcard
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hTpos
  have happrox (x : ZMod N) :
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ ≤ epsilon := by
    calc
      ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x - F x‖ =
          ‖((μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F) x‖ := rfl
      _ ≤ ‖(μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) - F‖_[∞] :=
        MeasureTheory.norm_le_dLinftyNorm
      _ ≤ epsilon := by simpa only [F] using hTapprox
  obtain ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank, htlow,
      hthigh, hdeltaFormula, hdelta, hdeltat, hregular, hDR, hsmooth⟩ :=
    exists_regular_refined_bohr_smoothing_of_boosted_sharp
      R hT F k m hRradius hRrank hm heta (hrho T hT) hepsilon0.le
      happrox (by
        simpa only [F] using sum_norm_fourier_triple_ddconv_le hA hQ P)
  exact ⟨T, D, t, delta, by simpa using hTcard, hDradius, hDpos,
    hRrankD, hDrank, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
    hregular, hDR, by simpa only [F] using hsmooth⟩

end CyclicBoostedAlmostPeriodicity
end Erdos721
