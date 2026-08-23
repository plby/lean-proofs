/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.LocalAPCounting
import APAP.Prereqs.FourierTransform.Discrete

/-!
# The improved Bloom--Sisask Fourier bootstrap

The older Kelley--Meka bootstrap tests an almost-periodic correlation
against an indicator.  Bloom and Sisask instead test it against the current
self-correlation.  The resulting fourfold convolution has Fourier
`L¹` norm at most `1 / |A|`, with no loss depending on the cardinality of
the test set.  This is the quantitative input responsible for the exponent
`9` in the integer three-term-progression bound.
-/

namespace Erdos721

open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicImprovedBootstrapping

variable {N : ℕ} [NeZero N]

lemma fourier_eq_inv_mul_dft (f : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier f r =
      (N : ℂ)⁻¹ * dft f (CyclicBohr.character r) := by
  simp [CyclicFourier.fourier, CyclicFourier.average, dft_apply,
    wInner_one_eq_sum, inner_apply, mul_comm]

lemma dft_eq_card_mul_fourier (f : ZMod N → ℂ) (r : ZMod N) :
    dft f (CyclicBohr.character r) =
      (N : ℂ) * CyclicFourier.fourier f r := by
  rw [fourier_eq_inv_mul_dft]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]

lemma fourier_ddconv (f g : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (f ∗ᵈ g) r =
      (N : ℂ) * CyclicFourier.fourier f r * CyclicFourier.fourier g r := by
  rw [fourier_eq_inv_mul_dft, dft_ddconv_apply,
    dft_eq_card_mul_fourier, dft_eq_card_mul_fourier]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

lemma fourier_dddconv (f g : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (f ○ᵈ g) r =
      (N : ℂ) * CyclicFourier.fourier f r *
        (starRingEnd ℂ) (CyclicFourier.fourier g r) := by
  rw [fourier_eq_inv_mul_dft, dft_dddconv_apply,
    dft_eq_card_mul_fourier, dft_eq_card_mul_fourier]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [map_mul, map_natCast]
  field_simp [hN]

lemma mu_eq_inv_mul_probabilityWeight
    {A : Finset (ZMod N)} (hA : A.Nonempty) :
    μ_[ℂ] A = fun x ↦ (N : ℂ)⁻¹ *
      CyclicSpectralSmoothing.probabilityWeight A x := by
  funext x
  by_cases hx : x ∈ A
  · rw [mu_apply, if_pos hx,
      CyclicSpectralSmoothing.probabilityWeight_apply_mem hx]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hcard : (A.card : ℂ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hA
    field_simp
  · rw [mu_apply, if_neg hx,
      CyclicSpectralSmoothing.probabilityWeight_apply_notMem hx]
    simp

lemma fourier_mu
    {A : Finset (ZMod N)} (hA : A.Nonempty) (r : ZMod N) :
    CyclicFourier.fourier (μ_[ℂ] A) r =
      (N : ℂ)⁻¹ * CyclicFourier.fourier
        (CyclicSpectralSmoothing.probabilityWeight A) r := by
  rw [mu_eq_inv_mul_probabilityWeight hA]
  exact CyclicSpectralSmoothing.fourier_const_mul _ _ _

lemma norm_fourier_mu_dddconv_mu
    {A : Finset (ZMod N)} (hA : A.Nonempty) (r : ZMod N) :
    ‖CyclicFourier.fourier (μ_[ℂ] A ○ᵈ μ_[ℂ] A) r‖ =
      (N : ℝ)⁻¹ *
        ‖CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 := by
  rw [fourier_dddconv, fourier_mu hA, norm_mul, norm_mul,
    RCLike.norm_conj, pow_two]
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  field_simp

lemma norm_fourier_mu_dddconv_mu_two
    {A B : Finset (ZMod N)} (hA : A.Nonempty) (hB : B.Nonempty)
    (r : ZMod N) :
    ‖CyclicFourier.fourier (μ_[ℂ] A ○ᵈ μ_[ℂ] B) r‖ =
      (N : ℝ)⁻¹ *
        ‖CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight A) r‖ *
        ‖CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight B) r‖ := by
  rw [fourier_dddconv, fourier_mu hA, fourier_mu hB, norm_mul, norm_mul,
    RCLike.norm_conj]
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  field_simp

/-- The improved fourfold test function has Fourier `L¹` norm at most
`1 / |A|`.  The proof is Parseval for the self-correlation of `A`, together
with the pointwise Fourier bound `|\widehat{\mu_S}| ≤ 1 / N` for probability
measures in the unnormalised-convolution convention used by APAP. -/
theorem sum_norm_fourier_improvedTestFunction_le
    {A A₁ A₂ : Finset (ZMod N)}
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) :
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A)) r‖ ≤
      (A.card : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpoint (r : ZMod N) :
      ‖CyclicFourier.fourier
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A)) r‖ ≤
        (N : ℝ)⁻¹ *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 := by
    rw [fourier_ddconv, norm_mul, norm_mul,
      norm_fourier_mu_dddconv_mu_two hA₁ hA₂,
      norm_fourier_mu_dddconv_mu hA]
    have hA₁one :=
      CyclicSpectralSmoothing.norm_fourier_probabilityWeight_le_one hA₁ r
    have hA₂one :=
      CyclicSpectralSmoothing.norm_fourier_probabilityWeight_le_one hA₂ r
    have hprod :
        ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight A₁) r‖ *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight A₂) r‖ ≤ 1 := by
      calc
        _ ≤ 1 * 1 := mul_le_mul hA₁one hA₂one (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc
      ‖(N : ℂ)‖ *
            ((N : ℝ)⁻¹ *
              ‖CyclicFourier.fourier
                (CyclicSpectralSmoothing.probabilityWeight A₁) r‖ *
              ‖CyclicFourier.fourier
                (CyclicSpectralSmoothing.probabilityWeight A₂) r‖) *
          ((N : ℝ)⁻¹ *
            ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2) =
          (N : ℝ)⁻¹ *
            (‖CyclicFourier.fourier
                (CyclicSpectralSmoothing.probabilityWeight A₁) r‖ *
              ‖CyclicFourier.fourier
                (CyclicSpectralSmoothing.probabilityWeight A₂) r‖) *
            ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 := by
        have hnormN : ‖(N : ℂ)‖ = (N : ℝ) := by simp
        rw [hnormN]
        field_simp
      _ ≤ (N : ℝ)⁻¹ * 1 *
            ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 := by
        gcongr
      _ = _ := by ring
  calc
    ∑ r : ZMod N,
        ‖CyclicFourier.fourier
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A)) r‖ ≤
        ∑ r : ZMod N, (N : ℝ)⁻¹ *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 :=
      Finset.sum_le_sum fun r _ ↦ hpoint r
    _ = (N : ℝ)⁻¹ *
        ∑ r : ZMod N,
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight A) r‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ((N : ℝ) / A.card) := by
      rw [CyclicBoostedAlmostPeriodicity.sum_norm_sq_fourier_probabilityWeight hA]
    _ = (A.card : ℝ)⁻¹ := by
      have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
      field_simp

/-! ## Smoothing the boosted function itself -/

/-- If a Bohr carrier controls the relative large spectrum of `T`, then it
almost fixes the *boosted* function `μ_T^(k) * F`.  Unlike the older transfer
lemma, this statement needs no hypothesis that the boosted function is close
to `F`; this is the form used after replacing the test-set indicator by the
self-correlation of `A`. -/
theorem norm_probabilityWeight_convolution_boosted_sub_le
    {T C : Finset (ZMod N)} (hT : T.Nonempty) (hC : C.Nonempty)
    (F : ZMod N → ℂ) (k : ℕ) {eta delta L : ℝ}
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ C,
      ‖1 - CyclicBohr.character r x‖ ≤ delta)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∀ x,
      ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C)
            (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x -
          (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x‖ ≤
        (delta + 2 * eta ^ k) * L := by
  have hmultiplier (r : ZMod N) :
      ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight C) r - 1‖ *
          ‖CyclicFourier.fourier (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) r‖ ≤
        (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
    rw [CyclicBoostedAlmostPeriodicity.fourier_mu_iterConv_ddconv hT F k r,
      norm_mul, norm_pow]
    by_cases hr : r ∈ CyclicChang.relativeLargeSpectrum T eta
    · have hCspec :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight C) r - 1‖ ≤ delta :=
        CyclicSpectralSmoothing.norm_fourier_probabilityWeight_sub_one_le
          hC (hcontrol r hr)
      have hTone :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight T) r‖ ≤ 1 :=
        CyclicSpectralSmoothing.norm_fourier_probabilityWeight_le_one hT r
      have hpow :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight T) r‖ ^ k ≤ 1 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) hTone k
      calc
        _ ≤ delta * (1 * ‖CyclicFourier.fourier F r‖) := by gcongr
        _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (by positivity)) (norm_nonneg _)
    · have hCtwo :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight C) r - 1‖ ≤ 2 :=
        CyclicSpectralSmoothing.norm_fourier_probabilityWeight_sub_one_le_two hC r
      have htail :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight T) r‖ ≤ eta := by
        have hr' : r ∉ CyclicFourier.largeSpectrum
            (CyclicSpectralSmoothing.probabilityWeight T) eta := by
          rwa [CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
            hT]
        exact le_of_lt (by
          simpa only [CyclicFourier.mem_largeSpectrum, not_le] using hr')
      have hpow :
          ‖CyclicFourier.fourier
              (CyclicSpectralSmoothing.probabilityWeight T) r‖ ^ k ≤ eta ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) htail k
      calc
        _ ≤ 2 * (eta ^ k * ‖CyclicFourier.fourier F r‖) := by gcongr
        _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
          rw [show 2 * (eta ^ k * ‖CyclicFourier.fourier F r‖) =
            (2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ by ring]
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hdelta) (norm_nonneg _)
  intro x
  calc
    ‖CyclicFourier.convolution
          (CyclicSpectralSmoothing.probabilityWeight C)
          (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x -
        (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x‖ ≤
      ∑ r : ZMod N,
        ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight C) r - 1‖ *
          ‖CyclicFourier.fourier (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) r‖ :=
      CyclicSpectralSmoothing.norm_convolution_sub_le_sum_fourier _ _ _
    _ ≤ ∑ r : ZMod N,
        (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ :=
      Finset.sum_le_sum fun r _ ↦ hmultiplier r
    _ = (delta + 2 * eta ^ k) *
        ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ := by
      rw [Finset.mul_sum]
    _ ≤ (delta + 2 * eta ^ k) * L := by
      exact mul_le_mul_of_nonneg_left hFourierL1 (by positivity)

/-- A preconstructed Bohr controller can be intersected with an ambient
Bohr set and regularized without changing the spectral smoothing argument.
This is the interface needed by the local Chang--Sanders lemma: unlike the
global Chang specialization below, its rank cost is exactly the rank of the
supplied controller. -/
theorem exists_regular_refined_bohr_smoothing_of_boostedFunction_of_controller
    (R B : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k m : ℕ) {eta control L : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hBradius : 0 < B.radius) (heta : 0 ≤ eta) (hcontrol0 : 0 ≤ control)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ control)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ (D : CyclicBohr.Set N) (t delta : ℝ),
      D.radius = min R.radius B.radius ∧
      0 < D.radius ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + B.rank ∧
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      (10 * m) * (D.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (D.dilate (t - delta)).carrier.card ∧
      (D.dilate t).carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
              (CyclicSpectralSmoothing.probabilityWeight
                (D.dilate t).carrier)
              (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x -
            (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x‖ ≤
          (control + 2 * eta ^ k) * L := by
  let D : CyclicBohr.Set N := R.meet B
  have hDradius : D.radius = min R.radius B.radius := rfl
  have hDpos : 0 < D.radius := by
    rw [hDradius]
    exact lt_min hRradius hBradius
  have hRD : R.rank ≤ D.rank :=
    Finset.card_le_card Finset.subset_union_left
  have hDrank : D.rank ≤ R.rank + B.rank :=
    CyclicBohr.Set.rank_meet_le R B
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
    apply norm_probabilityWeight_convolution_boosted_sub_le
      hT (D.dilate t).carrier_nonempty F k heta hcontrol0
    · intro r hr y hy
      exact hcontrol r hr y
        (CyclicBohr.Set.carrier_meet_subset_right R B (hDtD hy))
    · exact hFourierL1

/-- Frequency-subset specialization of the preceding controller theorem.
If the supplied controller already contains every ambient frequency, the
final meet adds no rank at all.  This is the form used by the local
Chang--Sanders construction, whose auxiliary Bohr set deliberately retains
the ambient frequencies. -/
theorem exists_regular_refined_bohr_smoothing_of_boostedFunction_of_controller_subset
    (R B : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k m : ℕ) {eta control L : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hBradius : 0 < B.radius) (hfreq : R.frequencies ⊆ B.frequencies)
    (heta : 0 ≤ eta) (hcontrol0 : 0 ≤ control)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ control)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∃ (D : CyclicBohr.Set N) (t delta : ℝ),
      D.radius = min R.radius B.radius ∧
      0 < D.radius ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ B.rank ∧
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      (10 * m) * (D.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (D.dilate (t - delta)).carrier.card ∧
      (D.dilate t).carrier ⊆ R.carrier ∧
      ∀ x,
        ‖CyclicFourier.convolution
              (CyclicSpectralSmoothing.probabilityWeight
                (D.dilate t).carrier)
              (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x -
            (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x‖ ≤
          (control + 2 * eta ^ k) * L := by
  let D : CyclicBohr.Set N := R.meet B
  have hDradius : D.radius = min R.radius B.radius := rfl
  have hDpos : 0 < D.radius := by
    rw [hDradius]
    exact lt_min hRradius hBradius
  have hRD : R.rank ≤ D.rank :=
    Finset.card_le_card Finset.subset_union_left
  have hDrank : D.rank ≤ B.rank := by
    change (R.frequencies ∪ B.frequencies).card ≤ B.frequencies.card
    rw [Finset.union_eq_right.mpr hfreq]
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
    apply norm_probabilityWeight_convolution_boosted_sub_le
      hT (D.dilate t).carrier_nonempty F k heta hcontrol0
    · intro r hr y hy
      exact hcontrol r hr y
        (CyclicBohr.Set.carrier_meet_subset_right R B (hDtD hy))
    · exact hFourierL1

/-- Chang's lemma, intersection with an ambient Bohr set, and fine-scale
regularization, applied directly to the boosted function. -/
theorem exists_regular_refined_bohr_smoothing_of_boostedFunction
    (R : CyclicBohr.Set N)
    {T : Finset (ZMod N)} (hT : T.Nonempty)
    (F : ZMod N → ℂ) (k m : ℕ) {eta rho L : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (heta : 0 < eta) (hrho : 0 < rho)
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
              (CyclicSpectralSmoothing.probabilityWeight
                (D.dilate t).carrier)
              (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x -
            (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ F) x‖ ≤
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
    apply norm_probabilityWeight_convolution_boosted_sub_le
      hT (D.dilate t).carrier_nonempty F k heta.le
        (mul_nonneg (Nat.cast_nonneg _) hrho.le)
    · intro r hr y hy
      calc
        ‖1 - CyclicBohr.character r y‖ ≤ (B.rank : ℝ) * rho :=
          hcontrol r hr y
            (CyclicBohr.Set.carrier_meet_subset_right R B (hDtD hy))
        _ ≤ (CyclicChang.changRankBound T eta : ℝ) * rho := by gcongr
    · exact hFourierL1

end CyclicImprovedBootstrapping
end Erdos721
