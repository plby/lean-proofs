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

import ErdosProblems.Erdos721.Chang
import ErdosProblems.Erdos721.CrootSisask

/-!
# Fourier smoothing on cyclic Bohr sets

This file proves the Fourier-tail step which replaces the exact annihilator
subspace in the finite-field Kelley--Meka argument.  A cyclic Bohr set only
approximately annihilates a chosen spectrum.  Averaging over that Bohr set
therefore changes the large-spectrum contribution by the prescribed chord
error, while convolution powers of an almost-period set suppress the
complementary spectrum geometrically.
-/

namespace Erdos721

open AddChar Finset Fintype
open scoped BigOperators

namespace CyclicSpectralSmoothing

variable {N : ℕ} [NeZero N]

open CyclicFourier

/-! ## Probability weights -/

/-- The complex probability weight of a finite subset of `ZMod N`, scaled so
that its normalized average is one. -/
noncomputable def probabilityWeight (S : Finset (ZMod N)) (x : ZMod N) : ℂ :=
  if x ∈ S then (N : ℂ) / S.card else 0

lemma probabilityWeight_apply_mem {S : Finset (ZMod N)} {x : ZMod N}
    (hx : x ∈ S) : probabilityWeight S x = (N : ℂ) / S.card := by
  simp [probabilityWeight, hx]

lemma probabilityWeight_apply_notMem {S : Finset (ZMod N)} {x : ZMod N}
    (hx : x ∉ S) : probabilityWeight S x = 0 := by
  simp [probabilityWeight, hx]

/-- A nonempty finite-set probability weight has normalized average one. -/
lemma average_probabilityWeight {S : Finset (ZMod N)} (hS : S.Nonempty) :
    average (probabilityWeight S) = 1 := by
  have hScard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  unfold average probabilityWeight
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]
  field_simp [hScard, NeZero.ne N]

/-- The probability Fourier coefficient is the literal average of the
conjugate character over the finite set. -/
lemma fourier_probabilityWeight {S : Finset (ZMod N)} (hS : S.Nonempty)
    (r : ZMod N) :
    CyclicFourier.fourier (probabilityWeight S) r =
      (S.card : ℂ)⁻¹ * ∑ x ∈ S,
        (starRingEnd ℂ) (CyclicBohr.character r x) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hScard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  unfold CyclicFourier.fourier average probabilityWeight
  calc
    (N : ℂ)⁻¹ * ∑ x : ZMod N,
        (starRingEnd ℂ) (CyclicBohr.character r x) *
          (if x ∈ S then (N : ℂ) / S.card else 0) =
      (N : ℂ)⁻¹ * ∑ x ∈ S,
        (starRingEnd ℂ) (CyclicBohr.character r x) *
          ((N : ℂ) / S.card) := by
        congr 1
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = (S.card : ℂ)⁻¹ * ∑ x ∈ S,
          (starRingEnd ℂ) (CyclicBohr.character r x) := by
        rw [← Finset.sum_mul]
        field_simp

/-- Every Fourier coefficient of a finite-set probability weight lies in the
closed unit disk. -/
lemma norm_fourier_probabilityWeight_le_one {S : Finset (ZMod N)}
    (hS : S.Nonempty) (r : ZMod N) :
    ‖CyclicFourier.fourier (probabilityWeight S) r‖ ≤ 1 := by
  rw [fourier_probabilityWeight hS]
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  calc
    ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S,
        (starRingEnd ℂ) (CyclicBohr.character r x)‖ ≤
      ‖(S.card : ℂ)⁻¹‖ *
        ∑ x ∈ S, ‖(starRingEnd ℂ) (CyclicBohr.character r x)‖ := by
          rw [norm_mul]
          gcongr
          exact norm_sum_le _ _
    _ = (S.card : ℝ)⁻¹ * S.card := by
      simp [CyclicBohr.norm_character, norm_inv, abs_of_pos hcard]
    _ = 1 := by field_simp

/-- If every point of a probability set nearly annihilates a frequency, its
Fourier coefficient at that frequency is close to one. -/
lemma norm_fourier_probabilityWeight_sub_one_le
    {S : Finset (ZMod N)} (hS : S.Nonempty) {r : ZMod N} {delta : ℝ}
    (hcontrol : ∀ x ∈ S, ‖1 - CyclicBohr.character r x‖ ≤ delta) :
    ‖CyclicFourier.fourier (probabilityWeight S) r - 1‖ ≤ delta := by
  rw [fourier_probabilityWeight hS]
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hcardC : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hrearrange :
      (S.card : ℂ)⁻¹ * ∑ x ∈ S,
          (starRingEnd ℂ) (CyclicBohr.character r x) - 1 =
        (S.card : ℂ)⁻¹ * ∑ x ∈ S,
          ((starRingEnd ℂ) (CyclicBohr.character r x) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [mul_sub]
    simp [hcardC]
  rw [hrearrange]
  calc
    ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S,
        ((starRingEnd ℂ) (CyclicBohr.character r x) - 1)‖ ≤
      ‖(S.card : ℂ)⁻¹‖ * ∑ x ∈ S,
        ‖(starRingEnd ℂ) (CyclicBohr.character r x) - 1‖ := by
          rw [norm_mul]
          gcongr
          exact norm_sum_le _ _
    _ ≤ (S.card : ℝ)⁻¹ * ∑ _x ∈ S, delta := by
      have hnormInv : ‖(S.card : ℂ)⁻¹‖ = (S.card : ℝ)⁻¹ := by
        simp [norm_inv, abs_of_pos hcard]
      rw [hnormInv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro x hx
      calc
        ‖(starRingEnd ℂ) (CyclicBohr.character r x) - 1‖ =
            ‖CyclicBohr.character r x - 1‖ := by
              rw [← map_one (starRingEnd ℂ), ← map_sub,
                RCLike.norm_conj]
              simp
        _ =
            ‖1 - CyclicBohr.character r x‖ := by
              simpa only [neg_sub] using
                (norm_neg (1 - CyclicBohr.character r x))
        _ ≤ delta := hcontrol x hx
    _ = delta := by
      simp only [Finset.sum_const, nsmul_eq_mul, norm_inv, Complex.norm_natCast,
        abs_of_pos hcard]
      field_simp

/-! ## Fourier expansions and elementary convolution bounds -/

/-- Convolution by a finite-set probability weight does not increase a
uniform pointwise bound. -/
lemma norm_convolution_probabilityWeight_le
    {S : Finset (ZMod N)} (hS : S.Nonempty) (f : ZMod N → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x, ‖f x‖ ≤ M) (x : ZMod N) :
    ‖CyclicFourier.convolution (probabilityWeight S) f x‖ ≤ M := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  unfold CyclicFourier.convolution average probabilityWeight
  calc
    ‖(N : ℂ)⁻¹ * ∑ y : ZMod N,
        (if y ∈ S then (N : ℂ) / S.card else 0) * f (x - y)‖ ≤
      ‖(N : ℂ)⁻¹‖ * ∑ y ∈ S,
        ‖((N : ℂ) / S.card) * f (x - y)‖ := by
          rw [norm_mul]
          gcongr
          calc
            ‖∑ y : ZMod N,
                (if y ∈ S then (N : ℂ) / S.card else 0) * f (x - y)‖ ≤
              ‖∑ y ∈ S, ((N : ℂ) / S.card) * f (x - y)‖ := by
                congr 1
                simp_rw [ite_mul, zero_mul]
                rw [← Finset.sum_filter]
                simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
                exact le_rfl
            _ ≤ ∑ y ∈ S, ‖((N : ℂ) / S.card) * f (x - y)‖ :=
              norm_sum_le _ _
    _ ≤ ‖(N : ℂ)⁻¹‖ * ∑ _y ∈ S,
        ((N : ℝ) / S.card) * M := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Finset.sum_le_sum
          intro y _hy
          rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hf (x - y)) (by positivity)
    _ = M := by
      simp only [Finset.sum_const, nsmul_eq_mul, norm_inv, Complex.norm_natCast,
        abs_of_pos hN]
      field_simp

/-- Fourier inversion expresses the error of convolution by a kernel as the
sum of its multiplier errors. -/
lemma convolution_sub_eq_sum_fourier
    (mu f : ZMod N → ℂ) (x : ZMod N) :
    CyclicFourier.convolution mu f x - f x =
      ∑ r : ZMod N,
        (CyclicFourier.fourier mu r - 1) * CyclicFourier.fourier f r *
          CyclicBohr.character r x := by
  rw [← fourier_inversion (convolution mu f) x,
    ← fourier_inversion f x, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [fourier_convolution]
  ring

/-- A direct Fourier `L¹` bound for the pointwise smoothing error. -/
lemma norm_convolution_sub_le_sum_fourier
    (mu f : ZMod N → ℂ) (x : ZMod N) :
    ‖CyclicFourier.convolution mu f x - f x‖ ≤
      ∑ r : ZMod N,
        ‖CyclicFourier.fourier mu r - 1‖ * ‖CyclicFourier.fourier f r‖ := by
  rw [convolution_sub_eq_sum_fourier]
  calc
    ‖∑ r : ZMod N,
        (CyclicFourier.fourier mu r - 1) * CyclicFourier.fourier f r *
          CyclicBohr.character r x‖ ≤
      ∑ r : ZMod N,
        ‖(CyclicFourier.fourier mu r - 1) * CyclicFourier.fourier f r *
          CyclicBohr.character r x‖ :=
          norm_sum_le _ _
    _ = ∑ r : ZMod N,
        ‖CyclicFourier.fourier mu r - 1‖ * ‖CyclicFourier.fourier f r‖ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [norm_mul, norm_mul, CyclicBohr.norm_character, mul_one]

/-- Convolution is additive in its right input. -/
lemma convolution_sub_right (mu f g : ZMod N → ℂ) :
    CyclicFourier.convolution mu (fun x ↦ f x - g x) =
      fun x ↦ CyclicFourier.convolution mu f x -
        CyclicFourier.convolution mu g x := by
  funext x
  unfold CyclicFourier.convolution average
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- A probability Fourier multiplier differs from one by at most two. -/
lemma norm_fourier_probabilityWeight_sub_one_le_two
    {S : Finset (ZMod N)} (hS : S.Nonempty) (r : ZMod N) :
    ‖CyclicFourier.fourier (probabilityWeight S) r - 1‖ ≤ 2 := by
  calc
    ‖CyclicFourier.fourier (probabilityWeight S) r - 1‖ ≤
        ‖CyclicFourier.fourier (probabilityWeight S) r‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_fourier_probabilityWeight_le_one hS r) (by norm_num)
    _ = 2 := by norm_num

/-! ## Compatibility with the relative spectrum used by Chang's lemma -/

/-- The normalized Fourier transform is complex-linear. -/
lemma fourier_const_mul (c : ℂ) (f : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (fun x ↦ c * f x) r =
      c * CyclicFourier.fourier f r := by
  unfold CyclicFourier.fourier average
  calc
    (N : ℂ)⁻¹ * ∑ x : ZMod N,
        (starRingEnd ℂ) (CyclicBohr.character r x) * (c * f x) =
      (N : ℂ)⁻¹ * ∑ x : ZMod N,
        c * ((starRingEnd ℂ) (CyclicBohr.character r x) * f x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = c * ((N : ℂ)⁻¹ * ∑ x : ZMod N,
        (starRingEnd ℂ) (CyclicBohr.character r x) * f x) := by
      rw [← Finset.mul_sum]
      ring

/-- The probability weight is density inverse times the ordinary complex
indicator. -/
lemma probabilityWeight_eq_density_inv_mul_indicator
    {S : Finset (ZMod N)} (hS : S.Nonempty) :
    probabilityWeight S = fun x ↦
      ((CyclicChang.density S : ℂ)⁻¹ * CyclicFourier.indicator S x) := by
  funext x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  by_cases hx : x ∈ S
  · simp only [probabilityWeight_apply_mem hx,
      CyclicFourier.indicator_apply_mem hx, mul_one]
    unfold CyclicChang.density
    push_cast
    field_simp
  · simp [probabilityWeight_apply_notMem hx,
      CyclicFourier.indicator_apply_notMem hx]

/-- Fourier coefficients of a set probability weight are the relative
Fourier coefficients of its indicator. -/
lemma fourier_probabilityWeight_eq_density_inv_mul
    {S : Finset (ZMod N)} (hS : S.Nonempty) (r : ZMod N) :
    CyclicFourier.fourier (probabilityWeight S) r =
      (CyclicChang.density S : ℂ)⁻¹ *
        CyclicFourier.fourier (CyclicFourier.indicator S) r := by
  rw [probabilityWeight_eq_density_inv_mul_indicator hS,
    fourier_const_mul]

/-- Norm form of the preceding relative-Fourier identity. -/
lemma norm_fourier_probabilityWeight_eq_div_density
    {S : Finset (ZMod N)} (hS : S.Nonempty) (r : ZMod N) :
    ‖CyclicFourier.fourier (probabilityWeight S) r‖ =
      ‖CyclicFourier.fourier (CyclicFourier.indicator S) r‖ /
        CyclicChang.density S := by
  rw [fourier_probabilityWeight_eq_density_inv_mul hS, norm_mul, norm_inv]
  have hdensity : 0 < CyclicChang.density S := CyclicChang.density_pos hS
  have hdensityNorm : ‖(CyclicChang.density S : ℂ)‖ =
      CyclicChang.density S := by
    calc
      ‖(CyclicChang.density S : ℂ)‖ =
          ‖CyclicChang.density S‖ := Complex.norm_real _
      _ = |CyclicChang.density S| := Real.norm_eq_abs _
      _ = CyclicChang.density S := abs_of_pos hdensity
  rw [hdensityNorm]
  ring

/-- Chang's relative large spectrum is exactly the ordinary large spectrum
of the corresponding probability weight. -/
lemma largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
    {S : Finset (ZMod N)} (hS : S.Nonempty) (eta : ℝ) :
    CyclicFourier.largeSpectrum (probabilityWeight S) eta =
      CyclicChang.relativeLargeSpectrum S eta := by
  ext r
  rw [CyclicFourier.mem_largeSpectrum,
    CyclicChang.mem_relativeLargeSpectrum,
    norm_fourier_probabilityWeight_eq_div_density hS]
  exact le_div_iff₀ (CyclicChang.density_pos hS)

/-! ## Large-spectrum versus tail smoothing -/

/-- The cyclic Fourier-tail smoothing lemma.  The function `G` is a
convolution-power approximation to `F`: its Fourier transform has multiplier
`fourier (probabilityWeight T) ^ k`.  On `Delta` the Bohr set approximately
annihilates every frequency; off `Delta` that convolution power suppresses
the multiplier by `eta ^ k`. -/
theorem norm_probabilityWeight_convolution_sub_le_of_fourier_decay
    {T B Delta : Finset (ZMod N)} (hT : T.Nonempty) (hB : B.Nonempty)
    (F G : ZMod N → ℂ) (k : ℕ) {eta delta epsilon L : ℝ}
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hcontrol : ∀ r ∈ Delta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ delta)
    (htail : ∀ r ∉ Delta,
      ‖CyclicFourier.fourier (probabilityWeight T) r‖ ≤ eta)
    (hGfourier : ∀ r,
      CyclicFourier.fourier G r =
        CyclicFourier.fourier (probabilityWeight T) r ^ k *
          CyclicFourier.fourier F r)
    (happrox : ∀ x, ‖G x - F x‖ ≤ epsilon)
    (hFourierL1 : ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ ≤ L) :
    ∀ x,
      ‖CyclicFourier.convolution (probabilityWeight B) F x - F x‖ ≤
        2 * epsilon + (delta + 2 * eta ^ k) * L := by
  have hkernelApprox (x : ZMod N) :
      ‖CyclicFourier.convolution (probabilityWeight B) F x -
          CyclicFourier.convolution (probabilityWeight B) G x‖ ≤ epsilon := by
    rw [← congrFun (convolution_sub_right (probabilityWeight B) F G) x]
    apply norm_convolution_probabilityWeight_le hB (fun y ↦ F y - G y)
      hepsilon
    intro y
    simpa [norm_sub_rev] using happrox y
  have hmultiplier (r : ZMod N) :
      ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ *
          ‖CyclicFourier.fourier G r‖ ≤
        (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
    rw [hGfourier, norm_mul, norm_pow]
    by_cases hr : r ∈ Delta
    · have hBspec :
          ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ ≤ delta :=
        norm_fourier_probabilityWeight_sub_one_le hB (hcontrol r hr)
      have hTone :
          ‖CyclicFourier.fourier (probabilityWeight T) r‖ ≤ 1 :=
        norm_fourier_probabilityWeight_le_one hT r
      have hpow :
          ‖CyclicFourier.fourier (probabilityWeight T) r‖ ^ k ≤ 1 := by
        simpa using pow_le_pow_left₀ (norm_nonneg _) hTone k
      calc
        ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ *
            (‖CyclicFourier.fourier (probabilityWeight T) r‖ ^ k *
              ‖CyclicFourier.fourier F r‖) ≤
          delta * (1 * ‖CyclicFourier.fourier F r‖) := by
            gcongr
        _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
          calc
            delta * (1 * ‖CyclicFourier.fourier F r‖) =
                delta * ‖CyclicFourier.fourier F r‖ := by ring
            _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ :=
              mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right (by positivity)) (norm_nonneg _)
    · have hBtwo :
          ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ ≤ 2 :=
        norm_fourier_probabilityWeight_sub_one_le_two hB r
      have hpow :
          ‖CyclicFourier.fourier (probabilityWeight T) r‖ ^ k ≤ eta ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) (htail r hr) k
      calc
        ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ *
            (‖CyclicFourier.fourier (probabilityWeight T) r‖ ^ k *
              ‖CyclicFourier.fourier F r‖) ≤
          2 * (eta ^ k * ‖CyclicFourier.fourier F r‖) := by
            gcongr
        _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by
          calc
            2 * (eta ^ k * ‖CyclicFourier.fourier F r‖) =
                (2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ := by ring
            _ ≤ (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ :=
              mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_left hdelta) (norm_nonneg _)
  have hsmoothG (x : ZMod N) :
      ‖CyclicFourier.convolution (probabilityWeight B) G x - G x‖ ≤
        (delta + 2 * eta ^ k) * L := by
    calc
      ‖CyclicFourier.convolution (probabilityWeight B) G x - G x‖ ≤
          ∑ r : ZMod N,
            ‖CyclicFourier.fourier (probabilityWeight B) r - 1‖ *
              ‖CyclicFourier.fourier G r‖ :=
        norm_convolution_sub_le_sum_fourier _ _ _
      _ ≤ ∑ r : ZMod N,
          (delta + 2 * eta ^ k) * ‖CyclicFourier.fourier F r‖ :=
        Finset.sum_le_sum fun r _ ↦ hmultiplier r
      _ = (delta + 2 * eta ^ k) *
          ∑ r : ZMod N, ‖CyclicFourier.fourier F r‖ := by
        rw [Finset.mul_sum]
      _ ≤ (delta + 2 * eta ^ k) * L := by
        exact mul_le_mul_of_nonneg_left hFourierL1 (by positivity)
  intro x
  calc
    ‖CyclicFourier.convolution (probabilityWeight B) F x - F x‖ ≤
        ‖CyclicFourier.convolution (probabilityWeight B) F x -
          CyclicFourier.convolution (probabilityWeight B) G x‖ +
        ‖CyclicFourier.convolution (probabilityWeight B) G x - G x‖ +
        ‖G x - F x‖ := by
      rw [show CyclicFourier.convolution (probabilityWeight B) F x - F x =
          (CyclicFourier.convolution (probabilityWeight B) F x -
            CyclicFourier.convolution (probabilityWeight B) G x) +
          (CyclicFourier.convolution (probabilityWeight B) G x - G x) +
          (G x - F x) by ring]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ epsilon + (delta + 2 * eta ^ k) * L + epsilon := by
      gcongr
      exact hkernelApprox x
      exact hsmoothG x
      exact happrox x
    _ = 2 * epsilon + (delta + 2 * eta ^ k) * L := by ring

end CyclicSpectralSmoothing
end Erdos721
