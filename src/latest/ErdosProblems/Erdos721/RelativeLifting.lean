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

import ErdosProblems.Erdos721.DensityIncrement
import APAP.Prereqs.LpNorm.Weighted

/-!
# Relative convolution estimates on cyclic Bohr sets

This file supplies the elementary regular-Bohr estimates needed to replace
the uniform measure on the whole cyclic group in the density-increment
argument by the normalized indicator of a Bohr carrier.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicRelativeLifting

variable {N : ℕ} [NeZero N]

open CyclicBohr CyclicDensityIncrement

section WeightedHolder

variable {G : Type*} [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- A probability average over a nonempty finite set is bounded by every
finite `L^p` norm with `p ≥ 1`.  This is the weighted form of the elementary
`L¹`--`L^p` comparison used in the relative argument. -/
lemma abs_mu_average_le_wLpNorm
    (C : Finset G) (hC : C.Nonempty) (f : G → ℝ)
    (p : ℕ) (hp : p ≠ 0) :
    |∑ x, μ_[ℝ] C x * f x| ≤ ‖f‖_[p, μ C] := by
  calc
    |∑ x, μ_[ℝ] C x * f x| ≤ ∑ x, μ_[ℝ] C x * |f x| := by
      calc
        _ ≤ ∑ x, |μ_[ℝ] C x * f x| := abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg]
          simp only [mu_apply]
          split_ifs <;> positivity
    _ = ‖f‖_[1, μ C] := by
      rw [wL1Norm_eq_sum_norm]
      apply Finset.sum_congr rfl
      intro x _
      simp [NNReal.coe_mu, NNReal.smul_def, Real.norm_eq_abs]
    _ ≤ ‖f‖_[p, μ C] := by
      apply wLpNorm_mono_right
      · exact_mod_cast sum_mu ℝ≥0 hC
      · norm_cast
        exact Nat.one_le_iff_ne_zero.mpr hp

/-- Restricting a normalized finite-set weight increases an `L^p` norm by
at most the `p`-th root of the reciprocal relative density. -/
lemma wLpNorm_mu_mono_of_subset
    (C D : Finset G) (hC : C.Nonempty) (hD : D.Nonempty)
    (hCD : C ⊆ D) (f : G → ℝ) (p : ℕ) (hp : p ≠ 0) :
    ‖f‖_[p, μ C] ≤
      (((D.card : ℝ) / C.card) ^ ((p : ℝ)⁻¹) : ℝ) * ‖f‖_[p, μ D] := by
  rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp) (by simp),
    wLpNorm_eq_sum_norm (by exact_mod_cast hp) (by simp)]
  simp only [ENNReal.toReal_natCast, NNReal.smul_def, smul_eq_mul,
    Real.norm_eq_abs, NNReal.coe_mu]
  calc
    _ ≤ ((D.card : ℝ) / C.card *
        ∑ i, (↑(μ D i) : ℝ) * |f i| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ ↦ mul_nonneg
          ((mu_nonneg (K := ℝ) (s := C)) i)
          (Real.rpow_nonneg (abs_nonneg _) _)) ?_ (by positivity)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      by_cases hxC : x ∈ C
      · have hxD : x ∈ D := hCD hxC
        simp [mu_apply, hxC, hxD]
        have hCcard : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
        have hDcard : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
        field_simp
        rfl
      · simp only [mu_apply, hxC, if_false, mul_zero]
        by_cases hxD : x ∈ D <;> simp only [rpow_natCast, zero_mul, mul_ite, mul_one, mul_zero, ite_mul]
        positivity
    _ = ((D.card : ℝ) / C.card) ^ ((p : ℝ)⁻¹) *
        (∑ i, (↑(μ D i) : ℝ) * |f i| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹) := by
      exact Real.mul_rpow (by positivity)
        (Finset.sum_nonneg fun i _ ↦ mul_nonneg
          ((mu_nonneg (K := ℝ) (s := D)) i)
          (Real.rpow_nonneg (abs_nonneg _) _))

/-- Relative Hölder lifting.  If `C` occupies at least a `gamma` fraction of
`D`, correlation against the uniform probability measure of `C` is bounded
by the `L^p(μ_D)` norm with the sharp density loss `gamma^(-1/p)`. -/
lemma abs_mu_average_le_density_rpow_mul_wLpNorm
    (C D : Finset G) (hC : C.Nonempty) (hD : D.Nonempty)
    (hCD : C ⊆ D) (f : G → ℝ) (p : ℕ) (hp : p ≠ 0)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hdense : gamma * D.card ≤ C.card) :
    |∑ x, μ_[ℝ] C x * f x| ≤
      gamma⁻¹ ^ ((p : ℝ)⁻¹) * ‖f‖_[p, μ D] := by
  calc
    _ ≤ ‖f‖_[p, μ C] := abs_mu_average_le_wLpNorm C hC f p hp
    _ ≤ (((D.card : ℝ) / C.card) ^ ((p : ℝ)⁻¹) : ℝ) *
        ‖f‖_[p, μ D] := wLpNorm_mu_mono_of_subset C D hC hD hCD f p hp
    _ ≤ gamma⁻¹ ^ ((p : ℝ)⁻¹) * ‖f‖_[p, μ D] := by
      gcongr
      have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
      have hratio : (D.card : ℝ) / C.card ≤ 1 / gamma := by
        rw [div_le_div_iff₀ hCpos hgamma]
        simpa [mul_comm] using hdense
      simpa only [one_div] using hratio

end WeightedHolder

/-- The scalar triangle inequality behind local balancing: if the main term
is separated from one while the two regularity terms are close to one, then
the balanced four-term expansion remains large. -/
lemma abs_balanced_expansion_lower {a b c epsilon delta : ℝ}
    (hmain : epsilon ≤ |a - 1|)
    (hmix : |b - 1| ≤ delta) (hbase : |c - 1| ≤ delta) :
    epsilon - 3 * delta ≤ |a - 2 * b + c| := by
  have hid : a - 1 = (a - 2 * b + c) + 2 * (b - 1) - (c - 1) := by ring
  have htri : |a - 1| ≤ |a - 2 * b + c| + 2 * |b - 1| + |c - 1| := by
    rw [hid]
    calc
      |(a - 2 * b + c) + 2 * (b - 1) - (c - 1)| ≤
          |(a - 2 * b + c) + 2 * (b - 1)| + |c - 1| := abs_sub _ _
      _ ≤ (|a - 2 * b + c| + |2 * (b - 1)|) + |c - 1| := by
        gcongr
        exact abs_add_le _ _
      _ = |a - 2 * b + c| + 2 * |b - 1| + |c - 1| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- The local balanced probability function attached to `A ⊆ B`. -/
noncomputable def relativeBalance
    (A B : Finset (ZMod N)) : ZMod N → ℝ :=
  μ_[ℝ] A - μ_[ℝ] B

/-- Exact four-term expansion of the locally balanced self-convolution. -/
lemma card_mul_inner_relativeBalance_ddconv
    (A B C : Finset (ZMod N)) :
    (B.card : ℝ) *
        ⟪relativeBalance A B ∗ᵈ relativeBalance A B, μ_[ℝ] C⟫_[ℝ] =
      (B.card : ℝ) * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] -
        2 * ((B.card : ℝ) * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ]) +
        (B.card : ℝ) * ⟪μ_[ℝ] B ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ] := by
  simp only [relativeBalance, sub_ddconv, ddconv_sub, wInner_sub_left]
  rw [ddconv_comm (μ_[ℝ] B) (μ_[ℝ] A)]
  ring

/-- The main local correlation gap survives subtraction of the carrier
measure, up to the three regularity errors in the four-term expansion. -/
theorem relativeBalance_ddconv_correlation_lower
    (A B C : Finset (ZMod N)) {epsilon delta : ℝ}
    (hmain : epsilon ≤
      |(B.card : ℝ) * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|)
    (hmix : |(B.card : ℝ) *
      ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ] - 1| ≤ delta)
    (hbase : |(B.card : ℝ) *
      ⟪μ_[ℝ] B ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ] - 1| ≤ delta) :
    epsilon - 3 * delta ≤
      |(B.card : ℝ) *
        ⟪relativeBalance A B ∗ᵈ relativeBalance A B, μ_[ℝ] C⟫_[ℝ]| := by
  rw [card_mul_inner_relativeBalance_ddconv]
  exact abs_balanced_expansion_lower hmain hmix hbase

/-- Relative Hölder converts the surviving balanced correlation into a
weighted norm lower bound on the carrier `D`. -/
theorem relativeBalance_ddconv_wLpNorm_lower
    (A B C D : Finset (ZMod N)) (hC : C.Nonempty) (hD : D.Nonempty)
    (hCD : C ⊆ D) (p : ℕ) (hp : p ≠ 0)
    {gamma epsilon delta : ℝ} (hgamma : 0 < gamma)
    (hCdense : gamma * D.card ≤ C.card)
    (hmain : epsilon ≤
      |(B.card : ℝ) * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|)
    (hmix : |(B.card : ℝ) *
      ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ] - 1| ≤ delta)
    (hbase : |(B.card : ℝ) *
      ⟪μ_[ℝ] B ∗ᵈ μ_[ℝ] B, μ_[ℝ] C⟫_[ℝ] - 1| ≤ delta) :
    epsilon - 3 * delta ≤
      gamma⁻¹ ^ ((p : ℝ)⁻¹) *
        ‖(B.card : ℝ) •
          (relativeBalance A B ∗ᵈ relativeBalance A B)‖_[p, μ D] := by
  let f : ZMod N → ℝ :=
    (B.card : ℝ) • (relativeBalance A B ∗ᵈ relativeBalance A B)
  have havg :
      |∑ x, μ_[ℝ] C x * f x| =
        |(B.card : ℝ) *
          ⟪relativeBalance A B ∗ᵈ relativeBalance A B, μ_[ℝ] C⟫_[ℝ]| := by
    congr 1
    rw [wInner_one_eq_sum]
    simp only [f, Pi.smul_apply, smul_eq_mul, Real.inner_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    epsilon - 3 * delta ≤
        |(B.card : ℝ) *
          ⟪relativeBalance A B ∗ᵈ relativeBalance A B, μ_[ℝ] C⟫_[ℝ]| :=
      relativeBalance_ddconv_correlation_lower A B C hmain hmix hbase
    _ = |∑ x, μ_[ℝ] C x * f x| := havg.symm
    _ ≤ gamma⁻¹ ^ ((p : ℝ)⁻¹) * ‖f‖_[p, μ D] :=
      abs_mu_average_le_density_rpow_mul_wLpNorm C D hC hD hCD f p hp
        hgamma hCdense

/-- Convolution of two finite probability measures counts the corresponding
translated slice, with one cardinality denominator for each measure. -/
lemma mu_ddconv_mu_apply_eq_card_translatedSlice
    (A B : Finset (ZMod N)) (hA : A.Nonempty) (hB : B.Nonempty)
    (x : ZMod N) :
    (μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x =
      (CyclicBohr.translatedSlice A B x).card /
        ((A.card : ℝ) * B.card) := by
  let T := CyclicBohr.translatedSlice A B x
  have hpoint (y : ZMod N) :
      μ_[ℝ] A y * μ_[ℝ] B (x - y) =
        if y ∈ T then ((A.card : ℝ) * B.card)⁻¹ else 0 := by
    by_cases hyA : y ∈ A <;> by_cases hyB : x - y ∈ B <;>
      simp [mu_apply, T, CyclicBohr.translatedSlice, hyA, hyB, mul_inv, mul_comm]
  rw [ddconv_eq_sum_sub']
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hAcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  have hBcard : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hB
  dsimp only [T]
  field_simp
  simp

/-- At the origin, convolution with the probability measure of a symmetric
carrier containing `A` equals the reciprocal carrier cardinality. -/
lemma mu_ddconv_mu_apply_zero_eq_inv_card
    (A : Finset (ZMod N)) (B : CyclicBohr.Set N) (hA : A.Nonempty)
    (hAB : A ⊆ B.carrier) :
    (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) 0 = (B.carrier.card : ℝ)⁻¹ := by
  rw [mu_ddconv_mu_apply_eq_card_translatedSlice A B.carrier hA
    B.carrier_nonempty]
  have hslice : CyclicBohr.translatedSlice A B.carrier 0 = A := by
    apply Finset.Subset.antisymm (translatedSlice_subset_left A B.carrier 0)
    intro y hy
    rw [CyclicBohr.translatedSlice, Finset.mem_filter]
    refine ⟨hy, ?_⟩
    have hneg : -y ∈ B.carrier := B.neg_mem_iff y |>.2 (hAB hy)
    simpa only [zero_sub] using hneg
  rw [hslice]
  have hAcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  field_simp

/-- Points of `A` missed by a translated carrier are contained in the
carrier's translation symmetric difference. -/
lemma card_sub_card_translatedSlice_le_translationDiscrepancy
    (A : Finset (ZMod N)) (B : CyclicBohr.Set N) (hAB : A ⊆ B.carrier)
    (x : ZMod N) :
    A.card - (CyclicBohr.translatedSlice A B.carrier x).card ≤
      translationDiscrepancy B.carrier x := by
  have hslice : CyclicBohr.translatedSlice A B.carrier x ⊆ A :=
    translatedSlice_subset_left A B.carrier x
  rw [← Finset.card_sdiff_of_subset hslice]
  have hsub : A \ CyclicBohr.translatedSlice A B.carrier x ⊆
      B.carrier \ translateFinset B.carrier x := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    have hyB : y ∈ B.carrier := hAB hy.1
    refine ⟨hyB, ?_⟩
    intro hytrans
    have hyminus : y - x ∈ B.carrier := mem_translateFinset.mp hytrans
    have hxy : x - y ∈ B.carrier := by
      have := B.neg_mem_iff (y - x) |>.2 hyminus
      rw [neg_sub] at this
      exact this
    exact hy.2 (by
      rw [CyclicBohr.translatedSlice, Finset.mem_filter]
      exact ⟨hy.1, hxy⟩)
  calc
    #(A \ CyclicBohr.translatedSlice A B.carrier x) ≤
        #(B.carrier \ translateFinset B.carrier x) := Finset.card_le_card hsub
    _ ≤ #(B.carrier \ translateFinset B.carrier x) +
        #(translateFinset B.carrier x \ B.carrier) := Nat.le_add_right _ _
    _ = translationDiscrepancy B.carrier x := rfl

/-- Pointwise regularity estimate for a mixed convolution.  The error is
measured relative to its value `1/|B|` at the origin. -/
theorem abs_card_mul_mu_ddconv_mu_sub_one_le
    (A : Finset (ZMod N)) (B : CyclicBohr.Set N)
    (hA : A.Nonempty) (hAB : A ⊆ B.carrier) (x : ZMod N) :
    |(B.carrier.card : ℝ) *
        (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1| ≤
      (translationDiscrepancy B.carrier x : ℝ) / A.card := by
  rw [mu_ddconv_mu_apply_eq_card_translatedSlice A B.carrier hA
    B.carrier_nonempty]
  have hslice := translatedSlice_subset_left A B.carrier x
  have hcardle := Finset.card_le_card hslice
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBcard : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.card_pos
  have hdiffNat :=
    card_sub_card_translatedSlice_le_translationDiscrepancy A B hAB x
  have hdiff :
      (A.card : ℝ) - (CyclicBohr.translatedSlice A B.carrier x).card ≤
        translationDiscrepancy B.carrier x := by exact_mod_cast hdiffNat
  have hslicecard :
      (0 : ℝ) ≤ (CyclicBohr.translatedSlice A B.carrier x).card := by positivity
  have hnonpos :
      (B.carrier.card : ℝ) *
          ((CyclicBohr.translatedSlice A B.carrier x).card /
            ((A.card : ℝ) * B.carrier.card)) - 1 ≤ 0 := by
    rw [sub_nonpos]
    calc
      (B.carrier.card : ℝ) *
          ((CyclicBohr.translatedSlice A B.carrier x).card /
            ((A.card : ℝ) * B.carrier.card)) =
          (CyclicBohr.translatedSlice A B.carrier x).card / A.card := by
            field_simp
      _ ≤ 1 := (div_le_one hAcard).2 (by exact_mod_cast hcardle)
  rw [abs_of_nonpos hnonpos]
  calc
    -((B.carrier.card : ℝ) *
          ((CyclicBohr.translatedSlice A B.carrier x).card /
            ((A.card : ℝ) * B.carrier.card)) - 1) =
        ((A.card : ℝ) -
          (CyclicBohr.translatedSlice A B.carrier x).card) / A.card := by
      field_simp
      ring
    _ ≤ (translationDiscrepancy B.carrier x : ℝ) / A.card :=
      (div_le_div_iff_of_pos_right hAcard).2 hdiff

/-- A relative-density lower bound converts carrier translation stability
into a pointwise mixed-convolution estimate. -/
theorem abs_card_mul_mu_ddconv_mu_sub_one_le_of_dense
    (A : Finset (ZMod N)) (B : CyclicBohr.Set N) (m : ℕ) {alpha : ℝ}
    (hm : 0 < m) (halpha : 0 < alpha) (hA : A.Nonempty)
    (hAB : A ⊆ B.carrier)
    (hAdense : alpha * B.carrier.card ≤ A.card)
    {x : ZMod N}
    (hstable : (5 * m) * translationDiscrepancy B.carrier x ≤
      B.carrier.card) :
    |(B.carrier.card : ℝ) *
        (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1| ≤
      1 / ((5 * m : ℕ) * alpha) := by
  refine (abs_card_mul_mu_ddconv_mu_sub_one_le A B hA hAB x).trans ?_
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hmR : (0 : ℝ) < (5 * m : ℕ) := by positivity
  have hstableR :
      ((5 * m : ℕ) : ℝ) * translationDiscrepancy B.carrier x ≤
        B.carrier.card := by exact_mod_cast hstable
  have hdenseR : alpha * (B.carrier.card : ℝ) ≤ A.card := by
    exact_mod_cast hAdense
  rw [div_le_div_iff₀ hAcard (mul_pos hmR halpha)]
  calc
    (translationDiscrepancy B.carrier x : ℝ) *
        (((5 * m : ℕ) : ℝ) * alpha) =
        alpha * (((5 * m : ℕ) : ℝ) *
          translationDiscrepancy B.carrier x) := by ring
    _ ≤ alpha * B.carrier.card :=
      mul_le_mul_of_nonneg_left hstableR halpha.le
    _ ≤ A.card := hdenseR
    _ = 1 * (A.card : ℝ) := by ring

/-- Averaging the preceding pointwise estimate against a probability measure
supported on the stable inner dilate preserves the same error. -/
theorem abs_card_mul_mixed_inner_sub_one_le_of_dense
    (A C : Finset (ZMod N)) (B : CyclicBohr.Set N) (m : ℕ)
    {alpha : ℝ} (hm : 0 < m) (halpha : 0 < alpha)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAB : A ⊆ B.carrier)
    (hAdense : alpha * B.carrier.card ≤ A.card)
    (hstable : ∀ x ∈ C,
      (5 * m) * translationDiscrepancy B.carrier x ≤ B.carrier.card) :
    |(B.carrier.card : ℝ) *
        ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier, μ_[ℝ] C⟫_[ℝ] - 1| ≤
      1 / ((5 * m : ℕ) * alpha) := by
  let e : ℝ := 1 / ((5 * m : ℕ) * alpha)
  have he : 0 ≤ e := by positivity
  have hpoint : ∀ x ∈ C,
      |(B.carrier.card : ℝ) *
          (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1| ≤ e := by
    intro x hx
    exact abs_card_mul_mu_ddconv_mu_sub_one_le_of_dense A B m hm halpha hA
      hAB hAdense (hstable x hx)
  have hsumMu : ∑ x : ZMod N, μ_[ℝ] C x = 1 := by simpa using sum_mu ℝ hC
  have hid :
      (B.carrier.card : ℝ) *
          ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier, μ_[ℝ] C⟫_[ℝ] - 1 =
        ∑ x ∈ C, μ_[ℝ] C x *
          ((B.carrier.card : ℝ) *
            (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1) := by
    have hrhs :
        ∑ x ∈ C, μ_[ℝ] C x *
            ((B.carrier.card : ℝ) *
              (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1) =
          ∑ x : ZMod N, μ_[ℝ] C x *
            ((B.carrier.card : ℝ) *
              (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1) := by
      apply Finset.sum_subset (Finset.subset_univ C)
      intro x _hx hxC
      simp [mu_apply, hxC]
    rw [wInner_one_eq_sum]
    simp only [Real.inner_apply]
    calc
      (B.carrier.card : ℝ) *
          (∑ x : ZMod N,
            (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x * μ_[ℝ] C x) - 1 =
          (B.carrier.card : ℝ) *
            (∑ x : ZMod N,
              (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x * μ_[ℝ] C x) -
            ∑ x : ZMod N, μ_[ℝ] C x := by rw [hsumMu]
      _ = ∑ x : ZMod N,
          ((B.carrier.card : ℝ) *
              ((μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x * μ_[ℝ] C x) -
            μ_[ℝ] C x) := by
        rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ = ∑ x : ZMod N, μ_[ℝ] C x *
          ((B.carrier.card : ℝ) *
            (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1) := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = ∑ x ∈ C, μ_[ℝ] C x *
          ((B.carrier.card : ℝ) *
            (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1) := hrhs.symm
  rw [hid]
  calc
    |∑ x ∈ C, μ_[ℝ] C x *
        ((B.carrier.card : ℝ) *
          (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1)| ≤
        ∑ x ∈ C, |μ_[ℝ] C x *
          ((B.carrier.card : ℝ) *
            (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) x - 1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ C, μ_[ℝ] C x * e := by
      gcongr with x hx
      have hmu : (0 : ℝ) ≤ μ_[ℝ] C x := by
        simp [mu_apply, hx]
      rw [abs_mul, abs_of_nonneg hmu]
      exact mul_le_mul_of_nonneg_left (hpoint x hx) hmu
    _ = e := by
      rw [← Finset.sum_mul]
      have hmuFilter : ∑ x ∈ C, μ_[ℝ] C x = 1 := by
        calc
          ∑ x ∈ C, μ_[ℝ] C x = ∑ x : ZMod N, μ_[ℝ] C x := by
            apply Finset.sum_subset (Finset.subset_univ C)
            intro x _hx hxC
            simp [mu_apply, hxC]
          _ = 1 := hsumMu
      rw [hmuFilter, one_mul]

/-- Fully packaged relative Hölder lifting on a stable Bohr carrier.  The
mixed and carrier-carrier terms are discharged by translation regularity;
only the main correlation gap remains as input. -/
theorem relativeBalance_ddconv_wLpNorm_lower_of_stable
    (A C D : Finset (ZMod N)) (B : CyclicBohr.Set N)
    (m p : ℕ) {alpha gamma epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hA : A.Nonempty) (hC : C.Nonempty)
    (hD : D.Nonempty) (hAB : A ⊆ B.carrier)
    (hAdense : alpha * B.carrier.card ≤ A.card)
    (hCD : C ⊆ D) (hCdense : gamma * D.card ≤ C.card)
    (hstable : ∀ x ∈ C,
      (5 * m) * translationDiscrepancy B.carrier x ≤ B.carrier.card)
    (hmain : epsilon ≤
      |(B.carrier.card : ℝ) *
        ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    epsilon - 3 * (1 / ((5 * m : ℕ) * alpha)) ≤
      gamma⁻¹ ^ ((p : ℝ)⁻¹) *
        ‖(B.carrier.card : ℝ) •
          (relativeBalance A B.carrier ∗ᵈ
            relativeBalance A B.carrier)‖_[p, μ D] := by
  have hmix := abs_card_mul_mixed_inner_sub_one_le_of_dense
    A C B m hm halpha hA hC hAB hAdense hstable
  have hAcardle : A.card ≤ B.carrier.card := Finset.card_le_card hAB
  have hAcardleR : (A.card : ℝ) ≤ B.carrier.card := by exact_mod_cast hAcardle
  have hAdenseR : alpha * (B.carrier.card : ℝ) ≤ A.card := by
    exact_mod_cast hAdense
  have hBcard : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.card_pos
  have halphaOne : alpha ≤ 1 := by nlinarith
  have hbaseRaw := abs_card_mul_mixed_inner_sub_one_le_of_dense
    B.carrier C B m hm (by norm_num : (0 : ℝ) < 1)
    B.carrier_nonempty hC (by rfl) (by simp) hstable
  have hdenomPos : (0 : ℝ) < ((5 * m : ℕ) : ℝ) * alpha := by positivity
  have hdenomLe : ((5 * m : ℕ) : ℝ) * alpha ≤ (5 * m : ℕ) := by
    nlinarith [show (0 : ℝ) ≤ (5 * m : ℕ) by positivity]
  have hbase :
      |(B.carrier.card : ℝ) *
          ⟪μ_[ℝ] B.carrier ∗ᵈ μ_[ℝ] B.carrier,
            μ_[ℝ] C⟫_[ℝ] - 1| ≤
        1 / ((5 * m : ℕ) * alpha) := by
    refine hbaseRaw.trans ?_
    simpa only [mul_one] using one_div_le_one_div_of_le hdenomPos hdenomLe
  exact relativeBalance_ddconv_wLpNorm_lower A B.carrier C D hC hD hCD p hp
    hgamma hCdense hmain hmix hbase

/-- Fine regularization packaged in the form consumed by relative Hölder
lifting: every probability measure supported on the inner perturbation sees
the mixed convolution with the center carrier as approximately constant. -/
theorem exists_regular_mixed_inner_control
    (B : CyclicBohr.Set N) (m : ℕ) (hB : 0 < B.radius)
    (hrank : 0 < B.rank) (hm : 0 < m) :
    ∃ t delta : ℝ,
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (B.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      ∀ (A C : Finset (ZMod N)) {alpha : ℝ},
        0 < alpha → A.Nonempty → C.Nonempty →
        A ⊆ (B.dilate t).carrier →
        alpha * (B.dilate t).carrier.card ≤ A.card →
        C ⊆ (B.dilate delta).carrier →
        |((B.dilate t).carrier.card : ℝ) *
            ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] (B.dilate t).carrier,
              μ_[ℝ] C⟫_[ℝ] - 1| ≤
          1 / ((5 * m : ℕ) * alpha) := by
  obtain ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
      hregular⟩ := CyclicBohr.exists_fixed_regular_scale_fine B m hB hrank hm
  refine ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat, ?_⟩
  intro A C alpha halpha hA hC hAB hAdense hCsub
  apply abs_card_mul_mixed_inner_sub_one_le_of_dense A C (B.dilate t) m hm
    halpha hA hC hAB hAdense
  intro x hx
  exact CyclicBohr.five_mul_m_translationDiscrepancy_le_card B m hm hdelta.le
    (sub_nonneg.mpr hdeltat.le) hregular (hCsub hx)

end CyclicRelativeLifting
end Erdos721
