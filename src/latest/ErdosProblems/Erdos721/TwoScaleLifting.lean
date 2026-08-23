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

import ErdosProblems.Erdos721.QuantitativeBounds

/-!
# Two-scale relative lifting in an odd cyclic group

The integer Kelley--Meka iteration uses two independent regular Bohr scales.
The outer scale makes the current dense set translation-stable, while a
second scale measures the density of the test set and supports the
positive-definite weight.  Keeping these scales separate avoids charging the
Hölder moment for the density of a tiny Bohr set in the whole ambient group.

This file also records the doubling automorphism of an odd cyclic group and
its action on Bohr sets.  Consequently the set of doubled centres has exactly
the same relative density in the doubled Bohr carrier.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicTwoScaleLifting

variable {N : ℕ} [NeZero N]

/-- Multiplication by two is an additive equivalence on a cyclic group of
odd order. -/
noncomputable def doubleEquiv (hN : Odd N) : ZMod N ≃+ ZMod N := by
  let f : ZMod N →+ ZMod N :=
    { toFun := fun x ↦ 2 • x
      map_zero' := by simp
      map_add' := by simp }
  apply AddEquiv.ofBijective f
  have hcoprime : (Nat.card (ZMod N)).Coprime 2 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hN.coprime_two_right
  exact hcoprime.nsmul_right_bijective

@[simp] lemma doubleEquiv_apply (hN : Odd N) (x : ZMod N) :
    doubleEquiv hN x = 2 • x := rfl

/-- The cyclic character pairing commutes with applying the inverse doubling
map in either coordinate. -/
lemma character_doubleEquiv_symm (hN : Odd N) (r x : ZMod N) :
    CyclicBohr.character ((doubleEquiv hN).symm r) x =
      CyclicBohr.character r ((doubleEquiv hN).symm x) := by
  let s := (doubleEquiv hN).symm r
  let y := (doubleEquiv hN).symm x
  have hs : 2 • s = r := by
    have hs' := (doubleEquiv hN).apply_symm_apply r
    change doubleEquiv hN ((doubleEquiv hN).symm r) = r at hs'
    rw [doubleEquiv_apply] at hs'
    simpa only [s] using hs'
  have hy : 2 • y = x := by
    have hy' := (doubleEquiv hN).apply_symm_apply x
    change doubleEquiv hN ((doubleEquiv hN).symm x) = x at hy'
    rw [doubleEquiv_apply] at hy'
    simpa only [y] using hy'
  change CyclicBohr.character s x = CyclicBohr.character r y
  rw [← hs, ← hy]
  simp only [two_nsmul]
  rw [CyclicBohr.character_add, CyclicBohr.character_add_index]

/-- The image of a cyclic Bohr set under the doubling automorphism. -/
noncomputable def doubleBohr (hN : Odd N) (B : CyclicBohr.Set N) :
    CyclicBohr.Set N where
  frequencies := B.frequencies.image (doubleEquiv hN).symm
  radius := B.radius
  radius_nonneg := B.radius_nonneg

@[simp] lemma doubleBohr_radius (hN : Odd N) (B : CyclicBohr.Set N) :
    (doubleBohr hN B).radius = B.radius := rfl

@[simp] lemma doubleBohr_rank (hN : Odd N) (B : CyclicBohr.Set N) :
    (doubleBohr hN B).rank = B.rank := by
  unfold doubleBohr CyclicBohr.Set.rank
  exact Finset.card_image_of_injective _ (doubleEquiv hN).symm.injective

lemma mem_doubleBohr_iff (hN : Odd N) (B : CyclicBohr.Set N)
    (x : ZMod N) :
    x ∈ doubleBohr hN B ↔ (doubleEquiv hN).symm x ∈ B := by
  rw [CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_iff]
  constructor
  · intro hx r hr
    have himage : (doubleEquiv hN).symm r ∈
        B.frequencies.image (doubleEquiv hN).symm :=
      Finset.mem_image.mpr ⟨r, hr, rfl⟩
    simpa [doubleBohr, character_doubleEquiv_symm] using
      hx ((doubleEquiv hN).symm r) himage
  · intro hx r hr
    rw [show (doubleBohr hN B).frequencies =
      B.frequencies.image (doubleEquiv hN).symm by rfl] at hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    simpa [doubleBohr, character_doubleEquiv_symm] using hx s hs

/-- The carrier of the doubled Bohr set is exactly the image of the original
carrier. -/
lemma carrier_doubleBohr (hN : Odd N) (B : CyclicBohr.Set N) :
    (doubleBohr hN B).carrier =
      B.carrier.image (doubleEquiv hN) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · intro hx
    refine ⟨(doubleEquiv hN).symm x, ?_, ?_⟩
    · exact (mem_doubleBohr_iff hN B x).mp hx
    · exact (doubleEquiv hN).apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩
    change (doubleEquiv hN) y ∈ doubleBohr hN B
    rw [mem_doubleBohr_iff]
    rw [(doubleEquiv hN).symm_apply_apply]
    exact hy

lemma card_carrier_doubleBohr (hN : Odd N) (B : CyclicBohr.Set N) :
    (doubleBohr hN B).carrier.card = B.carrier.card := by
  rw [carrier_doubleBohr, Finset.card_image_of_injective]
  exact (doubleEquiv hN).injective

@[simp] lemma doubleBohr_dilate (hN : Odd N) (B : CyclicBohr.Set N)
    (rho : ℝ) :
    doubleBohr hN (B.dilate rho) = (doubleBohr hN B).dilate rho := by
  rfl

/-- Doubling preserves relative density in corresponding Bohr carriers. -/
lemma card_image_double_eq (hN : Odd N) (A : Finset (ZMod N)) :
    (A.image (2 • ·)).card = A.card := by
  apply Finset.card_image_of_injective
  simpa only [← doubleEquiv_apply hN] using (doubleEquiv hN).injective

/-- For a progression-free set, testing its self-convolution only on the
doubles of a nonempty subset still sees exactly the diagonal contribution.
This is the localized version used after simultaneous narrowing. -/
theorem diagonal_correlation_on_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Odd (Fintype.card G)) (A D : Finset G)
    (hD : D.Nonempty) (hDA : D ⊆ A)
    (hAfree : ThreeAPFree (A : Set G)) :
    ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] (D.image (2 • ·))⟫_[ℝ] =
      ((A.card : ℝ) ^ 2)⁻¹ := by
  have hA : A.Nonempty := hD.mono hDA
  simp only [wInner_one_eq_sum, inner_apply', sum_ddconv_mul,
    ← sum_product', RCLike.conj_to_real]
  rw [← diag_union_offDiag univ, sum_union (disjoint_diag_offDiag _),
    sum_diag, ← sum_add_sum_compl D,
    @sum_eq_card_nsmul _ _ _ _ _
      ((A.card : ℝ)⁻¹ * (A.card : ℝ)⁻¹ * (D.card : ℝ)⁻¹),
    nsmul_eq_mul, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero,
    add_zero]
  · have hAcard : (A.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hA
    have hDcard : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hD
    field_simp [hAcard, hDcard]
  · refine fun i hi ↦ not_ne_iff.1 fun h ↦ (mem_offDiag.1 hi).2.2 ?_
    simp_rw [mul_ne_zero_iff, ← mem_support, support_mu, mem_coe,
      mem_image, two_smul] at h
    obtain ⟨b, hbD, hab⟩ := h.2
    have hbA : b ∈ A := hDA hbD
    obtain rfl := hAfree h.1.1 hbA h.1.2 hab.symm
    simpa using hab
  · intro x hxD
    by_cases hxA : x ∈ A
    · have hnot : x + x ∉ D.image (2 • ·) := by
        intro hximage
        obtain ⟨y, hyD, hyx⟩ := Finset.mem_image.mp hximage
        have hinj : Function.Injective (2 • · : G → G) := by
          rw [← Nat.card_eq_fintype_card] at hG
          exact hG.coprime_two_right.nsmul_right_bijective.injective
        have hxy : y = x := by
          apply hinj
          simpa only [two_nsmul] using hyx
        have hxD' : x ∉ D := by simpa using hxD
        apply hxD'
        rwa [← hxy]
      simp [mu_apply, hxA, hnot]
    · simp [mu_apply, hxA]
  · rintro a haD
    have haA : a ∈ A := hDA haD
    simp only [mu_apply, haA, if_true, mul_one, mem_image, mul_ite,
      mul_zero]
    rw [if_pos ⟨a, haD, two_nsmul a⟩]
    congr 2
    rw [Finset.card_image_of_injective]
    rw [← Nat.card_eq_fintype_card] at hG
    exact hG.coprime_two_right.nsmul_right_bijective.injective

/-- Cardinal form of the fixed half-sized correlation gap on a localized
set of centres. -/
theorem half_le_abs_scaled_correlation_on_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Odd (Fintype.card G)) (B A D : Finset G)
    (hD : D.Nonempty) (hDA : D ⊆ A)
    (hAfree : ThreeAPFree (A : Set G))
    (hcard : 2 * B.card ≤ A.card ^ 2) :
    1 / 2 ≤
      |(B.card : ℝ) *
          ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A,
            μ_[ℝ] (D.image (2 • ·))⟫_[ℝ] - 1| := by
  rw [diagonal_correlation_on_subset hG A D hD hDA hAfree]
  have hA : A.Nonempty := hD.mono hDA
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hdiag : (B.card : ℝ) * ((A.card : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv,
      div_le_iff₀ (by positivity : (0 : ℝ) < (A.card : ℝ) ^ 2)]
    have hcardR : (2 : ℝ) * B.card ≤ (A.card : ℝ) ^ 2 := by
      exact_mod_cast hcard
    nlinarith
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Two-scale form of relative Hölder followed by positive-definite lifting.
The current set `A` lives on the outer regular Bohr carrier `B_t`; the test
set `C` has density `gamma` on the independent inner carrier `K_(v-eta)`;
and `S,T` generate the positive-definite weight on the fine perturbation of
that second carrier. -/
theorem large_positiveDefinite_norm_of_two_scale_correlation_gap
    (B K : CyclicBohr.Set N) (A C S T : Finset (ZMod N))
    (m p : ℕ) {t delta v eta alpha gamma epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (hpEven : Even p)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hepsilon0 : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltat : delta < t)
    (hOuterRegular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (heta : 0 < eta) (hetav : eta < v)
    (hInnerRegular :
      (10 * m) * (K.dilate (v + eta)).carrier.card ≤
        (10 * m + 1) * (K.dilate (v - eta)).carrier.card)
    (hA : A.Nonempty) (hC : C.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hAdense : alpha * (B.dilate t).carrier.card ≤ A.card)
    (hCstable : C ⊆ (B.dilate delta).carrier)
    (hCinner : C ⊆ (K.dilate (v - eta)).carrier)
    (hCdense : gamma * (K.dilate (v - eta)).carrier.card ≤ C.card)
    (hgammaFactor : gamma⁻¹ ^ ((p : ℝ)⁻¹) ≤ 2)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (K.dilate (eta / 4)).carrier)
    (hTsub : T ⊆ (K.dilate (eta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ epsilon / 4)
    (hmain : epsilon ≤
      |((B.dilate t).carrier.card : ℝ) *
        ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    epsilon / 8 ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T] := by
  have hstable : ∀ x ∈ C,
      (5 * m) * CyclicBohr.translationDiscrepancy
          (B.dilate t).carrier x ≤ (B.dilate t).carrier.card := by
    intro x hx
    exact CyclicBohr.five_mul_m_translationDiscrepancy_le_card B m hm
      hdelta.le (sub_nonneg.mpr hdeltat.le) hOuterRegular (hCstable hx)
  have hrel :=
    CyclicRelativeLifting.relativeBalance_ddconv_wLpNorm_lower_of_stable
      A C (K.dilate (v - eta)).carrier (B.dilate t) m p hm hp halpha
      hgamma hA hC (K.dilate (v - eta)).carrier_nonempty hAB hAdense
      hCinner hCdense hstable hmain
  rw [wLpNorm_smul] at hrel
  have hcardNorm :
      (↑‖((B.dilate t).carrier.card : ℝ)‖₊ : ℝ) =
        (B.dilate t).carrier.card := by
    rw [Real.nnnorm_of_nonneg (by positivity)]
    rfl
  rw [hcardNorm] at hrel
  have hordinary : epsilon / 4 ≤
      (B.dilate t).carrier.card •
        ‖CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ∗ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier‖_[p,
              μ (K.dilate (v - eta)).carrier] := by
    simp only [nsmul_eq_mul]
    have hprod : gamma⁻¹ ^ ((p : ℝ)⁻¹) *
          (((B.dilate t).carrier.card : ℝ) *
            ‖CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier ∗ᵈ
              CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier‖_[p,
                  μ (K.dilate (v - eta)).carrier]) ≤
        2 * (((B.dilate t).carrier.card : ℝ) *
            ‖CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier ∗ᵈ
              CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier‖_[p,
                  μ (K.dilate (v - eta)).carrier]) := by
      apply mul_le_mul_of_nonneg_right hgammaFactor
      positivity
    nlinarith [hrel.trans hprod]
  have hpositive :=
    CyclicPositiveDefiniteLifting.bohr_ddconv_norm_le_two_mul_dddconv_norm
      K m hm heta hetav hInnerRegular S T hS hT hSsub hTsub
      (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier)
      p hp hpEven
  have hpositiveScaled := nsmul_le_nsmul_right hpositive
    (B.dilate t).carrier.card
  have htargetNonneg : 0 ≤
      (B.dilate t).carrier.card •
        ‖CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T] := by
    positivity
  rw [wLpNorm_nsmul]
  simp only [nsmul_eq_mul] at hordinary hpositiveScaled htargetNonneg ⊢
  nlinarith

end CyclicTwoScaleLifting
end Erdos721
