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

import ErdosProblems.Erdos721.LocalSifting

/-!
# The local unbalancing--sifting package

This file combines the checked local unbalancing theorem with averaging of
the positive-definite Bohr weight and unconditional dependent random choice.
It is the local counterpart of the global package in
`DensityIncrementIteration`.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalDensityIncrement

variable {N : ℕ} [NeZero N]

/-- The purely algebraic tail after a translated pair with a large weighted
norm has been selected. -/
theorem sifting_from_large_reflected_norm
    (A S T : Finset (ZMod N)) (scale q : ℕ) (x : ZMod N)
    {alpha epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (halpha : 0 < alpha) (hscale0 : 0 < scale)
    (hA : A.Nonempty) (hS : S.Nonempty) (hT : T.Nonempty)
    (hx : x ∈ S + T) (hqEven : Even q) (hq2 : 2 ≤ q)
    (hAdense : alpha * scale ≤ A.card)
    (hqexp : (epsilon / 16)⁻¹ * Real.log (8 / (epsilon / 32)) ≤ q)
    (hnormPair :
      1 + epsilon / 4 ≤ scale •
        ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
          μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)]) :
    ∃ (A₁ A₂ U : Finset (ZMod N)),
      A₁ ⊆ S ∧ A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U = s q (epsilon / 16) S
        (CyclicLocalSifting.reflectedTranslate T x) A ∧
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₂.card : ℝ) / T.card ∧
      ∀ y ∈ U,
        1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
  obtain ⟨A₁, hA₁S, A₂, hA₂T, hmass, hA₁card, hA₂card⟩ :=
    CyclicLocalSifting.sifting_total_on_reflectedTranslate S T A hx
      (by positivity) (by linarith) (by positivity) hqEven hq2 hqexp hA
  let U : Finset (ZMod N) :=
    s q (epsilon / 16) S
      (CyclicLocalSifting.reflectedTranslate T x) A
  have hscaleR : (0 : ℝ) < scale := by exact_mod_cast hscale0
  have hscale : alpha ≤
      ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
          μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)] * A.card := by
    have hdenseR : alpha * (scale : ℝ) ≤ A.card := by
      exact_mod_cast hAdense
    have hnormOne : 1 ≤ (scale : ℝ) *
        ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
          μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)] := by
      simpa only [nsmul_eq_mul] using hnormPair.trans' (by linarith)
    have hnormLower : (scale : ℝ)⁻¹ ≤
        ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
          μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)] := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hscaleR).2 (by simpa [mul_comm] using hnormOne)
    calc
      alpha ≤ (scale : ℝ)⁻¹ * A.card := by
        rw [inv_mul_eq_div, le_div_iff₀ hscaleR]
        simpa [mul_comm] using hdenseR
      _ ≤ _ := by gcongr
  have hA₁dense : (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
      (A₁.card : ℝ) / S.card := by
    apply (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hscale (2 * q)) (by positivity)).trans
    rw [mul_pow]
    simpa only [mul_assoc] using hA₁card
  have hA₂dense : (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
      (A₂.card : ℝ) / T.card := by
    apply (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hscale (2 * q)) (by positivity)).trans
    rw [mul_pow]
    simpa only [mul_assoc] using hA₂card
  have hhigh : ∀ y ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
    intro y hy
    have hy' :
        (1 - epsilon / 16) *
            ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
              μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)] <
          (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
      have hyU : y ∈ s (q : ℝ≥0) (epsilon / 16) S
          (CyclicLocalSifting.reflectedTranslate T x) A := by
        simpa [U] using hy
      have hyraw := (mem_s' (p := (q : ℝ≥0))
        (ε := epsilon / 16) (B₁ := S)
        (B₂ := CyclicLocalSifting.reflectedTranslate T x) (A := A)).1 hyU
      rw [ENNReal.coe_natCast] at hyraw
      exact hyraw
    have hfactor : 1 + epsilon / 8 ≤
        (1 - epsilon / 16) * (1 + epsilon / 4) := by
      have hprod : 0 ≤ epsilon * (4 - epsilon) :=
        mul_nonneg hepsilon0.le (by linarith)
      nlinarith
    calc
      1 + epsilon / 8 ≤ (1 - epsilon / 16) * (1 + epsilon / 4) := hfactor
      _ ≤ (1 - epsilon / 16) *
          (scale • ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
            μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)]) := by
        gcongr
        linarith
      _ = scale • ((1 - epsilon / 16) *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
            μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)]) :=
        mul_smul_comm ..
      _ ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
        exact nsmul_le_nsmul_right hy'.le _
  refine ⟨A₁, A₂, U, hA₁S, hA₂T, rfl, ?_, hA₁dense, hA₂dense,
    hhigh⟩
  simpa [U] using hmass

/-- Relative Hölder lifting and the positive-definite Bohr comparison turn a
local correlation discrepancy into the exact large norm consumed by local
unbalancing.  Constants are deliberately slack so that all regularity errors
are explicit. -/
theorem large_positiveDefinite_norm_of_local_correlation_gap
    (B : CyclicBohr.Set N) (A C S T : Finset (ZMod N)) (m p : ℕ)
    {t delta alpha gamma epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (hpEven : Even p)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hepsilon0 : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hC : C.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hAdense : alpha * (B.dilate t).carrier.card ≤ A.card)
    (hCinner : C ⊆ (B.dilate (t - delta)).carrier)
    (hCsmall : C ⊆ (B.dilate delta).carrier)
    (hCdense : gamma * (B.dilate (t - delta)).carrier.card ≤ C.card)
    (hgammaFactor : gamma⁻¹ ^ ((p : ℝ)⁻¹) ≤ 2)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ epsilon / 32)
    (hmain : epsilon ≤
      |((B.dilate t).carrier.card : ℝ) *
        ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    epsilon / 8 ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T] := by
  have hinner : 0 ≤ t - delta := sub_nonneg.mpr hdeltat.le
  have hstable : ∀ x ∈ C,
      (5 * m) * CyclicBohr.translationDiscrepancy
          (B.dilate t).carrier x ≤ (B.dilate t).carrier.card := by
    intro x hx
    exact CyclicBohr.five_mul_m_translationDiscrepancy_le_card B m hm
      hdelta.le hinner hregular (hCsmall hx)
  have hrel :=
    CyclicRelativeLifting.relativeBalance_ddconv_wLpNorm_lower_of_stable
      A C (B.dilate (t - delta)).carrier (B.dilate t) m p hm hp halpha
      hgamma hA hC (B.dilate (t - delta)).carrier_nonempty hAB hAdense
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
            (B.dilate t).carrier‖_[p, μ (B.dilate (t - delta)).carrier] := by
    simp only [nsmul_eq_mul]
    have hprod : gamma⁻¹ ^ ((p : ℝ)⁻¹) *
          (((B.dilate t).carrier.card : ℝ) *
            ‖CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ∗ᵈ
              CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier‖_[p,
                  μ (B.dilate (t - delta)).carrier]) ≤
        2 * (((B.dilate t).carrier.card : ℝ) *
            ‖CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ∗ᵈ
              CyclicRelativeLifting.relativeBalance A
                (B.dilate t).carrier‖_[p,
                  μ (B.dilate (t - delta)).carrier]) := by
      apply mul_le_mul_of_nonneg_right hgammaFactor
      positivity
    nlinarith [hrel.trans hprod]
  have hpositive :=
    CyclicPositiveDefiniteLifting.bohr_ddconv_norm_le_two_mul_dddconv_norm
      B m hm hdelta hdeltat hregular S T hS hT hSsub hTsub
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

/-- A large unbalanced correlation norm against a positive-definite nested
Bohr weight produces two dense auxiliary sets whose difference convolution
is concentrated on a pointwise-high self-correlation set. -/
theorem unbalancing_sifting_of_large_positiveDefinite_norm
    (B : CyclicBohr.Set N) (A S T : Finset (ZMod N)) (m p : ℕ)
    {t delta alpha epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (halpha : 0 < alpha)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hAB : A ⊆ (B.dilate t).carrier)
    (hAdense : alpha * (B.dilate t).carrier.card ≤ A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T]) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U : Finset (ZMod N)),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      0 < q ∧ Even q ∧ x ∈ S + T ∧
      A₁ ⊆ S ∧ A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U = s q (epsilon / 16) S
        (CyclicLocalSifting.reflectedTranslate T x) A ∧
      1 - epsilon / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₂.card : ℝ) / T.card ∧
      ∀ y ∈ U,
        1 + epsilon / 8 ≤
          (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
  let nu : ZMod N → ℝ≥0 :=
    CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T
  let root : ZMod N → ℂ :=
    CyclicPositiveDefiniteLifting.positiveDefiniteRoot S T
  have hroot : root ○ᵈ root = fun x ↦ ((nu x : ℝ) : ℂ) := by
    exact CyclicPositiveDefiniteLifting.positiveDefiniteRoot_factor S T
  have hnu : ∑ x, nu x = 1 :=
    CyclicPositiveDefiniteLifting.positiveDefiniteWeight_sum S T hS hT
  have hdeltaFour : 0 ≤ delta / 4 :=
    div_nonneg hdelta (by norm_num)
  have hnusupport : Function.support nu ⊆
      ((B.dilate delta).carrier : Set (ZMod N)) := by
    simpa only [nu, abs_of_nonneg hdelta,
      abs_of_nonneg hdeltaFour,
      show 4 * (delta / 4) = delta by ring] using
      CyclicPositiveDefiniteLifting.positiveDefiniteWeight_support_subset_dilate
        B (show 0 ≤ delta / 4 by positivity) S T hSsub hTsub
  obtain ⟨p', hp'upper, hnormp'⟩ :=
    CyclicLocalUnbalancing.bohr_unbalancing B A m p hm hp halpha
      hepsilon0 hepsilon1.le hdelta hinner hregular hA hAB hAdense
      nu root hroot hnu hnusupport herror hlarge
  have hp'0 : p' ≠ 0 := by
    intro hp'zero
    subst p'
    simp at hnormp'
    linarith
  let q : ℕ := max (2 * p')
    (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊)
  have hlog : 0 < Real.log (256 / epsilon) := by
    apply Real.log_pos
    exact (one_lt_div hepsilon0).2 (hepsilon1.trans (by norm_num))
  have hceil : 0 < ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊ := by
    exact Nat.ceil_pos.2 (mul_pos (inv_pos.2 hepsilon0) hlog)
  have hq0 : 0 < q := by
    unfold q
    positivity
  have hqEven : Even q := by
    unfold q
    grind
  have hp'q : p' ≤ q := by
    unfold q
    grw [← le_max_left]
    omega
  have hnuENN : ∑ y, ((nu y : ℝ≥0) : ℝ≥0∞) = 1 := by
    exact_mod_cast hnu
  have hp'qENN : (p' : ℝ≥0∞) ≤ q := by exact_mod_cast hp'q
  have hnormq :
      1 + epsilon / 4 ≤
        (B.dilate t).carrier.card •
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q, nu] := by
    apply hnormp'.trans
    exact nsmul_le_nsmul_right
      (wLpNorm_mono_right hnuENN hp'qENN
        (μ_[ℝ] A ○ᵈ μ_[ℝ] A)) _
  obtain ⟨x, hx, hpair⟩ :=
    CyclicLocalSifting.exists_reflectedTranslate_wLpNorm_ge S T hS hT
      (μ_[ℝ] A ○ᵈ μ_[ℝ] A) q hq0.ne'
  have hnormPair :
      1 + epsilon / 4 ≤
        (B.dilate t).carrier.card •
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q,
            μ S ○ᵈ μ (CyclicLocalSifting.reflectedTranslate T x)] :=
    hnormq.trans (nsmul_le_nsmul_right hpair _)
  have hqexp :
      (epsilon / 16)⁻¹ * Real.log (8 / (epsilon / 32)) ≤ q := by
    have hceilLe : epsilon⁻¹ * Real.log (256 / epsilon) ≤
        ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊ := by
      exact_mod_cast Nat.le_ceil (epsilon⁻¹ * Real.log (256 / epsilon))
    calc
      (epsilon / 16)⁻¹ * Real.log (8 / (epsilon / 32)) =
          2 ^ 4 * (epsilon⁻¹ * Real.log (256 / epsilon)) := by
        have hinv : (epsilon / 16)⁻¹ = 16 * epsilon⁻¹ := by
          field_simp
        have hdiv : 8 / (epsilon / 32) = 256 / epsilon := by
          field_simp
          norm_num
        rw [hinv, hdiv]
        norm_num
        ring
      _ ≤ 2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊ := by
        gcongr
      _ ≤ q := by
        unfold q
        exact_mod_cast le_max_right (2 * p')
          (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊)
  obtain ⟨A₁, A₂, U, hA₁S, hA₂T, hU, hmass, hA₁dense, hA₂dense,
      hhigh⟩ :=
    sifting_from_large_reflected_norm A S T (B.dilate t).carrier.card q x
      hepsilon0 hepsilon1 halpha (B.dilate t).card_pos hA hS hT hx hqEven
      (by omega) hAdense hqexp hnormPair
  exact ⟨p', q, x, A₁, A₂, U, hp'upper, rfl, hq0, hqEven, hx,
    hA₁S, hA₂T, hU, hmass, hA₁dense, hA₂dense, hhigh⟩

/-- The complete local correlation-gap-to-sifting implication.  This is the
construction-level form of the first half of the Kelley--Meka density
increment: relative Hölder, positive-definite lifting, unbalancing, averaging,
and dependent random choice are all discharged. -/
theorem local_correlation_gap_sifting
    (B : CyclicBohr.Set N) (A C S T : Finset (ZMod N)) (m p : ℕ)
    {t delta alpha gamma epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (hpEven : Even p)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hC : C.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hAdense : alpha * (B.dilate t).carrier.card ≤ A.card)
    (hCinner : C ⊆ (B.dilate (t - delta)).carrier)
    (hCsmall : C ⊆ (B.dilate delta).carrier)
    (hCdense : gamma * (B.dilate (t - delta)).carrier.card ≤ C.card)
    (hgammaFactor : gamma⁻¹ ^ ((p : ℝ)⁻¹) ≤ 2)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ epsilon / 32)
    (hmain : epsilon ≤
      |((B.dilate t).carrier.card : ℝ) *
        ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U : Finset (ZMod N)),
      p' ≤ 2 ^ 10 * (epsilon / 8)⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈(epsilon / 8)⁻¹ * Real.log (256 / (epsilon / 8))⌉₊) ∧
      0 < q ∧ Even q ∧ x ∈ S + T ∧
      A₁ ⊆ S ∧ A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U = s q ((epsilon / 8) / 16) S
        (CyclicLocalSifting.reflectedTranslate T x) A ∧
      1 - (epsilon / 8) / 32 ≤
        ∑ y ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * alpha ^ (2 * q) ≤
        (A₂.card : ℝ) / T.card ∧
      ∀ y ∈ U,
        1 + (epsilon / 8) / 8 ≤
          (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) y := by
  have hlarge := large_positiveDefinite_norm_of_local_correlation_gap
    B A C S T m p hm hp hpEven halpha hgamma hepsilon0 hdelta hdeltat
    hregular hA hC hAB hAdense hCinner hCsmall hCdense hgammaFactor hS hT
    hSsub hTsub herror hmain
  have herror' :
      3 * (1 / ((5 * m : ℕ) * alpha)) ≤ (epsilon / 8) / 4 := by
    simpa only [div_div, show (8 : ℝ) * 4 = 32 by norm_num] using herror
  exact unbalancing_sifting_of_large_positiveDefinite_norm
    B A S T m p hm hp halpha (by positivity) (by nlinarith) hdelta.le
    (sub_nonneg.mpr hdeltat.le) hregular hA hAB hAdense hS hT hSsub hTsub
    herror' hlarge

end CyclicLocalDensityIncrement
end Erdos721
