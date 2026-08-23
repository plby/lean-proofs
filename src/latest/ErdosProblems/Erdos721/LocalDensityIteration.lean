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

import ErdosProblems.Erdos721.DensityIncrementIteration
import ErdosProblems.Erdos721.LocalDensityIncrement

/-!
# Relative local density increments

This file connects the local unbalancing--sifting package to tested
almost-periodicity and the relative algebraic density-increment tail.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalDensityIteration

variable {N : ℕ} [NeZero N]

/-- The Cauchy--Schwarz loss in the tested almost-periodicity estimate. -/
noncomputable def smoothingRatio (A₁ U : Finset (ZMod N)) : ℝ :=
  Real.sqrt ((N : ℝ) / A₁.card) * Real.sqrt ((U.card : ℝ) / N)

/-- An explicit spectral radius which makes the Chang error harmless. -/
noncomputable def smoothingEta (epsilon : ℝ)
    (A₁ U : Finset (ZMod N)) : ℝ :=
  Real.sqrt (epsilon / (128 * (smoothingRatio A₁ U + 1)))

/-- Spectral parameter leaving room for a strictly positive Bohr radius. -/
noncomputable def positiveSmoothingEta (epsilon : ℝ)
    (A₁ U : Finset (ZMod N)) : ℝ :=
  Real.sqrt (epsilon / (256 * (smoothingRatio A₁ U + 1)))

/-- Positive spectral radius chosen after the Croot--Sisask shift set is
known. -/
noncomputable def positiveSmoothingRho (epsilon : ℝ)
    (A₁ U T : Finset (ZMod N)) : ℝ :=
  epsilon /
    (128 *
      ((CyclicChang.changRankBound T
        (positiveSmoothingEta epsilon A₁ U) : ℝ) + 1) *
      (smoothingRatio A₁ U + 1))

lemma smoothingRatio_nonneg (A₁ U : Finset (ZMod N)) :
    0 ≤ smoothingRatio A₁ U := by
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma smoothingEta_pos (A₁ U : Finset (ZMod N)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) : 0 < smoothingEta epsilon A₁ U := by
  apply Real.sqrt_pos.2
  exact div_pos hepsilon (mul_pos (by norm_num)
    (by linarith [smoothingRatio_nonneg A₁ U]))

lemma positiveSmoothingEta_pos (A₁ U : Finset (ZMod N)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) : 0 < positiveSmoothingEta epsilon A₁ U := by
  apply Real.sqrt_pos.2
  exact div_pos hepsilon (mul_pos (by norm_num)
    (by linarith [smoothingRatio_nonneg A₁ U]))

lemma positiveSmoothingRho_pos (A₁ U T : Finset (ZMod N)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    0 < positiveSmoothingRho epsilon A₁ U T := by
  apply div_pos hepsilon
  exact mul_pos
    (mul_pos (by norm_num) (by positivity))
    (by linarith [smoothingRatio_nonneg A₁ U])

/-- Choosing `apError = epsilon / 128`, spectral radius
`sqrt (epsilon / (128(R+1)))`, exponent `2`, and radius loss `0` makes the
entire tested almost-periodicity error at most `epsilon / 32`. -/
lemma explicit_smoothing_error_bound {epsilon R : ℝ} (d : ℕ)
    (hepsilon : 0 < epsilon) (hR : 0 ≤ R) :
    2 * (epsilon / 128) +
        (((d : ℝ) * 0 +
          2 * (Real.sqrt (epsilon / (128 * (R + 1)))) ^ 2) * R) ≤
      epsilon / 32 := by
  have hden : 0 < 128 * (R + 1) := by positivity
  have hquot : 0 ≤ epsilon / (128 * (R + 1)) := by positivity
  rw [Real.sq_sqrt hquot]
  have hratio : R / (R + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hmul :
      (epsilon / 64) * (R / (R + 1)) ≤ epsilon / 64 := by
    simpa using mul_le_mul_of_nonneg_left hratio
      (by positivity : 0 ≤ epsilon / 64)
  calc
    2 * (epsilon / 128) +
        (((d : ℝ) * 0 + 2 * (epsilon / (128 * (R + 1)))) * R) =
        epsilon / 64 + (epsilon / 64) * (R / (R + 1)) := by
          field_simp
          ring
    _ ≤ epsilon / 64 + epsilon / 64 := by gcongr
    _ = epsilon / 32 := by ring

/-- The three error contributions for the positive-radius parameter choice. -/
lemma explicit_positive_smoothing_error_bound {epsilon R : ℝ} (d : ℕ)
    (hepsilon : 0 < epsilon) (hR : 0 ≤ R) :
    2 * (epsilon / 256) +
        (((d : ℝ) *
            (epsilon / (128 * ((d : ℝ) + 1) * (R + 1))) +
          2 * (Real.sqrt (epsilon / (256 * (R + 1)))) ^ 2) * R) ≤
      epsilon / 32 := by
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hRone : 0 < R + 1 := by linarith
  have hdone : 0 < (d : ℝ) + 1 := by positivity
  have hetaNonneg : 0 ≤ epsilon / (256 * (R + 1)) := by positivity
  rw [Real.sq_sqrt hetaNonneg]
  have hdRatio : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hdone]
    linarith
  have hRRatio : R / (R + 1) ≤ 1 := by
    rw [div_le_one hRone]
    linarith
  have hprodRatio :
      ((d : ℝ) / ((d : ℝ) + 1)) * (R / (R + 1)) ≤ 1 := by
    calc
      ((d : ℝ) / ((d : ℝ) + 1)) * (R / (R + 1)) ≤
          1 * (R / (R + 1)) := by gcongr
      _ ≤ 1 := by simpa using hRRatio
  have hrhoTerm :
      ((d : ℝ) *
          (epsilon / (128 * ((d : ℝ) + 1) * (R + 1)))) * R ≤
        epsilon / 128 := by
    calc
      ((d : ℝ) *
          (epsilon / (128 * ((d : ℝ) + 1) * (R + 1)))) * R =
          (epsilon / 128) *
            (((d : ℝ) / ((d : ℝ) + 1)) * (R / (R + 1))) := by
              field_simp
      _ ≤ (epsilon / 128) * 1 := by
        exact mul_le_mul_of_nonneg_left hprodRatio (by positivity)
      _ = epsilon / 128 := by ring
  have hetaTerm :
      (2 * (epsilon / (256 * (R + 1)))) * R ≤ epsilon / 128 := by
    calc
      (2 * (epsilon / (256 * (R + 1)))) * R =
          (epsilon / 128) * (R / (R + 1)) := by
            field_simp
            ring
      _ ≤ (epsilon / 128) * 1 := by
        exact mul_le_mul_of_nonneg_left hRRatio (by positivity)
      _ = epsilon / 128 := by ring
  nlinarith

/-- Relative version of the tested almost-periodicity density increment.
Unlike the global wrapper, the normalizing scale is an ambient Bohr carrier
cardinality. -/
theorem exists_local_bohr_density_increment_relative
    (B : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale : ℕ) {t delta alpha beta epsilon apError eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hapError0 : 0 < apError) (hapError1 : apError ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho)
    (hbase :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hsmall : ∀ T : Finset (ZMod N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / apError ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card →
      2 * apError +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) ≤ epsilon / 32) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / apError ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      (1 + epsilon / 32) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞] := by
  obtain ⟨T, C, hT, hCrank, hCsub, hsmooth⟩ :=
    CyclicDensityIncrement.exists_local_bohr_tested_correlation_real
      B A₁ A₂ U k halpha0 halphahalf hdelta hdeltat hAinner hAdense
      hregular hapError0 hapError1 hk hA₁ hA₂ hU heta hrho
  refine ⟨T, C, hT, hCrank, hCsub, ?_⟩
  apply CyclicDensityIncrement.density_increment_of_large_smoothed_test_sum_relative
    A A₁ A₂ C.carrier U scale hepsilon0 hepsilon1 hbeta hdensity
    hA hA₁ hA₂ hhigh
  calc
    1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        |(∑ x ∈ U,
            (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
      gcongr
      exact hsmooth.trans (hsmall T hT)
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        -((∑ x ∈ U,
            (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
      gcongr
      exact neg_le_abs _
    _ = ∑ x ∈ U,
        (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      ring

/-- The relative local density increment with all smoothing parameters chosen
explicitly.  In particular, there is no residual analytic smallness
hypothesis. -/
theorem exists_local_bohr_density_increment_relative_explicit
    (B : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale : ℕ) {t delta alpha beta epsilon : ℝ}
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hbase :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (2 : ℝ) ^ 2 / (epsilon / 128) ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank +
        CyclicChang.changRankBound T (smoothingEta epsilon A₁ U) ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      (1 + epsilon / 32) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞] := by
  apply exists_local_bohr_density_increment_relative B A A₁ A₂ U scale
    (apError := epsilon / 128) (eta := smoothingEta epsilon A₁ U)
    (rho := 0) 2 halpha0 halphahalf hbeta hdensity hdelta hdeltat
    hAinner hAdense hregular hepsilon0 hepsilon1
  · positivity
  · linarith
  · norm_num
  · exact hA
  · exact hA₁
  · exact hA₂
  · exact hU
  · exact smoothingEta_pos A₁ U hepsilon0
  · norm_num
  · exact hbase
  · exact hhigh
  · intro T _hT
    simpa only [smoothingEta, smoothingRatio] using
      explicit_smoothing_error_bound
        (CyclicChang.changRankBound T (smoothingEta epsilon A₁ U))
        hepsilon0 (smoothingRatio_nonneg A₁ U)

/-- Positive-radius relative density increment with every smoothing parameter
chosen explicitly.  This is the iteration-safe form: positivity of the old
radius is inherited by the new Bohr set. -/
theorem exists_local_bohr_density_increment_relative_positive
    (B : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale : ℕ) {t delta alpha beta epsilon : ℝ}
    (hBradius : 0 < B.radius)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hdelta : 0 < delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hbase :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (2 : ℝ) ^ 2 / (epsilon / 256) ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius
        (positiveSmoothingRho epsilon A₁ U T) ∧
      0 < C.radius ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T
        (positiveSmoothingEta epsilon A₁ U) ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      (1 + epsilon / 32) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞] := by
  let rho : Finset (ZMod N) → ℝ :=
    positiveSmoothingRho epsilon A₁ U
  obtain ⟨T, C, hT, hCradius, hBrank, hCrank, hCsub, hsmooth⟩ :=
    CyclicDensityIncrement.exists_local_bohr_tested_correlation_real_adaptive
      B A₁ A₂ U rho (t := t) (delta := delta) (alpha := alpha)
      (epsilon := epsilon / 256)
      (eta := positiveSmoothingEta epsilon A₁ U) 2
      halpha0 halphahalf hdelta.le hdeltat hAinner
      hAdense hregular (by positivity) (by linarith) (by norm_num) hA₁ hA₂ hU
      (positiveSmoothingEta_pos A₁ U hepsilon0)
      (fun T _hT ↦ positiveSmoothingRho_pos A₁ U T hepsilon0)
  refine ⟨T, C, hT, hCradius, ?_, hBrank, hCrank, hCsub, ?_⟩
  · rw [hCradius]
    apply lt_min
    · simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hdelta]
      positivity
    · exact positiveSmoothingRho_pos A₁ U T hepsilon0
  · apply CyclicDensityIncrement.density_increment_of_large_smoothed_test_sum_relative
      A A₁ A₂ C.carrier U scale hepsilon0 hepsilon1 hbeta hdensity
      hA hA₁ hA₂ hhigh
    have herror :
        2 * (epsilon / 256) +
            ((CyclicChang.changRankBound T
                  (positiveSmoothingEta epsilon A₁ U) : ℝ) * rho T +
              2 * positiveSmoothingEta epsilon A₁ U ^ 2) *
                smoothingRatio A₁ U ≤ epsilon / 32 := by
      simpa only [rho, positiveSmoothingRho, positiveSmoothingEta] using
        explicit_positive_smoothing_error_bound
          (CyclicChang.changRankBound T
            (positiveSmoothingEta epsilon A₁ U))
          hepsilon0 (smoothingRatio_nonneg A₁ U)
    calc
      1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          |(∑ x ∈ U,
              (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
        gcongr
        exact hsmooth.trans herror
      _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          -((∑ x ∈ U,
              (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
            ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
        gcongr
        exact neg_le_abs _
      _ = ∑ x ∈ U,
          (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
        ring

/-- Positive-radius density increment whose smoothing carrier is selected at
a fine regular scale before the analytic estimate is applied.  Consequently
the output `C_u` and its adjacent dilates can be used directly as the next
iteration state. -/
theorem exists_local_regular_bohr_density_increment_relative_positive
    (B : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    (scale m : ℕ) {t delta alpha beta epsilon : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank) (hm : 0 < m)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hdelta : 0 < delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hbase :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N) (u zeta : ℝ),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (2 : ℝ) ^ 2 / (epsilon / 256) ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.radius = min (B.dilate delta).radius
        (positiveSmoothingRho epsilon A₁ U T) ∧
      0 < C.radius ∧
      B.rank ≤ C.rank ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T
        (positiveSmoothingEta epsilon A₁ U) ∧
      1 / 2 ≤ u ∧ u ≤ 1 ∧
      zeta = (400 * (m : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < zeta ∧ zeta < u ∧
      (10 * m) * (C.dilate (u + zeta)).carrier.card ≤
        (10 * m + 1) * (C.dilate (u - zeta)).carrier.card ∧
      (C.dilate u).carrier ⊆ (B.dilate delta).carrier ∧
      (1 + epsilon / 32) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (C.dilate u).carrier‖_[∞] := by
  let rho : Finset (ZMod N) → ℝ := positiveSmoothingRho epsilon A₁ U
  obtain ⟨T, C, u, zeta, hT, hCradius, hCpos, hBrankC, hCrank,
      hulow, huhigh, hzetaFormula, hzeta, hzetau, hregularC, hCsub,
      hsmooth⟩ :=
    CyclicDensityIncrement.exists_local_regular_bohr_tested_correlation_real_adaptive
        B A₁ A₂ U rho (t := t) (delta := delta) (alpha := alpha)
        (epsilon := epsilon / 256)
        (eta := positiveSmoothingEta epsilon A₁ U) 2 m
        hBradius hBrank hm halpha0 halphahalf
        hdelta hdeltat hAinner hAdense hregular (by positivity) (by linarith)
        (by norm_num) hA₁ hA₂ hU
        (positiveSmoothingEta_pos A₁ U hepsilon0)
        (fun T _hT ↦ positiveSmoothingRho_pos A₁ U T hepsilon0)
  refine ⟨T, C, u, zeta, hT, hCradius, hCpos, hBrankC, hCrank,
    hulow, huhigh, hzetaFormula, hzeta, hzetau, hregularC, hCsub, ?_⟩
  apply CyclicDensityIncrement.density_increment_of_large_smoothed_test_sum_relative
    A A₁ A₂ (C.dilate u).carrier U scale hepsilon0 hepsilon1 hbeta
    hdensity hA hA₁ hA₂ hhigh
  have herror :
      2 * (epsilon / 256) +
          ((CyclicChang.changRankBound T
                (positiveSmoothingEta epsilon A₁ U) : ℝ) * rho T +
            2 * positiveSmoothingEta epsilon A₁ U ^ 2) *
              smoothingRatio A₁ U ≤ epsilon / 32 := by
    simpa only [rho, positiveSmoothingRho, positiveSmoothingEta] using
      explicit_positive_smoothing_error_bound
        (CyclicChang.changRankBound T
          (positiveSmoothingEta epsilon A₁ U))
        hepsilon0 (smoothingRatio_nonneg A₁ U)
  calc
    1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        |(∑ x ∈ U,
            (μ_[ℝ] (C.dilate u).carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
      gcongr
      exact hsmooth.trans herror
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        -((∑ x ∈ U,
            (μ_[ℝ] (C.dilate u).carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
      gcongr
      exact neg_le_abs _
    _ = ∑ x ∈ U,
        (μ_[ℝ] (C.dilate u).carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      ring

end CyclicLocalDensityIteration
end Erdos721
