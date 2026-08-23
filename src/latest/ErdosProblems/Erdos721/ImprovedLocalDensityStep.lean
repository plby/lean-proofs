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

import ErdosProblems.Erdos721.ImprovedLocalDensityIteration
import ErdosProblems.Erdos721.LocalDensityIncrement

/-!
# The improved iteration-safe local density step

This file joins local unbalancing and sifting to the improved test-function
density increment.  Its output is a three-term-progression-free normalized
slice on a fine regular Bohr carrier, together with all quantitative data
needed by the global iteration.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicImprovedLocalDensityStep

variable {N : ℕ} [NeZero N]

private lemma nonempty_of_positive_relative_density
    (A S : Finset (ZMod N)) {alpha : ℝ} (halpha : 0 < alpha)
    (hS : S.Nonempty) (hdense : alpha ≤ (A.card : ℝ) / S.card) :
    A.Nonempty := by
  by_contra hA
  rw [not_nonempty_iff_eq_empty.mp hA] at hdense
  simp at hdense
  exact (not_lt_of_ge hdense) halpha

/-- Improved Bloom--Sisask Proposition 10 in the exact local form consumed
by the finite iteration. -/
theorem exists_positive_density_increment_slice_of_large_norm
    (B H : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta u zeta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (hzeta : 0 < zeta) (hzetau : zeta ≤ u)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hHregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSinner : S = (H.dilate (u - zeta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hHsmall : (H.dilate zeta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U X : Finset (ZMod N))
        (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      0 < q ∧ Even q ∧ x ∈ S + T ∧
      A₁ ⊆ S ∧
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U ⊆ A₁ - A₂ ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₂.card : ℝ) / T.card ∧
      CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
          H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ≤
        X.card ∧
      X.Nonempty ∧
      C.radius = min (H.dilate zeta).radius
        (CyclicImprovedParameters.improvedRho epsilon beta X) ∧
      0 < C.radius ∧
      H.rank ≤ C.rank ∧
      C.rank ≤ H.rank + CyclicChang.changRankBound X (1 / 2) ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  have hAdense : beta * (B.dilate t).carrier.card ≤ A.card :=
    hdensity.le
  obtain ⟨p', q, x, A₁, A₂, U₀, hp'upper, hq, hq0, hqEven, hx,
      hA₁S, hA₂T, _hU₀, hmass₀, hA₁dense, hA₂dense, hhigh₀⟩ :=
    CyclicLocalDensityIncrement.unbalancing_sifting_of_large_positiveDefinite_norm
      B A S T m p hm hp hbeta0 hepsilon0 hepsilon1 hdelta hinner hregular
      hA hAB hAdense hS hT hSsub hTsub herror hlarge
  let U : Finset (ZMod N) := U₀ ∩ (A₁ - A₂)
  have hmassEq :
      (∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z) =
        ∑ z ∈ U₀, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hzU₀ hznotU
    have hznot : z ∉ A₁ - A₂ := by
      intro hz
      exact hznotU (by simp [U, hzU₀, hz])
    have hzzero : (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z = 0 := by
      by_contra hz
      have hzsupp : z ∈ Function.support (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) := hz
      rw [support_dddconv (mu_nonneg (K := ℝ)) (mu_nonneg (K := ℝ)),
        support_mu, support_mu, ← Finset.coe_sub, Finset.mem_coe] at hzsupp
      exact hznot hzsupp
    exact hzzero
  have hmass :
      1 - epsilon / 32 ≤
        ∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    rw [hmassEq]
    exact hmass₀
  have hUsub : U ⊆ A₁ - A₂ := Finset.inter_subset_right
  have hhigh : ∀ z ∈ U,
      1 + epsilon / 8 ≤
        (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) z := by
    intro z hz
    exact hhigh₀ z (Finset.inter_subset_left hz)
  have haux0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hauxhalf : (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ 1 / 2 := by
    have hpow : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hA₁ : A₁.Nonempty :=
    nonempty_of_positive_relative_density A₁ S haux0 hS hA₁dense
  have hA₂ : A₂.Nonempty :=
    nonempty_of_positive_relative_density A₂ T haux0 hT hA₂dense
  have hU : U.Nonempty := by
    by_contra hUnonempty
    rw [not_nonempty_iff_eq_empty.mp hUnonempty] at hmass
    simp at hmass
    linarith
  have hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier := by
    simpa only [← hSinner] using hA₁S
  have hA₁dense' :
      ((4 : ℝ)⁻¹ * beta ^ (2 * q)) *
          (H.dilate (u - zeta)).carrier.card ≤ A₁.card := by
    rw [← hSinner]
    rw [le_div_iff₀ (by exact_mod_cast hS.card_pos)] at hA₁dense
    simpa only [mul_comm] using hA₁dense
  obtain ⟨X, C, v, xi, hXcard, hX, hCradius, hCpos, hHrankC, hCrank,
      hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hinc⟩ :=
    CyclicImprovedLocalDensityIteration.exists_local_improved_density_increment
      H A A₁ A₂ U (B.dilate t).carrier.card mNext hHradius hHrank
      hmNext haux0 hauxhalf hbeta0 hbeta1 hdensity hepsilon0 hepsilon1
      hzeta hzetau hA₁inner hA₁dense' hHregular hA hA₁ hA₂ hU
      hmass hhigh
  obtain ⟨y, hslice, hfree, hdense⟩ :=
    CyclicDensityIncrement.exists_normalizedSlice_of_dLinfty_bound A
      (C.dilate v)
      (mul_nonneg (by positivity) hbeta0.le) hAfree hinc
  exact ⟨p', q, x, A₁, A₂, U, X, C, v, xi, y, hp'upper, hq, hq0,
    hqEven, hx, hA₁S, hA₂T, hUsub, hA₁dense, hA₂dense, hXcard, hX,
    hCradius, hCpos, hHrankC, hCrank, hvlow, hvhigh, hxiFormula, hxi, hxiv,
    hCregular, hCsmall.trans hHsmall, hslice, hfree, hdense⟩

/-- Rank-free form of the complete improved local density step.  The
Croot--Sisask base set and its translating point are retained, and the new
Bohr rank is charged only by the canonical local Chang--Sanders entropy. -/
theorem exists_positive_density_increment_slice_of_large_norm_rankFree
    (B H : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta u zeta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (hzeta : 0 < zeta) (hzetau : zeta ≤ u)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hHregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSinner : S = (H.dilate (u - zeta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hHsmall : (H.dilate zeta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U Tbase : Finset (ZMod N))
        (zbase : ZMod N) (X : Finset (ZMod N))
        (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      0 < q ∧ Even q ∧ x ∈ S + T ∧
      A₁ ⊆ S ∧
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U ⊆ A₁ - A₂ ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₂.card : ℝ) / T.card ∧
      CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
          H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ≤
        Tbase.card ∧
      Tbase ⊆ (H.dilate zeta).carrier ∧ zbase ∈ Tbase ∧
      X = (-zbase) +ᵥ Tbase ∧ X.Nonempty ∧
      C.radius = min (H.dilate zeta).radius
        (CyclicLocalChangSanders.rankFreeControllerRadius H
          (CyclicImprovedLocalDensityIteration.rankFreeEntropy
            H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta)
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            epsilon beta)
          zeta
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            epsilon beta
            (CyclicImprovedLocalDensityIteration.rankFreeEntropy
              H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q))
                epsilon beta))) ∧
      0 < C.radius ∧
      H.rank ≤ C.rank ∧
      C.rank ≤ H.rank +
        CyclicImprovedLocalDensityIteration.rankFreeEntropy
          H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  have hAdense : beta * (B.dilate t).carrier.card ≤ A.card := hdensity.le
  obtain ⟨p', q, x, A₁, A₂, U₀, hp'upper, hq, hq0, hqEven, hx,
      hA₁S, hA₂T, _hU₀, hmass₀, hA₁dense, hA₂dense, hhigh₀⟩ :=
    CyclicLocalDensityIncrement.unbalancing_sifting_of_large_positiveDefinite_norm
      B A S T m p hm hp hbeta0 hepsilon0 hepsilon1 hdelta hinner hregular
      hA hAB hAdense hS hT hSsub hTsub herror hlarge
  let U : Finset (ZMod N) := U₀ ∩ (A₁ - A₂)
  have hmassEq :
      (∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z) =
        ∑ z ∈ U₀, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hzU₀ hznotU
    have hznot : z ∉ A₁ - A₂ := by
      intro hz
      exact hznotU (by simp [U, hzU₀, hz])
    have hzzero : (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z = 0 := by
      by_contra hz
      have hzsupp : z ∈ Function.support (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) := hz
      rw [support_dddconv (mu_nonneg (K := ℝ)) (mu_nonneg (K := ℝ)),
        support_mu, support_mu, ← Finset.coe_sub, Finset.mem_coe] at hzsupp
      exact hznot hzsupp
    exact hzzero
  have hmass :
      1 - epsilon / 32 ≤ ∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    rw [hmassEq]
    exact hmass₀
  have hUsub : U ⊆ A₁ - A₂ := Finset.inter_subset_right
  have hhigh : ∀ z ∈ U,
      1 + epsilon / 8 ≤
        (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) z := by
    intro z hz
    exact hhigh₀ z (Finset.inter_subset_left hz)
  have haux0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hauxhalf : (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ 1 / 2 := by
    have hpow : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hA₁ : A₁.Nonempty :=
    nonempty_of_positive_relative_density A₁ S haux0 hS hA₁dense
  have hA₂ : A₂.Nonempty :=
    nonempty_of_positive_relative_density A₂ T haux0 hT hA₂dense
  have hU : U.Nonempty := by
    by_contra hUnonempty
    rw [not_nonempty_iff_eq_empty.mp hUnonempty] at hmass
    simp at hmass
    linarith
  have hA₁inner : A₁ ⊆ (H.dilate (u - zeta)).carrier := by
    simpa only [← hSinner] using hA₁S
  have hA₁dense' :
      ((4 : ℝ)⁻¹ * beta ^ (2 * q)) *
          (H.dilate (u - zeta)).carrier.card ≤ A₁.card := by
    rw [← hSinner]
    rw [le_div_iff₀ (by exact_mod_cast hS.card_pos)] at hA₁dense
    simpa only [mul_comm] using hA₁dense
  obtain ⟨Tbase, zbase, X, C, v, xi, hTbaseCard, hTbaseSub,
      hzbase, hXeq, hX, hCradius, hCpos, hHrankC, hCrank,
      hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hinc⟩ :=
    CyclicImprovedLocalDensityIteration.exists_local_improved_density_increment_rankFree_explicit
      H A A₁ A₂ U (B.dilate t).carrier.card mNext hHradius hHrank
      hmNext haux0 hauxhalf hbeta0 hbeta1 hdensity hepsilon0 hepsilon1
      hzeta hzetau hA₁inner hA₁dense' hHregular hA hA₁ hA₂ hU
      hmass hhigh
  obtain ⟨y, hslice, hfree, hdense⟩ :=
    CyclicDensityIncrement.exists_normalizedSlice_of_dLinfty_bound A
      (C.dilate v) (mul_nonneg (by positivity) hbeta0.le) hAfree hinc
  exact ⟨p', q, x, A₁, A₂, U, Tbase, zbase, X, C, v, xi, y,
    hp'upper, hq, hq0, hqEven, hx, hA₁S, hA₂T, hUsub,
    hA₁dense, hA₂dense, hTbaseCard, hTbaseSub, hzbase, hXeq, hX,
    hCradius, hCpos, hHrankC, hCrank, hvlow, hvhigh, hxiFormula, hxi,
    hxiv, hCregular, hCsmall.trans hHsmall, hslice, hfree, hdense⟩

/-- Source-ordered rank-free local density step.  The second sifted set is
dense in the inner regular carrier of `R`, while the controller is built in
the much smaller scale `R.dilate eta`.  Its entropy therefore depends only on
the two sifted relative densities. -/
theorem exists_positive_density_increment_slice_of_large_norm_stable_reflected
    (B R : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta vr eta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (heta : 0 < eta) (hetavr : eta ≤ vr)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hTinner : T = (R.dilate (vr - eta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hRsmall : (R.dilate eta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U Sbase Tbase : Finset (ZMod N))
        (zbase : ZMod N) (X : Finset (ZMod N)) (deltaStable : ℝ)
        (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      0 < q ∧ Even q ∧ x ∈ S + T ∧
      A₁ ⊆ S ∧
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U ⊆ A₁ - A₂ ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₂.card : ℝ) / T.card ∧
      U.Nonempty ∧
      Sbase.Nonempty ∧ Sbase ⊆ (R.dilate eta).carrier ∧
      CyclicImprovedLocalDensityIteration.reflectedImprovedCrootLowerBound
          Sbase A₁ U (11 /
            (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) epsilon beta ≤
        Tbase.card ∧
      Tbase ⊆ Sbase ∧ zbase ∈ Tbase ∧ X = (-zbase) +ᵥ Tbase ∧
      X.Nonempty ∧
      deltaStable =
        (400 * ((2 ^
          CyclicImprovedLocalDensityIteration.reflectedStableEntropy
            A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta : ℕ) : ℝ) *
          (R.rank : ℝ))⁻¹ ∧
      0 < deltaStable ∧
      C.radius = min (R.dilate eta).radius
        (CyclicLocalChangSanders.stableCarrierControllerRadius
          (R.dilate eta)
          (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
            A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta)
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            epsilon beta)
          deltaStable
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            epsilon beta
            (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
              A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta))) ∧
      0 < C.radius ∧
      R.rank ≤ C.rank ∧
      C.rank ≤ R.rank +
        CyclicImprovedLocalDensityIteration.reflectedStableEntropy
          A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  have hAdense : beta * (B.dilate t).carrier.card ≤ A.card := hdensity.le
  obtain ⟨p', q, x, A₁, A₂, U₀, hp'upper, hq, hq0, hqEven, hx,
      hA₁S, hA₂T, _hU₀, hmass₀, hA₁dense, hA₂dense, hhigh₀⟩ :=
    CyclicLocalDensityIncrement.unbalancing_sifting_of_large_positiveDefinite_norm
      B A S T m p hm hp hbeta0 hepsilon0 hepsilon1 hdelta hinner hregular
      hA hAB hAdense hS hT hSsub hTsub herror hlarge
  let U : Finset (ZMod N) := U₀ ∩ (A₁ - A₂)
  have hmassEq :
      (∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z) =
        ∑ z ∈ U₀, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hzU₀ hznotU
    have hznot : z ∉ A₁ - A₂ := by
      intro hz
      exact hznotU (by simp [U, hzU₀, hz])
    have hzzero : (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z = 0 := by
      by_contra hz
      have hzsupp : z ∈ Function.support (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) := hz
      rw [support_dddconv (mu_nonneg (K := ℝ)) (mu_nonneg (K := ℝ)),
        support_mu, support_mu, ← Finset.coe_sub, Finset.mem_coe] at hzsupp
      exact hznot hzsupp
    exact hzzero
  have hmass :
      1 - epsilon / 32 ≤ ∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    rw [hmassEq]
    exact hmass₀
  have hUsub : U ⊆ A₁ - A₂ := Finset.inter_subset_right
  have hhigh : ∀ z ∈ U,
      1 + epsilon / 8 ≤
        (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) z := by
    intro z hz
    exact hhigh₀ z (Finset.inter_subset_left hz)
  have haux0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hauxhalf : (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ 1 / 2 := by
    have hpow : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hA₁ : A₁.Nonempty :=
    nonempty_of_positive_relative_density A₁ S haux0 hS hA₁dense
  have hA₂ : A₂.Nonempty :=
    nonempty_of_positive_relative_density A₂ T haux0 hT hA₂dense
  have hU : U.Nonempty := by
    by_contra hUnonempty
    rw [not_nonempty_iff_eq_empty.mp hUnonempty] at hmass
    simp at hmass
    linarith
  have hA₂inner :
      A₂ ⊆ x +ᵥ -(R.dilate (vr - eta)).carrier := by
    simpa only [CyclicLocalSifting.reflectedTranslate, ← hTinner] using hA₂T
  have hA₂dense' :
      ((4 : ℝ)⁻¹ * beta ^ (2 * q)) *
          (R.dilate (vr - eta)).carrier.card ≤ A₂.card := by
    rw [← hTinner]
    rw [le_div_iff₀ (by exact_mod_cast hT.card_pos)] at hA₂dense
    simpa only [mul_comm] using hA₂dense
  obtain ⟨Sbase, Tbase, zbase, X, deltaStable, C, v, xi,
      hSbase, hSbaseSub, hTbaseCard, hTbaseSub, hzbase, hXeq, hX,
      hdeltaFormula, hdeltaStable, hCradius, hCpos, hRrankC, hCrank,
      hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hinc⟩ :=
    CyclicImprovedLocalDensityIteration.exists_local_improved_density_increment_stable_reflected_explicit
      R A A₁ A₂ U x (B.dilate t).carrier.card mNext hRradius hRrank
      hmNext haux0 hauxhalf hbeta0 hbeta1 hdensity hepsilon0 hepsilon1
      heta hetavr hA₂inner hA₂dense' hRregular hA hA₁ hA₂ hU hmass hhigh
  obtain ⟨y, hslice, hfree, hdense⟩ :=
    CyclicDensityIncrement.exists_normalizedSlice_of_dLinfty_bound A
      (C.dilate v) (mul_nonneg (by positivity) hbeta0.le) hAfree hinc
  exact ⟨p', q, x, A₁, A₂, U, Sbase, Tbase, zbase, X, deltaStable,
    C, v, xi, y, hp'upper, hq, hq0, hqEven, hx, hA₁S, hA₂T,
    hUsub, hA₁dense, hA₂dense, hU, hSbase, hSbaseSub, hTbaseCard,
    hTbaseSub, hzbase, hXeq, hX, hdeltaFormula, hdeltaStable,
    hCradius, hCpos, hRrankC, hCrank, hvlow, hvhigh, hxiFormula, hxi,
    hxiv, hCregular, hCsmall.trans hRsmall, hslice, hfree, hdense⟩

/-- Iteration-facing quantitative local step with the sharp
Chang--Sanders radius.  The retained sifted witnesses are exactly those
needed to bound the entropy and hence the polynomial controller loss. -/
theorem exists_positive_density_increment_slice_of_large_norm_sharp_reflected_quantitative
    (B R : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta vr eta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (heta : 0 < eta) (hetavr : eta ≤ vr)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hTinner : T = (R.dilate (vr - eta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hRsmall : (R.dilate eta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U : Finset (ZMod N))
        (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      A₁.Nonempty ∧ U.Nonempty ∧
      A₁ ⊆ S ∧
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U ⊆ A₁ - A₂ ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₁.card : ℝ) / S.card ∧
      C.radius = min (R.dilate eta).radius
        (CyclicSharpLocalChangSanders.sharpControllerRadius
          (R.dilate eta)
          (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
            A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta - 1)
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            epsilon beta)
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            epsilon beta
            (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
              A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta))) ∧
      0 < C.radius ∧
      R.rank ≤ C.rank ∧
      C.rank ≤ R.rank +
        CyclicImprovedLocalDensityIteration.reflectedStableEntropy
          A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  have hAdense : beta * (B.dilate t).carrier.card ≤ A.card := hdensity.le
  obtain ⟨p', q, x, A₁, A₂, U₀, hp'upper, hq, hq0, hqEven, hx,
      hA₁S, hA₂T, _hU₀, hmass₀, hA₁dense, hA₂dense, hhigh₀⟩ :=
    CyclicLocalDensityIncrement.unbalancing_sifting_of_large_positiveDefinite_norm
      B A S T m p hm hp hbeta0 hepsilon0 hepsilon1 hdelta hinner hregular
      hA hAB hAdense hS hT hSsub hTsub herror hlarge
  let U : Finset (ZMod N) := U₀ ∩ (A₁ - A₂)
  have hmassEq :
      (∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z) =
        ∑ z ∈ U₀, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hzU₀ hznotU
    have hznot : z ∉ A₁ - A₂ := by
      intro hz
      exact hznotU (by simp [U, hzU₀, hz])
    have hzzero : (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z = 0 := by
      by_contra hz
      have hzsupp : z ∈ Function.support (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) := hz
      rw [support_dddconv (mu_nonneg (K := ℝ)) (mu_nonneg (K := ℝ)),
        support_mu, support_mu, ← Finset.coe_sub, Finset.mem_coe] at hzsupp
      exact hznot hzsupp
    exact hzzero
  have hmass :
      1 - epsilon / 32 ≤ ∑ z ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) z := by
    rw [hmassEq]
    exact hmass₀
  have hUsub : U ⊆ A₁ - A₂ := Finset.inter_subset_right
  have hhigh : ∀ z ∈ U,
      1 + epsilon / 8 ≤
        (B.dilate t).carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) z := by
    intro z hz
    exact hhigh₀ z (Finset.inter_subset_left hz)
  have haux0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hauxhalf : (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ 1 / 2 := by
    have hpow : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hA₁ : A₁.Nonempty :=
    nonempty_of_positive_relative_density A₁ S haux0 hS hA₁dense
  have hA₂ : A₂.Nonempty :=
    nonempty_of_positive_relative_density A₂ T haux0 hT hA₂dense
  have hU : U.Nonempty := by
    by_contra hUnonempty
    rw [not_nonempty_iff_eq_empty.mp hUnonempty] at hmass
    simp at hmass
    linarith
  have hA₂inner :
      A₂ ⊆ x +ᵥ -(R.dilate (vr - eta)).carrier := by
    simpa only [CyclicLocalSifting.reflectedTranslate, ← hTinner] using hA₂T
  have hA₂dense' :
      ((4 : ℝ)⁻¹ * beta ^ (2 * q)) *
          (R.dilate (vr - eta)).carrier.card ≤ A₂.card := by
    rw [← hTinner]
    rw [le_div_iff₀ (by exact_mod_cast hT.card_pos)] at hA₂dense
    simpa only [mul_comm] using hA₂dense
  obtain ⟨_Sbase, _Tbase, _zbase, _X, C, v, xi,
      _hSbase, _hSbaseSub, _hTbaseCard, _hTbaseSub, _hzbase, _hXeq,
      _hX, hCradius, hCpos, hRrankC, hCrank, hvlow, hvhigh,
      hxiFormula, hxi, hxiv, hCregular, hCsmall, hinc⟩ :=
    CyclicImprovedLocalDensityIteration.exists_local_improved_density_increment_sharp_reflected_explicit
      R A A₁ A₂ U x (B.dilate t).carrier.card mNext hRradius hRrank
      hmNext haux0 hauxhalf hbeta0 hbeta1 hdensity hepsilon0 hepsilon1
      heta hetavr hA₂inner hA₂dense' hRregular hA hA₁ hA₂ hU hmass hhigh
  obtain ⟨y, hslice, hfree, hdense⟩ :=
    CyclicDensityIncrement.exists_normalizedSlice_of_dLinfty_bound A
      (C.dilate v) (mul_nonneg (by positivity) hbeta0.le) hAfree hinc
  exact ⟨p', q, x, A₁, A₂, U, C, v, xi, y, hp'upper, hq, hA₁, hU,
    hA₁S, hA₂T, hUsub, hA₁dense, hCradius, hCpos, hRrankC, hCrank,
    hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular,
    hCsmall.trans hRsmall, hslice, hfree, hdense⟩

/-- Quantitative consumer interface for the source-ordered local step.
It retains exactly the sifting witnesses needed to bound the local entropy,
as well as the resulting rank and radius formulas. -/
theorem exists_positive_density_increment_slice_of_large_norm_stable_reflected_quantitative
    (B R : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta vr eta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (heta : 0 < eta) (hetavr : eta ≤ vr)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hTinner : T = (R.dilate (vr - eta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hRsmall : (R.dilate eta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (p' q : ℕ) (x : ZMod N) (A₁ A₂ U : Finset (ZMod N))
        (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      q = max (2 * p')
        (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (256 / epsilon)⌉₊) ∧
      A₁.Nonempty ∧ U.Nonempty ∧
      A₁ ⊆ S ∧
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x ∧
      U ⊆ A₁ - A₂ ∧
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (A₁.card : ℝ) / S.card ∧
      C.radius = min (R.dilate eta).radius
        (CyclicLocalChangSanders.stableCarrierControllerRadius
          (R.dilate eta)
          (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
            A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta)
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            epsilon beta)
          ((400 * ((2 ^
            CyclicImprovedLocalDensityIteration.reflectedStableEntropy
              A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta : ℕ) : ℝ) *
            (R.rank : ℝ))⁻¹)
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            epsilon beta
            (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
              A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta))) ∧
      0 < C.radius ∧
      R.rank ≤ C.rank ∧
      C.rank ≤ R.rank +
        CyclicImprovedLocalDensityIteration.reflectedStableEntropy
          A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) epsilon beta ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  obtain ⟨p', q, x, A₁, A₂, U, _Sbase, _Tbase, _zbase, _X,
      deltaStable, C, v, xi, y, hp', hq, _hq0, _hqEven, _hx,
      hA₁S, hA₂T, hUsub, hA₁dense, _hA₂dense, hU, _hSbase,
      _hSbaseSub, _hTbaseCard, _hTbaseSub, _hzbase, _hXeq, _hX,
      hdeltaFormula, _hdeltaStable, hCradius, hCpos, hRrankC, hCrank,
      hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall,
      hslice, hfree, hdense⟩ :=
    exists_positive_density_increment_slice_of_large_norm_stable_reflected
      B R A S T m p mNext hm hp hbeta0 hbeta1 hepsilon0 hepsilon1
      hRradius hRrank hmNext hdelta hinner heta hetavr hregular hRregular
      hA hAB hdensity hS hT hTinner hSsub hTsub hRsmall herror hlarge
      hAfree
  have haux0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hA₁ : A₁.Nonempty :=
    nonempty_of_positive_relative_density A₁ S haux0 hS hA₁dense
  subst deltaStable
  exact ⟨p', q, x, A₁, A₂, U, C, v, xi, y, hp', hq, hA₁, hU,
    hA₁S, hA₂T, hUsub, hA₁dense, hCradius, hCpos, hRrankC, hCrank,
    hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hslice,
    hfree, hdense⟩

/-- Concise consumer interface for the source-ordered local step.  The full
theorem above retains every Croot--Sisask witness for quantitative radius and
rank bookkeeping; the structural nested iteration only needs the resulting
regular slice. -/
theorem exists_positive_density_increment_slice_of_large_norm_stable_reflected_concise
    (B R : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ)
    {t delta vr eta beta epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (heta : 0 < eta) (hetavr : eta ≤ vr)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hTinner : T = (R.dilate (vr - eta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hRsmall : (R.dilate eta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      0 < C.radius ∧ R.rank ≤ C.rank ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + epsilon / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  obtain ⟨_p', _q, _x, _A₁, _A₂, _U, _Sbase, _Tbase, _zbase, _X,
      _deltaStable, C, v, xi, y, _hp', _hq, _hq0, _hqEven, _hx,
      _hA₁, _hA₂, _hUsub, _hA₁dense, _hA₂dense, _hUnonempty,
      _hSbase, _hSbaseSub,
      _hTbaseCard, _hTbaseSub, _hzbase, _hXeq, _hX, _hdeltaFormula,
      _hdeltaStable, _hCradius, hCpos, hRrankC, _hCrank, hvlow,
      hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hslice,
      hfree, hdense⟩ :=
    exists_positive_density_increment_slice_of_large_norm_stable_reflected
      B R A S T m p mNext hm hp hbeta0 hbeta1 hepsilon0 hepsilon1
      hRradius hRrank hmNext hdelta hinner heta hetavr hregular hRregular
      hA hAB hdensity hS hT hTinner hSsub hTsub hRsmall herror hlarge
      hAfree
  exact ⟨C, v, xi, y, hCpos, hRrankC, hvlow, hvhigh, hxiFormula,
    hxi, hxiv, hCregular, hCsmall, hslice, hfree, hdense⟩

end CyclicImprovedLocalDensityStep

end Erdos721
