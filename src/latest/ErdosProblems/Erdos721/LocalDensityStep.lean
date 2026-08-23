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

import ErdosProblems.Erdos721.LocalDensityIteration

/-!
# An iteration-safe local density-increment step

This file packages the checked local unbalancing, sifting, tested
almost-periodicity, and normalized-slice arguments into one combinatorial
step.  The hypotheses preceding the large weighted norm are the exact local
Bohr geometry used in the Kelley--Meka iteration.  The conclusion retains
the Croot--Sisask shift set, the exact positive radius, and both rank bounds,
so it can be iterated quantitatively.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalDensityStep

variable {N : ℕ} [NeZero N]

/-- A positive auxiliary relative density forces nonemptiness. -/
private lemma nonempty_of_positive_relative_density
    (A S : Finset (ZMod N)) {alpha : ℝ} (halpha : 0 < alpha)
    (hS : S.Nonempty) (hdense : alpha ≤ (A.card : ℝ) / S.card) :
    A.Nonempty := by
  by_contra hA
  rw [not_nonempty_iff_eq_empty.mp hA] at hdense
  simp at hdense
  exact (not_lt_of_ge hdense) halpha

/-- If `A₂` lies in the reflected translate `x - T`, translating the
difference set `A₁ - A₂` by `x` injects it into `S + T`.  This is the
finite-set geometry behind the carrier-loss estimate in the local
density-increment argument. -/
lemma card_shifted_difference_subset_add
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S T A₁ A₂ U : Finset G) (x : G)
    (hA₁ : A₁ ⊆ S)
    (hA₂ : A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x)
    (hU : U ⊆ A₁ - A₂) :
    U.card ≤ (S + T).card := by
  let e : G ↪ G := (Equiv.addRight x).toEmbedding
  have hmap : U.map e ⊆ S + T := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' := hU hw
    rw [Finset.mem_sub] at hw'
    obtain ⟨a, ha, b, hb, hab⟩ := hw'
    have haS := hA₁ ha
    have hbT := hA₂ hb
    rw [CyclicLocalSifting.reflectedTranslate] at hbT
    rw [Finset.mem_vadd_finset] at hbT
    obtain ⟨c, hc, hbc⟩ := hbT
    rw [Finset.mem_neg] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    rw [Finset.mem_add]
    refine ⟨a, haS, y, hy, ?_⟩
    rw [← hab]
    change a + y = (a - b) + x
    rw [vadd_eq_add] at hbc
    rw [← hbc]
    abel
  calc
    U.card = (U.map e).card := (Finset.card_map e).symm
    _ ≤ (S + T).card := Finset.card_le_card hmap

/-- When the two local factor sets use the same inner Bohr carrier, the
auxiliary shift set has cardinality at most `9^rank` times that carrier.
The estimate is independent of the absolute radius and is therefore safe
to iterate. -/
lemma card_shifted_difference_le_nine_pow_rank
    (H : CyclicBohr.Set N) (S A₁ A₂ U : Finset (ZMod N))
    (x : ZMod N) {u zeta : ℝ}
    (hH : 0 < H.radius) (hzetau : zeta < u)
    (hS : S = (H.dilate (u - zeta)).carrier)
    (hA₁ : A₁ ⊆ S)
    (hA₂ : A₂ ⊆ CyclicLocalSifting.reflectedTranslate S x)
    (hU : U ⊆ A₁ - A₂) :
    U.card ≤ 9 ^ H.rank * S.card := by
  let r : ℝ := u - zeta
  let K : CyclicBohr.Set N := H.dilate (2 * r)
  have hr : 0 < r := sub_pos.mpr hzetau
  have hsum : (H.dilate r).carrier + (H.dilate r).carrier ⊆ K.carrier := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    have hadd := CyclicBohr.Set.add_mem_dilate hr.le hr.le ha hb
    change a + b ∈ H.dilate (2 * r)
    rwa [two_mul]
  have hK : 0 < K.radius := by
    simp only [K, CyclicBohr.Set.radius_dilate]
    positivity
  have hdouble :=
    CyclicBohr.card_carrier_le_nine_pow_rank_mul_card_half K hK
  have hhalf :
      (K.dilate (1 / 2 : ℝ)).carrier = (H.dilate r).carrier := by
    ext z
    simp [K, r]
    ring_nf
  calc
    U.card ≤ (S + S).card :=
      card_shifted_difference_subset_add S S A₁ A₂ U x hA₁ hA₂ hU
    _ = ((H.dilate r).carrier + (H.dilate r).carrier).card := by
      rw [hS]
    _ ≤ K.carrier.card := Finset.card_le_card hsum
    _ ≤ 9 ^ K.rank * (K.dilate (1 / 2 : ℝ)).carrier.card := hdouble
    _ = 9 ^ H.rank * S.card := by
      rw [hhalf, hS]
      simp [K, r]

/-- The complete local positive-radius density-increment step, starting from
the weighted positive-definite norm which is the hypothesis of the general
case of Bloom--Sisask Proposition 10.

`B` is the current ambient Bohr set and `H` is the smaller Bohr set on which
tested almost-periodicity is bootstrapped.  The equality for `S` says that
the first sifted set is dense in a regular inner dilate of `H`; the last
containment keeps the newly constructed Bohr carrier inside the current
perturbation scale. -/
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
      (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) ^
          (-4096 *
            ((⌈1 + Real.log
              (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
            (2 : ℝ) ^ 2 / (epsilon / 256) ^ 2) *
          ((H.dilate zeta).carrier.card : ℝ) ≤ X.card ∧
      C.radius = min (H.dilate zeta).radius
        (CyclicLocalDensityIteration.positiveSmoothingRho epsilon A₁ U X) ∧
      0 < C.radius ∧
      H.rank ≤ C.rank ∧
      C.rank ≤ H.rank + CyclicChang.changRankBound X
        (CyclicLocalDensityIteration.positiveSmoothingEta epsilon A₁ U) ∧
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
      (1 + epsilon / 32) * beta ≤
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
  obtain ⟨X, C, v, xi, hX, hCradius, hCpos, hHrankC, hCrank,
      hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular, hCsmall, hinc⟩ :=
    CyclicLocalDensityIteration.exists_local_regular_bohr_density_increment_relative_positive
        H A A₁ A₂ U (B.dilate t).carrier.card mNext hHradius hHrank
        hmNext haux0 hauxhalf hbeta0 hdensity hzeta hzetau hA₁inner
        hA₁dense' hHregular hepsilon0 hepsilon1 hA hA₁ hA₂ hU hmass
        hhigh
  obtain ⟨y, hslice, hfree, hdense⟩ :=
    CyclicDensityIncrement.exists_normalizedSlice_of_dLinfty_bound A
      (C.dilate v)
      (mul_nonneg (by positivity) hbeta0.le) hAfree hinc
  exact ⟨p', q, x, A₁, A₂, U, X, C, v, xi, y, hp'upper, hq, hq0, hqEven,
    hx, hA₁S, hA₂T, hUsub, hA₁dense, hA₂dense, hX, hCradius, hCpos,
    hHrankC, hCrank, hvlow, hvhigh, hxiFormula, hxi, hxiv, hCregular,
    hCsmall.trans hHsmall, hslice, hfree, hdense⟩

end CyclicLocalDensityStep
end Erdos721
