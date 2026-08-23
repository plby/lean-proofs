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

import ErdosProblems.Erdos721.RelativeLifting
import APAP.Physics.Unbalancing
import APAP.Prereqs.FourierTransform.Convolution

/-!
# Positive-definite lifting on cyclic Bohr sets

This file proves the physical-space form of the positive-definite comparison
used in Proposition 19 of Bloom--Sisask.  A pointwise majorization of an inner
Bohr probability measure reduces an ordinary-convolution moment to shifted
moments against a positive-definite weight.  A finite-dimensional
Cauchy--Schwarz argument bounds every shifted moment by the corresponding
difference-convolution moment.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal Indicator mu NNReal Pointwise
  translate

namespace CyclicPositiveDefiniteLifting

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The vector whose Gram matrix expands a weighted difference-convolution
moment. -/
noncomputable def momentVector (g h : G → ℂ) (k : ℕ)
    (z : Fin k → G) : ℂ :=
  ∑ x, (∏ i, conj (g (x + z i))) * h x

/-- Polarized Gram identity for weighted difference-convolution moments. -/
lemma sum_momentVector_mul_conj
    (g₁ g₂ h₁ h₂ : G → ℂ) (k : ℕ) :
    ∑ z : Fin k → G, momentVector g₁ h₁ k z *
        conj (momentVector g₂ h₂ k z) =
      ⟪(g₁ ○ᵈ g₂) ^ k, h₁ ○ᵈ h₂⟫_[ℂ] := by
  calc
    _ = ∑ x : G, ∑ yz : G × G with yz.1 - yz.2 = x,
          h₁ yz.1 * conj (h₂ yz.2) *
            conj ((g₁ ○ᵈ g₂) (yz.1 - yz.2)) ^ k := by
      simp_rw [momentVector, dddconv_apply_sub, Finset.sum_fiberwise,
        ← univ_product_univ, sum_product]
      simp only [sum_pow', Fintype.sum_mul_sum, map_mul, map_sum, map_prod,
        Fintype.piFinset_univ, ← Complex.conj_mul', prod_mul_distrib]
      simp only [mul_sum, @sum_comm _ _ (Fin k → G), mul_comm (conj _),
        prod_mul_distrib, Pi.conj_apply]
      congr with x
      congr with y
      congr with z
      group
    _ = ∑ x : G, ∑ yz : G × G with yz.1 - yz.2 = x,
          h₁ yz.1 * conj (h₂ yz.2) *
            conj ((g₁ ○ᵈ g₂) x) ^ k := by
      congr! with x _ yz hyz
      simpa using hyz
    _ = _ := by
      rw [wInner_one_eq_sum]
      simp only [Pi.pow_apply, RCLike.inner_apply, map_pow]
      simp_rw [dddconv_apply h₁, sum_mul]
      simp only [Pi.conj_apply]

/-- Cauchy--Schwarz for the polarized moment-vector identity. -/
lemma norm_sum_momentVector_mul_conj_le
    (g₁ g₂ h₁ h₂ : G → ℂ) (k : ℕ) :
    ‖∑ z : Fin k → G, momentVector g₁ h₁ k z *
        conj (momentVector g₂ h₂ k z)‖ ≤
      Real.sqrt (∑ z : Fin k → G, ‖momentVector g₁ h₁ k z‖ ^ 2) *
        Real.sqrt (∑ z : Fin k → G, ‖momentVector g₂ h₂ k z‖ ^ 2) := by
  calc
    _ ≤ ∑ z : Fin k → G,
        ‖momentVector g₁ h₁ k z * conj (momentVector g₂ h₂ k z)‖ :=
      norm_sum_le _ _
    _ = ∑ z : Fin k → G,
        ‖momentVector g₁ h₁ k z‖ * ‖momentVector g₂ h₂ k z‖ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [norm_mul, RCLike.norm_conj]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

/-- The squared norm sum is the unpolarized complex moment. -/
lemma ofReal_sum_norm_momentVector_sq
    (g h : G → ℂ) (k : ℕ) :
    ((↑) : ℝ → ℂ) (∑ z : Fin k → G, ‖momentVector g h k z‖ ^ 2) =
      ⟪(g ○ᵈ g) ^ k, h ○ᵈ h⟫_[ℂ] := by
  rw [← sum_momentVector_mul_conj]
  push_cast
  apply Finset.sum_congr rfl
  intro z _
  rw [← Complex.ofReal_pow, Complex.sq_norm]
  exact (Complex.mul_conj _).symm

/-- Real form of the moment-vector norm identity. -/
lemma sum_norm_momentVector_sq_eq_weighted_dddconv_moment
    (f : G → ℝ) (ν : G → ℝ≥0) (h : G → ℂ)
    (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) :
    ∑ z : Fin k → G, ‖momentVector ((↑) ∘ f) h k z‖ ^ 2 =
      ∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ k := by
  let g : G → ℂ := Complex.ofReal ∘ f
  change ∑ z : Fin k → G, ‖momentVector g h k z‖ ^ 2 = _
  have hg : g ○ᵈ g = ((↑) : ℝ → ℂ) ∘ (f ○ᵈ f) := by
    exact (Complex.ofReal_comp_dddconv f f).symm
  apply Complex.ofReal_injective
  calc
    ((↑) : ℝ → ℂ)
        (∑ z : Fin k → G, ‖momentVector g h k z‖ ^ 2) =
        ⟪(g ○ᵈ g) ^ k, h ○ᵈ h⟫_[ℂ] :=
      ofReal_sum_norm_momentVector_sq (G := G) g h k
    _ = ((↑) : ℝ → ℂ) (∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ k) := by
      rw [hν, hg]
      simp only [wInner_one_eq_sum, Pi.pow_apply, RCLike.inner_apply,
        Function.comp_apply, map_pow, Complex.conj_ofReal]
      norm_cast

lemma translate_self_dddconv (h : G → ℂ) (t : G) :
    τ t h ○ᵈ τ t h = h ○ᵈ h := by
  rw [translate_dddconv, dddconv_translate, translate_translate]
  simp

lemma comp_neg_self_dddconv (f : G → ℝ) :
    (fun x ↦ f (-x)) ○ᵈ (fun x ↦ f (-x)) = f ○ᵈ f := by
  change conjneg f ○ᵈ conjneg f = f ○ᵈ f
  rw [dddconv_conjneg, ddconv_comm, ddconv_conjneg]

/-- The polarized moment associated to an ordinary self-convolution and a
translated positive-definite weight. -/
lemma sum_mixed_moment_eq_ofReal_shifted_ddconv_moment
    (f : G → ℝ) (ν : G → ℝ≥0) (h : G → ℂ)
    (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) (t : G) :
    ∑ z : Fin k → G,
        momentVector (Complex.ofReal ∘ f) (τ t h) k z *
          conj (momentVector (conjneg (Complex.ofReal ∘ f)) h k z) =
      ((↑) : ℝ → ℂ) (∑ x, (ν (x - t) : ℝ) * (f ∗ᵈ f) x ^ k) := by
  rw [sum_momentVector_mul_conj]
  have hg : (Complex.ofReal ∘ f) ○ᵈ conjneg (Complex.ofReal ∘ f) =
      Complex.ofReal ∘ (f ∗ᵈ f) := by
    rw [dddconv_conjneg, ← Complex.ofReal_comp_ddconv]
  have hh : τ t h ○ᵈ h = (↑) ∘ fun x ↦ ν (x - t) := by
    rw [translate_dddconv, hν]
    rfl
  rw [hg, hh]
  simp only [wInner_one_eq_sum, Pi.pow_apply, RCLike.inner_apply,
    Function.comp_apply, map_pow, Complex.conj_ofReal]
  norm_cast

/-- Positive-definite weighted moment comparison.  This is the physical-space
form of the Fourier estimate in Proposition 19 of Bloom--Sisask. -/
lemma shifted_ddconv_moment_le_dddconv_moment
    (f : G → ℝ) (ν : G → ℝ≥0) (h : G → ℂ)
    (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) (t : G) :
    ∑ x, (ν (x - t) : ℝ) * (f ∗ᵈ f) x ^ k ≤
      ∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ k := by
  let g : G → ℂ := Complex.ofReal ∘ f
  let fneg : G → ℝ := fun x ↦ f (-x)
  let R : ℝ := ∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ k
  have hshift : τ t h ○ᵈ τ t h = (↑) ∘ ν := by
    rw [translate_self_dddconv, hν]
  have hgneg : conjneg g = Complex.ofReal ∘ fneg := by
    funext x
    simp [g, fneg, conjneg_apply]
  have hA : ∑ z : Fin k → G, ‖momentVector g (τ t h) k z‖ ^ 2 = R := by
    simpa only [g, R] using
      sum_norm_momentVector_sq_eq_weighted_dddconv_moment f ν (τ t h) hshift k
  have hBraw :=
    sum_norm_momentVector_sq_eq_weighted_dddconv_moment fneg ν h hν k
  have hfneg : fneg ○ᵈ fneg = f ○ᵈ f := by
    exact comp_neg_self_dddconv f
  have hB : ∑ z : Fin k → G, ‖momentVector (conjneg g) h k z‖ ^ 2 = R := by
    rw [hgneg]
    rw [hBraw, hfneg]
  have hCS := norm_sum_momentVector_mul_conj_le
    g (conjneg g) (τ t h) h k
  rw [hA, hB] at hCS
  have hmix := sum_mixed_moment_eq_ofReal_shifted_ddconv_moment f ν h hν k t
  have hR : 0 ≤ R := by
    rw [← hA]
    positivity
  calc
    ∑ x, (ν (x - t) : ℝ) * (f ∗ᵈ f) x ^ k ≤
        ‖((↑) : ℝ → ℂ)
          (∑ x, (ν (x - t) : ℝ) * (f ∗ᵈ f) x ^ k)‖ := by
      rw [Complex.norm_real]
      exact le_abs_self _
    _ = ‖∑ z : Fin k → G,
        momentVector g (τ t h) k z *
          conj (momentVector (conjneg g) h k z)‖ := by
      rw [hmix]
    _ ≤ Real.sqrt R * Real.sqrt R := hCS
    _ = R := by
      rw [← sq]
      exact Real.sq_sqrt hR

/-- A pointwise measure majorization and positive-definite factorization imply
the weighted ordinary-to-difference convolution comparison. -/
lemma weighted_ddconv_norm_le_two_mul_dddconv_norm
    (f : G → ℝ) (ν : G → ℝ≥0) (h : G → ℂ)
    (hν : h ○ᵈ h = (↑) ∘ ν) (I O : Finset G) (hO : O.Nonempty)
    (hmajor : ∀ x, μ I x ≤ 2 * (μ O ∗ᵈ ν) x)
    (p : ℕ) (hp0 : p ≠ 0) (hpEven : Even p) :
    ‖f ∗ᵈ f‖_[p, μ I] ≤ 2 * ‖f ○ᵈ f‖_[p, ν] := by
  have hpPos : 0 < p := Nat.pos_of_ne_zero hp0
  have hcoe : (((↑) : ℝ≥0 → ℝ) ∘ (μ_[ℝ≥0] O ∗ᵈ ν)) =
      μ_[ℝ] O ∗ᵈ (((↑) : ℝ≥0 → ℝ) ∘ ν) := by
    simpa only [NNReal.coe_comp_mu] using
      NNReal.coe_comp_ddconv (μ_[ℝ≥0] O) ν
  have hmajorR : ∀ x, μ_[ℝ] I x ≤
      2 * (μ_[ℝ] O ∗ᵈ (((↑) : ℝ≥0 → ℝ) ∘ ν)) x := by
    intro x
    calc
      μ_[ℝ] I x = (↑(μ_[ℝ≥0] I x) : ℝ) := (NNReal.coe_mu I x).symm
      _ ≤ (↑(2 * (μ_[ℝ≥0] O ∗ᵈ ν) x) : ℝ) :=
        NNReal.coe_le_coe.mpr (hmajor x)
      _ = 2 * (μ_[ℝ] O ∗ᵈ (((↑) : ℝ≥0 → ℝ) ∘ ν)) x := by
        rw [NNReal.coe_mul]
        norm_num
  have hpow : ‖f ∗ᵈ f‖_[p, μ I] ^ p ≤
      2 * ‖f ○ᵈ f‖_[p, ν] ^ p := by
    rw [wLpNorm_pow_eq_sum_norm hp0, wLpNorm_pow_eq_sum_norm hp0]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_mu,
      Real.norm_eq_abs, hpEven.pow_abs]
    calc
      ∑ x, μ_[ℝ] I x * (f ∗ᵈ f) x ^ p ≤
          ∑ x, (2 * (μ_[ℝ] O ∗ᵈ (((↑) : ℝ≥0 → ℝ) ∘ ν)) x) *
            (f ∗ᵈ f) x ^ p := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_right
        · exact hmajorR x
        · exact hpEven.pow_nonneg _
      _ = 2 * ∑ x, (μ_[ℝ] O ∗ᵈ (((↑) : ℝ≥0 → ℝ) ∘ ν)) x *
          (f ∗ᵈ f) x ^ p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 2 * ∑ a, (↑(μ O a) : ℝ) *
          ∑ x, (ν (x - a) : ℝ) * (f ∗ᵈ f) x ^ p := by
        congr 1
        rw [sum_ddconv_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.addLeft a) _ _
          (fun b ↦ by simp [Function.comp_apply]; ring)
      _ ≤ 2 * ∑ a, (↑(μ O a) : ℝ) *
          ∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ p := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left
        · exact shifted_ddconv_moment_le_dddconv_moment f ν h hν p a
        · exact (mu_nonneg (K := ℝ) (s := O)) a
      _ = 2 * ∑ x, (ν x : ℝ) * (f ○ᵈ f) x ^ p := by
        rw [← Finset.sum_mul, sum_mu ℝ hO, one_mul]
  refine le_of_pow_le_pow_left₀ hp0 (by positivity) (hpow.trans ?_)
  rw [mul_pow]
  gcongr
  exact (show (2 : ℝ) ≤ 2 ^ p by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr hp0))

/-- A probability weight supported on differences that keep `I` inside `O`
pointwise majorizes the normalized indicator of `I`. -/
lemma probability_majorization
    (I O : Finset G) (ν : G → ℝ≥0)
    (hI : I.Nonempty) (hO : O.Nonempty)
    (hνsum : ∑ x, ν x = 1)
    (hgeom : ∀ x ∈ I, ∀ y, ν y ≠ 0 → x - y ∈ O)
    (hcard : O.card ≤ 2 * I.card) :
    ∀ x, μ I x ≤ 2 * (μ O ∗ᵈ ν) x := by
  intro x
  by_cases hx : x ∈ I
  · have hconv : (μ O ∗ᵈ ν) x = (O.card : ℝ≥0)⁻¹ := by
      rw [ddconv_eq_sum_sub']
      calc
        ∑ t, μ O t * ν (x - t) = ∑ t, (O.card : ℝ≥0)⁻¹ * ν (x - t) := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases hν : ν (x - t) = 0
          · simp [hν]
          · have htO : t ∈ O := by
              have := hgeom x hx (x - t) hν
              simpa using this
            simp [mu_apply, htO]
        _ = (O.card : ℝ≥0)⁻¹ * ∑ t, ν (x - t) := by rw [Finset.mul_sum]
        _ = (O.card : ℝ≥0)⁻¹ := by
          have hshift : ∑ t, ν (x - t) = ∑ t, ν t := by
            exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun t ↦ by rfl)
          rw [hshift, hνsum, mul_one]
    rw [mu_apply, if_pos hx, hconv]
    simp only [mul_one]
    have hIpos : (0 : ℝ≥0) < I.card := by exact_mod_cast hI.card_pos
    have hOpos : (0 : ℝ≥0) < O.card := by exact_mod_cast hO.card_pos
    have hdiv : (1 : ℝ≥0) / I.card ≤ 2 / O.card := by
      rw [div_le_div_iff₀ hIpos hOpos]
      simpa using (show (O.card : ℝ≥0) ≤ 2 * I.card by exact_mod_cast hcard)
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  · simp [mu_apply, hx]

/-- The normalized positive-definite weight built from two finite sets. -/
noncomputable def positiveDefiniteWeight (S T : Finset G) : G → ℝ≥0 :=
  (μ_[ℝ≥0] S ○ᵈ μ S) ∗ᵈ (μ_[ℝ≥0] T ○ᵈ μ T)

/-- A complex square root of `positiveDefiniteWeight`. -/
noncomputable def positiveDefiniteRoot (S T : Finset G) : G → ℂ :=
  (↑) ∘ ((↑) ∘ (μ_[ℝ≥0] S ∗ᵈ μ T) : G → ℝ)

lemma positiveDefiniteRoot_factor (S T : Finset G) :
    positiveDefiniteRoot S T ○ᵈ positiveDefiniteRoot S T =
      (↑) ∘ positiveDefiniteWeight S T := by
  funext x
  simp only [positiveDefiniteRoot, positiveDefiniteWeight, Function.comp_apply,
    ← Complex.ofReal_dddconv, ← NNReal.coe_dddconv, ← NNReal.coe_ddconv]
  exact congrArg (fun z : ℝ≥0 ↦ (z : ℂ))
    (congrFun (dddconv_ddconv_dddconv_comm
      (μ_[ℝ≥0] S) (μ_[ℝ≥0] S) (μ_[ℝ≥0] T) (μ_[ℝ≥0] T)).symm x)

lemma positiveDefiniteWeight_sum (S T : Finset G)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    ∑ x, positiveDefiniteWeight S T x = 1 := by
  simp [positiveDefiniteWeight, sum_ddconv, sum_dddconv, sum_mu ℝ≥0 hS,
    sum_mu ℝ≥0 hT]

section ZMod

variable {N : ℕ} [NeZero N]

lemma positiveDefiniteWeight_support_subset_dilate
    (B : CyclicBohr.Set N) {delta : ℝ} (hdelta : 0 ≤ delta)
    (S T : Finset (ZMod N))
    (hS : S ⊆ (B.dilate delta).carrier)
    (hT : T ⊆ (B.dilate delta).carrier) :
    Function.support (positiveDefiniteWeight S T) ⊆
      ((B.dilate (4 * delta)).carrier : Set (ZMod N)) := by
  intro y hy
  have hy' := support_ddconv_subset
    (μ_[ℝ≥0] S ○ᵈ μ S) (μ_[ℝ≥0] T ○ᵈ μ T) hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  have hu' := support_dddconv_subset (μ_[ℝ≥0] S) (μ_[ℝ≥0] S) hu
  have hv' := support_dddconv_subset (μ_[ℝ≥0] T) (μ_[ℝ≥0] T) hv
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hu'
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hv'
  rw [support_mu] at hs₁ hs₂ ht₁ ht₂
  have hs₁B := hS hs₁
  have hs₂B := hS hs₂
  have ht₁B := hT ht₁
  have ht₂B := hT ht₂
  have hsubS : s₁ - s₂ ∈ B.dilate (delta + delta) :=
    CyclicBohr.Set.sub_mem_dilate hdelta hdelta hs₁B hs₂B
  have hsubT : t₁ - t₂ ∈ B.dilate (delta + delta) :=
    CyclicBohr.Set.sub_mem_dilate hdelta hdelta ht₁B ht₂B
  have hadd := CyclicBohr.Set.add_mem_dilate
    (B := B) (add_nonneg hdelta hdelta) (add_nonneg hdelta hdelta) hsubS hsubT
  change s₁ - s₂ + (t₁ - t₂) ∈ B.dilate (4 * delta)
  simpa only [show (delta + delta) + (delta + delta) = 4 * delta by ring] using hadd

lemma controlled_ratio_le_two
    (I O : Finset (ZMod N)) (m : ℕ) (hm : 0 < m)
    (hregular : (10 * m) * O.card ≤ (10 * m + 1) * I.card) :
    O.card ≤ 2 * I.card := by
  have hcoef : 10 * m + 1 ≤ 2 * (10 * m) := by omega
  have hmul : (10 * m) * O.card ≤ (10 * m) * (2 * I.card) := by
    calc
      (10 * m) * O.card ≤ (10 * m + 1) * I.card := hregular
      _ ≤ (2 * (10 * m)) * I.card := Nat.mul_le_mul_right I.card hcoef
      _ = (10 * m) * (2 * I.card) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Pointwise Bohr majorization for the positive-definite nested-dilate
weight. -/
lemma bohr_probability_majorization
    (B : CyclicBohr.Set N) (m : ℕ) (hm : 0 < m)
    {t delta : ℝ} (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular : (10 * m) * (B.dilate (t + delta)).carrier.card ≤
      (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (S T : Finset (ZMod N)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier) :
    ∀ x, μ (B.dilate (t - delta)).carrier x ≤
      2 * (μ (B.dilate (t + delta)).carrier ∗ᵈ
        positiveDefiniteWeight S T) x := by
  apply probability_majorization
  · exact (B.dilate (t - delta)).carrier_nonempty
  · exact (B.dilate (t + delta)).carrier_nonempty
  · exact positiveDefiniteWeight_sum S T hS hT
  · intro x hx y hy
    have hyraw := positiveDefiniteWeight_support_subset_dilate
      B (show 0 ≤ delta / 4 by positivity) S T hSsub hTsub hy
    have hyB : y ∈ B.dilate delta := by
      change y ∈ B.dilate (4 * (delta / 4)) at hyraw
      simpa only [show 4 * (delta / 4) = delta by ring] using hyraw
    have hxy : x - y ∈ B.dilate ((t - delta) + delta) :=
      CyclicBohr.Set.sub_mem_dilate (sub_nonneg.mpr hdeltat.le) hdelta.le hx hyB
    have hxy' : x - y ∈ B.dilate t := by
      simpa only [show (t - delta) + delta = t by ring] using hxy
    exact CyclicBohr.Set.dilate_mono B (show 0 ≤ t by linarith)
      (show t ≤ t + delta by linarith) hxy'
  · exact controlled_ratio_le_two _ _ m hm hregular

/-- Cyclic Bohr-set version of the positive-definite lifting estimate
(Bloom--Sisask, Proposition 19), with an explicit factor `2`. -/
theorem bohr_ddconv_norm_le_two_mul_dddconv_norm
    (B : CyclicBohr.Set N) (m : ℕ) (hm : 0 < m)
    {t delta : ℝ} (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular : (10 * m) * (B.dilate (t + delta)).carrier.card ≤
      (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (S T : Finset (ZMod N)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (f : ZMod N → ℝ) (p : ℕ) (hp0 : p ≠ 0) (hpEven : Even p) :
    ‖f ∗ᵈ f‖_[p, μ (B.dilate (t - delta)).carrier] ≤
      2 * ‖f ○ᵈ f‖_[p, positiveDefiniteWeight S T] := by
  apply weighted_ddconv_norm_le_two_mul_dddconv_norm f
    (positiveDefiniteWeight S T) (positiveDefiniteRoot S T)
  · exact positiveDefiniteRoot_factor S T
  · exact (B.dilate (t + delta)).carrier_nonempty
  · exact bohr_probability_majorization B m hm hdelta hdeltat hregular
      S T hS hT hSsub hTsub
  · exact hp0
  · exact hpEven

end ZMod

end CyclicPositiveDefiniteLifting
end Erdos721
