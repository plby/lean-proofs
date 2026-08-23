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

import ErdosProblems.Erdos721.LocalUnbalancing
import APAP.Physics.DRC

/-!
# Averaging and local sifting

The positive-definite weight used in the Bohr-set argument is an average of
difference-convolution weights attached to a translated pair of its two
factor sets.  This file makes that averaging identity explicit and extracts
one translated pair on which the relevant weighted norm is at least its
positive-definite average.  This is the bridge to dependent random choice.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise translate

namespace CyclicLocalSifting

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The reflected translate `x - T`. -/
def reflectedTranslate (T : Finset G) (x : G) : Finset G := x +ᵥ (-T)

@[simp] lemma card_reflectedTranslate (T : Finset G) (x : G) :
    (reflectedTranslate T x).card = T.card := by
  simp [reflectedTranslate]

lemma reflectedTranslate_nonempty {T : Finset G} (hT : T.Nonempty) (x : G) :
    (reflectedTranslate T x).Nonempty := by
  simpa [reflectedTranslate] using
    (hT.neg.vadd_finset : (x +ᵥ (-T)).Nonempty)

/-- The translated-pair difference weight is a translate of the convolution
root of the positive-definite weight. -/
lemma mu_dddconv_reflectedTranslate
    (S T : Finset G) (x : G) :
    μ_[ℝ≥0] S ○ᵈ μ_[ℝ≥0] (reflectedTranslate T x) =
      τ (-x) (μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) := by
  rw [reflectedTranslate, ← translate_mu, ← conjneg_mu,
    dddconv_translate, dddconv_conjneg]

lemma mu_dddconv_reflectedTranslate_apply
    (S T : Finset G) (x y : G) :
    (μ_[ℝ≥0] S ○ᵈ μ_[ℝ≥0] (reflectedTranslate T x)) y =
      (μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) (y + x) := by
  rw [mu_dddconv_reflectedTranslate, translate_apply]
  simp

/-- Exact mixture identity for the nested positive-definite weight. -/
lemma positiveDefiniteWeight_eq_sum_translatedPair
    (S T : Finset G) (y : G) :
    CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T y =
      ∑ x, (μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) x *
        (μ_[ℝ≥0] S ○ᵈ
          μ_[ℝ≥0] (reflectedTranslate T x)) y := by
  rw [CyclicPositiveDefiniteLifting.positiveDefiniteWeight,
    dddconv_ddconv_dddconv_comm, dddconv_eq_sum_add]
  apply Finset.sum_congr rfl
  intro x _
  rw [mu_dddconv_reflectedTranslate_apply]
  simp [mul_comm]

/-- The weighted `p`-th moment for the positive-definite weight is the
average of the translated-pair weighted moments. -/
lemma positiveDefiniteWeight_moment_eq_average
    (S T : Finset G) (F : G → ℝ) (p : ℕ) :
    ∑ y, (CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T y : ℝ) *
        |F y| ^ p =
      ∑ x, ((μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) x : ℝ) *
        ∑ y, ((μ_[ℝ≥0] S ○ᵈ
            μ_[ℝ≥0] (reflectedTranslate T x)) y : ℝ) * |F y| ^ p := by
  calc
    _ = ∑ y, ∑ x,
        (((μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) x : ℝ) *
          ((μ_[ℝ≥0] S ○ᵈ
            μ_[ℝ≥0] (reflectedTranslate T x)) y : ℝ)) * |F y| ^ p := by
      apply Finset.sum_congr rfl
      intro y _
      rw [positiveDefiniteWeight_eq_sum_translatedPair]
      push_cast
      rw [Finset.sum_mul]
    _ = ∑ x, ∑ y,
        (((μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T) x : ℝ) *
          ((μ_[ℝ≥0] S ○ᵈ
            μ_[ℝ≥0] (reflectedTranslate T x)) y : ℝ)) * |F y| ^ p := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- Some translated pair realizes at least the positive-definite weighted
norm.  The chosen translation lies in `S + T`, so the two carrier factors
intersect, exactly as required by dependent random choice. -/
theorem exists_reflectedTranslate_wLpNorm_ge
    (S T : Finset G) (hS : S.Nonempty) (hT : T.Nonempty)
    (F : G → ℝ) (p : ℕ) (hp : p ≠ 0) :
    ∃ x ∈ S + T,
      ‖F‖_[p, CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T] ≤
        ‖F‖_[p, μ S ○ᵈ μ (reflectedTranslate T x)] := by
  let q : G → ℝ≥0 := μ_[ℝ≥0] S ∗ᵈ μ_[ℝ≥0] T
  let L : ℝ :=
    ‖F‖_[p, CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T]
  have hqsum : ∑ x, q x = 1 := by
    simp [q, sum_ddconv, sum_mu ℝ≥0 hS, sum_mu ℝ≥0 hT]
  have hqsupport : Function.support q ⊆ (S + T : Finset G) := by
    simpa [q, support_mu] using
      support_ddconv_subset (μ_[ℝ≥0] S) (μ_[ℝ≥0] T)
  have hqnonempty : (Function.support q).Nonempty := by
    by_contra hne
    have hempty : Function.support q = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : q = 0 := by
      funext x
      by_contra hx
      have hx' : x ∈ Function.support q := hx
      rw [hempty] at hx'
      simpa using hx'
    simp [hzero] at hqsum
  by_contra hnot
  push Not at hnot
  have hstrict (x : G) (hx : x ∈ Function.support q) :
      ‖F‖_[p, μ S ○ᵈ μ (reflectedTranslate T x)] < L := by
    simpa [L] using hnot x (hqsupport hx)
  have hLpos : 0 < L := by
    by_contra hL
    have hLzero : L = 0 := le_antisymm (le_of_not_gt hL) wLpNorm_nonneg
    obtain ⟨x, hx⟩ := hqnonempty
    have := hstrict x hx
    rw [hLzero] at this
    exact (not_lt_of_ge wLpNorm_nonneg) this
  have havg :
      L ^ p = ∑ x, (q x : ℝ) *
        ‖F‖_[p, μ S ○ᵈ μ (reflectedTranslate T x)] ^ p := by
    rw [show L =
      ‖F‖_[p, CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T] by rfl,
      wLpNorm_pow_eq_sum_norm hp]
    simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs]
    rw [positiveDefiniteWeight_moment_eq_average]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [wLpNorm_pow_eq_sum_norm hp]
    simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs]
  have hlt :
      ∑ x, (q x : ℝ) *
          ‖F‖_[p, μ S ○ᵈ μ (reflectedTranslate T x)] ^ p <
        ∑ x, (q x : ℝ) * L ^ p := by
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : q x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ wLpNorm_nonneg (hstrict x hx).le p) (by positivity)
    · obtain ⟨x, hx⟩ := hqnonempty
      refine ⟨x, Finset.mem_univ x, ?_⟩
      exact mul_lt_mul_of_pos_left
        (pow_lt_pow_left₀ (hstrict x hx) wLpNorm_nonneg hp)
        (by exact_mod_cast (pos_iff_ne_zero.2 hx))
  rw [← Finset.sum_mul, show ∑ x, (q x : ℝ) = 1 by exact_mod_cast hqsum,
    one_mul, ← havg] at hlt
  exact (lt_irrefl _ hlt)

/-- If `x` is represented as an element of `S + T`, then `S` intersects the
reflected translate `x - T`. -/
lemma inter_reflectedTranslate_nonempty
    (S T : Finset G) {x : G} (hx : x ∈ S + T) :
    (S ∩ reflectedTranslate T x).Nonempty := by
  rw [Finset.mem_add] at hx
  obtain ⟨s, hs, t, ht, rfl⟩ := hx
  refine ⟨s, Finset.mem_inter.2 ⟨hs, ?_⟩⟩
  rw [reflectedTranslate, Finset.mem_vadd_finset]
  refine ⟨-t, by simpa using ht, by simp⟩

/-- Positivity of the weighted correlation norm when the two carrier sets
intersect. -/
lemma indicator_dddconv_wLpNorm_pos
    {B₁ B₂ A : Finset G} {p : ℕ} (hp : p ≠ 0)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    0 < ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
  rw [wLpNorm_pow_eq_sum_norm hp]
  refine sum_pos' (fun x _ ↦ by positivity) ⟨0, mem_univ _,
    smul_pos ?_ <| pow_pos ?_ _⟩
  · rwa [pos_iff_ne_zero, ← Function.mem_support, support_dddconv,
      support_mu, support_mu, ← coe_sub, mem_coe, zero_mem_sub_iff,
      not_disjoint_iff_nonempty_inter] <;> exact mu_nonneg
  · rw [norm_pos_iff, ← Function.mem_support, support_dddconv,
      Set.support_indicator_one]
    any_goals exact Set.indicator_one_nonneg
    exact hA.to_set.zero_mem_sub

/-- General sifting without an auxiliary witness assumption.  Adding the
positive constant `delta / 8` to the complement test makes its support all
of `G`; the resulting error is absorbed by asking for
`epsilon⁻¹ log (8/delta) ≤ p`. -/
theorem sifting_total
    (B₁ B₂ A : Finset G) {epsilon delta : ℝ} {p : ℕ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 < delta) (hpEven : Even p) (hp2 : 2 ≤ p)
    (hpexp : epsilon⁻¹ * Real.log (8 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      1 - delta ≤ ∑ x ∈ s p epsilon B₁ B₂ A,
        (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x ∧
      (4 : ℝ)⁻¹ *
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
            A.card ^ (2 * p) ≤ (A₁.card : ℝ) / B₁.card ∧
      (4 : ℝ)⁻¹ *
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
            A.card ^ (2 * p) ≤ (A₂.card : ℝ) / B₂.card := by
  let U := s p epsilon B₁ B₂ A
  let theta : ℝ≥0 := ⟨delta / 8, by positivity⟩
  let test : G → ℝ≥0 := 𝟭_[((U : Finset G)ᶜ : Set G), ℝ≥0] + fun _ ↦ theta
  have htestpos (x : G) : test x ≠ 0 := by
    have htheta : 0 < theta := by
      rw [← NNReal.coe_pos]
      change 0 < delta / 8
      positivity
    change 𝟭_[((U : Finset G)ᶜ : Set G), ℝ≥0] x + theta ≠ 0
    exact ne_of_gt (add_pos_of_nonneg_of_pos (by positivity) htheta)
  have hBcopy := hB
  obtain ⟨b, hb⟩ := hBcopy
  have hb₁ : b ∈ B₁ := (Finset.mem_inter.mp hb).1
  have hb₂ : b ∈ B₂ := (Finset.mem_inter.mp hb).2
  have hAcopy := hA
  obtain ⟨a, ha⟩ := hAcopy
  have hwitness : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∈ Function.support test := by
    refine ⟨0, ?_, ?_, htestpos 0⟩
    · rw [Finset.mem_sub]
      exact ⟨b, hb₁, b, hb₂, sub_self b⟩
    · rw [Finset.mem_sub]
      exact ⟨a, ha, a, ha, sub_self a⟩
  obtain ⟨A₁, hA₁B, A₂, hA₂B, htest, hA₁card, hA₂card⟩ :=
    drc hp2 test hwitness hB hA
  have hnormpos := indicator_dddconv_wLpNorm_pos
    (show p ≠ 0 by omega) hB hA
  have hA₁ : A₁.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty.mp hne] at hA₁card
    simp only [Finset.card_empty, Nat.cast_zero, zero_div] at hA₁card
    have hleft : 0 < (4 : ℝ)⁻¹ *
        ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
          A.card ^ (2 * p) := by
      rw [pow_mul']
      positivity
    exact (not_lt_of_ge hA₁card) hleft
  have hA₂ : A₂.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty.mp hne] at hA₂card
    simp only [Finset.card_empty, Nat.cast_zero, zero_div] at hA₂card
    have hleft : 0 < (4 : ℝ)⁻¹ *
        ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
          A.card ^ (2 * p) := by
      rw [pow_mul']
      positivity
    exact (not_lt_of_ge hA₂card) hleft
  refine ⟨A₁, hA₁B, A₂, hA₂B, ?_, hA₁card, hA₂card⟩
  have hcorrNonneg : 0 ≤ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂ :=
    dddconv_nonneg mu_nonneg mu_nonneg
  have htest_apply (x : G) :
      (test x : ℝ) = (if x ∈ U then 0 else 1) + delta / 8 := by
    have htest_eq : test x =
        𝟭_[((U : Finset G)ᶜ : Set G), ℝ≥0] x + theta := rfl
    rw [htest_eq]
    push_cast
    simp [theta, Set.indicator_apply]
    rfl
  have htestInner :
      ⟪μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂, (↑) ∘ test⟫_[ℝ] =
        ∑ x ∈ Uᶜ, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x + delta / 8 := by
    rw [wInner_one_eq_sum]
    simp only [Function.comp_apply, Real.inner_apply, conj_trivial]
    calc
      ∑ x, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x * (test x : ℝ) =
          ∑ x, (if x ∈ Uᶜ then (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x else 0) +
            ∑ x, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x * (delta / 8) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ Uᶜ
        · have hxU : x ∉ U := by simpa using hx
          rw [htest_apply]
          simp [hxU]
          ring
        · have hxU : x ∈ U := by simpa using hx
          rw [htest_apply]
          simp [hxU]
      _ = ∑ x ∈ Uᶜ, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x + delta / 8 := by
        rw [← Finset.sum_filter, ← Finset.sum_mul, sum_dddconv]
        simp only [starRingEnd_apply, star_trivial]
        rw [sum_mu ℝ hA₁, sum_mu ℝ hA₂]
        rw [Finset.filter_univ_mem]
        ring
  have hmomentTest :
      ∑ x, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
          (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * test x =
        ∑ x ∈ Uᶜ, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
            (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p +
          (delta / 8) *
            ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
              μ B₁ ○ᵈ μ B₂] ^ p := by
    let H : G → ℝ := fun x ↦
      (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
        (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p
    have hindicatorCorr : 0 ≤ 𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A] :=
      dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg
    calc
      ∑ x, H x * (test x : ℝ) =
          ∑ x, (if x ∈ Uᶜ then H x else 0) +
            ∑ x, H x * (delta / 8) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ Uᶜ
        · have hxU : x ∉ U := by simpa using hx
          rw [htest_apply]
          simp [hxU]
          ring
        · have hxU : x ∈ U := by simpa using hx
          rw [htest_apply]
          simp [hxU]
      _ = ∑ x ∈ Uᶜ, H x + (delta / 8) * ∑ x, H x := by
        rw [← Finset.sum_filter, ← Finset.sum_mul]
        rw [Finset.filter_univ_mem]
        ring
      _ = _ := by
        rw [wLpNorm_pow_eq_sum_norm (show p ≠ 0 by omega)]
        simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs,
          NNReal.coe_dddconv]
        simp_rw [abs_of_nonneg (hindicatorCorr _)]
        simp only [H, NNReal.coe_comp_mu]
  have houtside :
      ∑ x ∈ Uᶜ, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
          (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p ≤
        (1 - epsilon) ^ p *
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
            μ B₁ ○ᵈ μ B₂] ^ p := by
    calc
      _ ≤ ∑ x ∈ Uᶜ, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
          ((1 - epsilon) *
            ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
              μ B₁ ○ᵈ μ B₂]) ^ p := by
        gcongr with x hx
        · exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
        · exact dddconv_apply_nonneg Set.indicator_one_nonneg
            Set.indicator_one_nonneg x
        · simpa [U] using hx
      _ ≤ ∑ x, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
          ((1 - epsilon) *
            ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
              μ B₁ ○ᵈ μ B₂]) ^ p := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro x
        exact mul_nonneg (dddconv_apply_nonneg mu_nonneg mu_nonneg x)
          (hpEven.pow_nonneg _)
      _ = (1 - epsilon) ^ p *
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
            μ B₁ ○ᵈ μ B₂] ^ p := by
        rw [mul_pow, ← Finset.sum_mul, sum_dddconv]
        simp only [starRingEnd_apply, star_trivial]
        rw [sum_mu ℝ (hB.mono inter_subset_left),
          sum_mu ℝ (hB.mono inter_subset_right), one_mul, one_mul]
  have hexp : (1 - epsilon) ^ p ≤ delta / 8 := by
    calc
      (1 - epsilon) ^ p ≤ Real.exp (-epsilon) ^ p := by
        gcongr
        exact one_sub_le_exp_neg epsilon
      _ = Real.exp (-(epsilon * p)) := by
        rw [← neg_mul, Real.exp_mul, Real.rpow_natCast]
      _ ≤ Real.exp (-Real.log (8 / delta)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]
        exact (inv_mul_le_iff₀ hepsilon0).1 hpexp
      _ = delta / 8 := by
        rw [Real.exp_neg, Real.exp_log, inv_div]
        positivity
  rw [sub_le_comm]
  calc
    1 - ∑ x ∈ s p epsilon B₁ B₂ A,
        (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x =
        ∑ x ∈ Uᶜ, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      rw [sub_eq_iff_eq_add', show s p epsilon B₁ B₂ A = U by rfl,
        sum_add_sum_compl, sum_dddconv]
      simp only [starRingEnd_apply, star_trivial]
      rw [sum_mu ℝ hA₁, sum_mu ℝ hA₂, one_mul]
    _ ≤
        ⟪μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂, (↑) ∘ test⟫_[ℝ] := by
      rw [htestInner]
      linarith
    _ ≤ 2 * (
        ∑ x, (μ_[ℝ] B₁ ○ᵈ μ_[ℝ] B₂) x *
          (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * test x) /
        ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
          μ B₁ ○ᵈ μ B₂] ^ p := by
      rw [le_div_iff₀ hnormpos]
      exact htest
    _ ≤ 2 * ((1 - epsilon) ^ p + delta / 8) := by
      rw [hmomentTest]
      have hnormNonneg : 0 ≤
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
            μ B₁ ○ᵈ μ B₂] ^ p := by positivity
      have hnum := add_le_add houtside
        (le_refl ((delta / 8) *
          ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
            μ B₁ ○ᵈ μ B₂] ^ p))
      rw [← add_mul] at hnum
      apply (div_le_iff₀ hnormpos).2
      nlinarith
    _ ≤ delta := by nlinarith


/-- Dependent-random-choice sifting on one translated pair extracted from
the positive-definite weight.  The explicit witness hypothesis is exactly
the non-degenerate branch of APAP's general `sifting` lemma. -/
theorem sifting_on_reflectedTranslate
    (S T A : Finset G) {x : G} (hx : x ∈ S + T)
    {epsilon delta : ℝ} {p : ℕ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 < delta) (hpEven : Even p) (hp2 : 2 ≤ p)
    (hpexp : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hA : A.Nonempty)
    (hwitness : ∃ y,
      y ∈ S - reflectedTranslate T x ∧ y ∈ A - A ∧
      y ∉ s p epsilon S (reflectedTranslate T x) A) :
    ∃ A₁, A₁ ⊆ S ∧ ∃ A₂, A₂ ⊆ reflectedTranslate T x ∧
      1 - delta ≤
        ∑ y ∈ s p epsilon S (reflectedTranslate T x) A,
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y ∧
      (4 : ℝ)⁻¹ *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] ^ (2 * p) * A.card ^ (2 * p) ≤
        (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] ^ (2 * p) * A.card ^ (2 * p) ≤
        (A₂.card : ℝ) / T.card := by
  obtain ⟨A₁, hA₁S, A₂, hA₂T, hmass, hA₁, hA₂⟩ :=
    sifting S (reflectedTranslate T x) hepsilon0 hepsilon1 hdelta hpEven hp2 hpexp
      (inter_reflectedTranslate_nonempty S T hx) hA hwitness
  have hnormIndicator :
      ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
          μ S ○ᵈ μ (reflectedTranslate T x)] =
        (A.card : ℝ) ^ 2 *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] := by
    rw [← card_smul_mu ℝ A, smul_dddconv, dddconv_smul,
      wLpNorm_nsmul, wLpNorm_nsmul]
    push_cast
    simp only [star_trivial]
    ring
  refine ⟨A₁, hA₁S, A₂, hA₂T, hmass, ?_, ?_⟩
  · rw [hnormIndicator] at hA₁
    convert hA₁ using 1
    field_simp [show (A.card : ℝ) ≠ 0 by exact_mod_cast hA.card_ne_zero]
    ring
  · rw [card_reflectedTranslate] at hA₂
    rw [hnormIndicator] at hA₂
    convert hA₂ using 1
    field_simp [show (A.card : ℝ) ≠ 0 by exact_mod_cast hA.card_ne_zero]
    ring

/-- Unconditional dependent-random-choice sifting on a translated pair.
The small everywhere-positive perturbation in `sifting_total` removes the
auxiliary support witness required by the unperturbed test. -/
theorem sifting_total_on_reflectedTranslate
    (S T A : Finset G) {x : G} (hx : x ∈ S + T)
    {epsilon delta : ℝ} {p : ℕ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 < delta) (hpEven : Even p) (hp2 : 2 ≤ p)
    (hpexp : epsilon⁻¹ * Real.log (8 / delta) ≤ p)
    (hA : A.Nonempty) :
    ∃ A₁, A₁ ⊆ S ∧ ∃ A₂, A₂ ⊆ reflectedTranslate T x ∧
      1 - delta ≤
        ∑ y ∈ s p epsilon S (reflectedTranslate T x) A,
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) y ∧
      (4 : ℝ)⁻¹ *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] ^ (2 * p) * A.card ^ (2 * p) ≤
        (A₁.card : ℝ) / S.card ∧
      (4 : ℝ)⁻¹ *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] ^ (2 * p) * A.card ^ (2 * p) ≤
        (A₂.card : ℝ) / T.card := by
  obtain ⟨A₁, hA₁S, A₂, hA₂T, hmass, hA₁, hA₂⟩ :=
    sifting_total S (reflectedTranslate T x) A hepsilon0 hepsilon1 hdelta
      hpEven hp2 hpexp (inter_reflectedTranslate_nonempty S T hx) hA
  have hnormIndicator :
      ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p,
          μ S ○ᵈ μ (reflectedTranslate T x)] =
        (A.card : ℝ) ^ 2 *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p,
            μ S ○ᵈ μ (reflectedTranslate T x)] := by
    rw [← card_smul_mu ℝ A, smul_dddconv, dddconv_smul,
      wLpNorm_nsmul, wLpNorm_nsmul]
    simp only [star_trivial]
    ring
  refine ⟨A₁, hA₁S, A₂, hA₂T, hmass, ?_, ?_⟩
  · rw [hnormIndicator] at hA₁
    convert hA₁ using 1
    field_simp [show (A.card : ℝ) ≠ 0 by exact_mod_cast hA.card_ne_zero]
    ring
  · rw [card_reflectedTranslate] at hA₂
    rw [hnormIndicator] at hA₂
    convert hA₂ using 1
    field_simp [show (A.card : ℝ) ≠ 0 by exact_mod_cast hA.card_ne_zero]
    ring

end CyclicLocalSifting
end Erdos721
