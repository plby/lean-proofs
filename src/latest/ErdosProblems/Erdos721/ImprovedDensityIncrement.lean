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

import ErdosProblems.Erdos721.ImprovedBootstrapping

/-!
# The improved tested density increment

This file formalizes the second half of Bloom--Sisask's improved
bootstrapping lemma.  A Croot--Sisask convolution power is tested against
the current self-correlation, smoothed on a refined regular Bohr carrier,
and removed from the final density-increment norm without loss.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicImprovedDensityIncrement

variable {N : ℕ} [NeZero N]

lemma kernel_triple_indicator_neg_apply_zero_eq_sum
    (K : ZMod N → ℂ) (A₁ A₂ U : Finset (ZMod N)) :
    (K ∗ᵈ (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] A₂)) 0 =
      ∑ x ∈ U, (K ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x := by
  have hsum :
      ∑ x ∈ U, (K ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) x =
        ((K ∗ᵈ μ_[ℂ] A₁ ∗ᵈ μ_[ℂ] A₂) ○ᵈ 𝟭_[U]) 0 := by
    simp [dddconv_indicator_one_eq_sum]
  rw [hsum, dddconv_indicator_one]
  rw [ddconv_right_comm (K ∗ᵈ μ_[ℂ] A₁)]
  simp only [ddconv_assoc]

lemma complex_iter_mu_ddconv_mu_ddconv_mu_apply
    (T : Finset (ZMod N)) (k : ℕ) (A B : Finset (ZMod N)) (x : ZMod N) :
    (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x =
      (((μ_[ℝ] T ∗ᵈ^ k ∗ᵈ μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x : ℝ) : ℂ) := by
  have hiter : μ_[ℂ] T ∗ᵈ^ k =
      Complex.ofReal ∘ (μ_[ℝ] T ∗ᵈ^ k) := by
    funext y
    rw [← CyclicDensityIncrement.ofReal_comp_mu T]
    exact (Complex.ofReal_iterConv (μ_[ℝ] T) k y).symm
  rw [hiter, ← CyclicDensityIncrement.ofReal_comp_mu A,
    ← CyclicDensityIncrement.ofReal_comp_mu B,
    ← Complex.ofReal_comp_ddconv, ← Complex.ofReal_comp_ddconv]
  rfl

lemma norm_complex_boosted_tested_sub_eq_abs_real
    (T : Finset (ZMod N)) (k : ℕ) (A B U : Finset (ZMod N)) :
    ‖(∑ x ∈ U, (μ_[ℂ] T ∗ᵈ^ k ∗ᵈ μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x) -
        ∑ x ∈ U, (μ_[ℂ] A ∗ᵈ μ_[ℂ] B) x‖ =
      |(∑ x ∈ U, (μ_[ℝ] T ∗ᵈ^ k ∗ᵈ μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x) -
        ∑ x ∈ U, (μ_[ℝ] A ∗ᵈ μ_[ℝ] B) x| := by
  simp only [complex_iter_mu_ddconv_mu_ddconv_mu_apply,
    CyclicDensityIncrement.complex_mu_ddconv_mu_apply]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

lemma boosted_tested_correlation_error_of_dLinfty
    (X : Finset (ZMod N)) (k : ℕ)
    (A₁ A₂ U : Finset (ZMod N)) {epsilon : ℝ}
    (happrox :
      ‖(μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
          (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) -
        (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))‖_[∞] ≤ epsilon) :
    |(∑ x ∈ U,
        (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| ≤ epsilon := by
  have hzero :
      ‖(μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
            (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) 0 -
          (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂)) 0‖ ≤ epsilon := by
    calc
      _ = ‖((μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
              (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) -
            (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) 0‖ := rfl
      _ ≤ ‖(μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
              (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))) -
            (μ_[ℂ] A₁ ∗ᵈ 𝟭_[-U] ∗ᵈ μ_[ℂ] (-A₂))‖_[∞] :=
        MeasureTheory.norm_le_dLinftyNorm
      _ ≤ epsilon := happrox
  rw [kernel_triple_indicator_neg_apply_zero_eq_sum,
    CyclicDensityIncrement.triple_indicator_neg_apply_zero_eq_sum] at hzero
  have hcorrR : μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂ =
      μ_[ℝ] A₁ ∗ᵈ μ_[ℝ] (-A₂) := by
    rw [← ddconv_conjneg, conjneg_mu]
  rw [← ddconv_conjneg, conjneg_mu, hcorrR]
  rw [← norm_complex_boosted_tested_sub_eq_abs_real X k A₁ (-A₂) U]
  exact hzero

theorem exists_large_nonempty_boosted_approximation
    (A S P Q : Finset (ZMod N)) {K epsilon : ℝ} (k : ℕ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hk : k ≠ 0) (hK2 : 2 ≤ K)
    (hK : (A.addConst S : ℝ) ≤ K)
    (hS : S.Nonempty) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    ∃ T : Finset (ZMod N),
      K ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((Q.card : ℝ) / (P.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / epsilon ^ 2) * (S.card : ℝ) ≤ T.card ∧
      T.Nonempty ∧
      ‖μ_[ℂ] T ∗ᵈ^ k ∗ᵈ (μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q) -
          μ_[ℂ] A ∗ᵈ 𝟭_[P] ∗ᵈ μ_[ℂ] Q‖_[∞] ≤ epsilon := by
  let : MeasurableSpace (ZMod N) := ⊤
  obtain ⟨T, hTcard, hTapprox⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted
      epsilon hepsilon0 hepsilon1 k hk hK2 hK hS P Q hP hQ
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK2
  have hScardpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTpos : (0 : ℝ) < T.card :=
    (mul_pos (Real.rpow_pos_of_pos hKpos _) hScardpos).trans_le hTcard
  have hT : T.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hTpos
  exact ⟨T, by simpa using hTcard, hT, hTapprox⟩

lemma lower_inner_of_mass_on_high_set
    {G : Type*} [Fintype G] [DecidableEq G]
    (f g : G → ℝ) (U : Finset G) (scale : ℕ) {a b c : ℝ}
    (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hb : 0 ≤ 1 + b)
    (hmass : 1 - a ≤ ∑ x ∈ U, f x)
    (hhigh : ∀ x ∈ U, 1 + b ≤ scale • g x)
    (hnumerical : c ≤ (1 + b) * (1 - a)) :
    c ≤ scale • ⟪f, g⟫_[ℝ] := by
  calc
    c ≤ (1 + b) * (1 - a) := hnumerical
    _ ≤ (1 + b) * ∑ x ∈ U, f x := by gcongr
    _ = ∑ x ∈ U, (1 + b) * f x := by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ U, (scale • g x) * f x := by
      gcongr with x hx
      · exact hf x
      · exact hhigh x hx
    _ ≤ ∑ x : G, (scale • g x) * f x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro x _hx _hxU
      exact mul_nonneg (nsmul_nonneg (hg x) scale) (hf x)
    _ = scale • ⟪f, g⟫_[ℝ] := by
      simp only [nsmul_eq_mul, wInner_one_eq_sum, inner_apply, conj_trivial,
        mul_assoc, smul_sum]

lemma ddconv_selfCorrelation_apply_zero_eq_inner
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (f a : G → ℝ) :
    (f ∗ᵈ (a ○ᵈ a)) 0 = ⟪f, a ○ᵈ a⟫_[ℝ] := by
  rw [ddconv_eq_wInner_one]
  simp only [conj_trivial, translate_apply, sub_zero,
    dddconv_apply_neg, wInner_one_eq_sum, inner_apply]

lemma boosted_fourfold_apply_zero_eq_inner
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (K f a : G → ℝ) :
    (K ∗ᵈ (f ∗ᵈ (a ○ᵈ a))) 0 =
      ⟪K ∗ᵈ f, a ○ᵈ a⟫_[ℝ] := by
  rw [← ddconv_assoc, ddconv_selfCorrelation_apply_zero_eq_inner]

lemma complex_fourfold_apply
    (A₁ A₂ A : Finset (ZMod N)) (x : ZMod N) :
    (((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
        (μ_[ℂ] A ○ᵈ μ_[ℂ] A)) x) =
      ((((μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) ∗ᵈ
        (μ_[ℝ] A ○ᵈ μ_[ℝ] A)) x : ℝ) : ℂ) := by
  rw [← CyclicDensityIncrement.ofReal_comp_mu A₁,
    ← CyclicDensityIncrement.ofReal_comp_mu A₂,
    ← CyclicDensityIncrement.ofReal_comp_mu A,
    ← Complex.ofReal_comp_dddconv, ← Complex.ofReal_comp_dddconv,
    ← Complex.ofReal_comp_ddconv]
  rfl

lemma complex_boosted_fourfold_apply
    (X : Finset (ZMod N)) (k : ℕ)
    (A₁ A₂ A : Finset (ZMod N)) (x : ZMod N) :
    (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
        ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
          (μ_[ℂ] A ○ᵈ μ_[ℂ] A))) x =
      (((μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
        ((μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) ∗ᵈ
          (μ_[ℝ] A ○ᵈ μ_[ℝ] A))) x : ℝ) : ℂ) := by
  have hiter : μ_[ℂ] X ∗ᵈ^ k =
      Complex.ofReal ∘ (μ_[ℝ] X ∗ᵈ^ k) := by
    funext y
    rw [← CyclicDensityIncrement.ofReal_comp_mu X]
    exact (Complex.ofReal_iterConv (μ_[ℝ] X) k y).symm
  have hfourfold :
      (μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ (μ_[ℂ] A ○ᵈ μ_[ℂ] A) =
        Complex.ofReal ∘
          ((μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) ∗ᵈ
            (μ_[ℝ] A ○ᵈ μ_[ℝ] A)) := by
    funext y
    exact complex_fourfold_apply A₁ A₂ A y
  rw [hiter, hfourfold, ← Complex.ofReal_comp_ddconv]
  rfl

lemma complex_smoothed_boosted_fourfold_apply
    (C X : Finset (ZMod N)) (k : ℕ)
    (A₁ A₂ A : Finset (ZMod N)) (x : ZMod N) :
    (μ_[ℂ] C ∗ᵈ (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
        ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
          (μ_[ℂ] A ○ᵈ μ_[ℂ] A)))) x =
      (((μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
        ((μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) ∗ᵈ
          (μ_[ℝ] A ○ᵈ μ_[ℝ] A)))) x : ℝ) : ℂ) := by
  have hC : μ_[ℂ] C = Complex.ofReal ∘ μ_[ℝ] C := by
    exact (CyclicDensityIncrement.ofReal_comp_mu C).symm
  have hboosted :
      μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A)) =
        Complex.ofReal ∘
          (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
            ((μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) ∗ᵈ
              (μ_[ℝ] A ○ᵈ μ_[ℝ] A))) := by
    funext y
    exact complex_boosted_fourfold_apply X k A₁ A₂ A y
  rw [hC, hboosted, ← Complex.ofReal_comp_ddconv]
  rfl

lemma smoothed_boosted_fourfold_apply_zero_eq_inner
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (C K f a : G → ℝ) :
    (C ∗ᵈ (K ∗ᵈ (f ∗ᵈ (a ○ᵈ a)))) 0 =
      ⟪C ∗ᵈ K ∗ᵈ f, a ○ᵈ a⟫_[ℝ] := by
  rw [← ddconv_assoc, boosted_fourfold_apply_zero_eq_inner]

lemma norm_complex_smoothed_boosted_fourfold_sub_eq_abs_inner
    (C X : Finset (ZMod N)) (k : ℕ)
    (A₁ A₂ A : Finset (ZMod N)) :
    ‖(μ_[ℂ] C ∗ᵈ (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A)))) 0 -
        (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
          ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
            (μ_[ℂ] A ○ᵈ μ_[ℂ] A))) 0‖ =
      |⟪μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
            (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
          μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ] -
        ⟪μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
            (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
          μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ]| := by
  rw [complex_smoothed_boosted_fourfold_apply,
    complex_boosted_fourfold_apply,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    smoothed_boosted_fourfold_apply_zero_eq_inner,
    boosted_fourfold_apply_zero_eq_inner]

lemma abs_inner_sub_inner_le_of_boosted_smoothing
    (C X : Finset (ZMod N)) (hC : C.Nonempty) (k : ℕ)
    (A₁ A₂ A : Finset (ZMod N)) {error : ℝ}
    (hsmooth : ∀ x,
      ‖CyclicFourier.convolution
            (CyclicSpectralSmoothing.probabilityWeight C)
            (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
              ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
                (μ_[ℂ] A ○ᵈ μ_[ℂ] A))) x -
          (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
            ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
              (μ_[ℂ] A ○ᵈ μ_[ℂ] A))) x‖ ≤ error) :
    |⟪μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
        μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ] -
      ⟪μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
        μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ]| ≤ error := by
  have hzero := hsmooth 0
  rw [← congrFun
    (CyclicBoostedAlmostPeriodicity.mu_ddconv_eq_probabilityWeight_convolution
      hC (μ_[ℂ] X ∗ᵈ^ k ∗ᵈ
        ((μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
          (μ_[ℂ] A ○ᵈ μ_[ℂ] A)))) 0] at hzero
  rwa [norm_complex_smoothed_boosted_fourfold_sub_eq_abs_inner] at hzero

lemma dLinftyNorm_ddconv_le_of_nonnegative_probability
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (K f : G → ℝ) (hK : 0 ≤ K) (hf : 0 ≤ f)
    (hKsum : ∑ x, K x = 1) :
    ‖K ∗ᵈ f‖_[∞] ≤ ‖f‖_[∞] := by
  have hconv : 0 ≤ K ∗ᵈ f := ddconv_nonneg hK hf
  rw [dLinftyNorm_eq_iSup_norm]
  apply ciSup_le
  intro x
  rw [Real.norm_of_nonneg (hconv x), ddconv_eq_sum_sub']
  calc
    ∑ y, K y * f (x - y) ≤ ∑ y, K y * ‖f‖_[∞] := by
      gcongr with y
      · exact hK y
      · exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_le_dLinftyNorm (f := f) (i := x - y)))
    _ = ‖f‖_[∞] := by rw [← Finset.sum_mul, hKsum, one_mul]

lemma inner_kernel_correlation_self_eq
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (K A A₁ A₂ : G → ℝ) :
    ⟪K ∗ᵈ A₁ ○ᵈ A₂, A ○ᵈ A⟫_[ℝ] =
      ⟪K ∗ᵈ A, A ∗ᵈ A₂ ○ᵈ A₁⟫_[ℝ] := by
  calc
    _ = ⟪A ○ᵈ A, K ∗ᵈ A₁ ○ᵈ A₂⟫_[ℝ] := by
      rw [← conj_wInner_symm]
      simp only [conj_trivial]
    _ = _ := by
      rw [← wInner_one_dddconv_eq_ddconv_wInner_one, dddconv_right_comm,
        ddconv_dddconv_right_comm A,
        wInner_one_dddconv_eq_ddconv_wInner_one,
        ← dddconv_wInner_one_eq_wInner_one_ddconv, ← conj_wInner_symm]
      simp only [conj_trivial]

lemma scale_smul_dLinfty_mu_ddconv_eq_indicator_div
    (A C : Finset (ZMod N)) (scale : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (hdensity : alpha * scale = A.card)
    (hA : A.Nonempty) (hC : C.Nonempty) :
    scale • ‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] =
      ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] / alpha := by
  simp [eq_div_iff, halpha.ne', hA, hC, ← card_smul_mu,
    smul_ddconv, dLpNorm_nsmul, -nsmul_eq_mul]
  all_goals simp [← mul_assoc, mul_comm, ddconv_comm, hdensity]

lemma dL1Norm_mu_ddconv_mu_dddconv_mu_eq_one
    (A A₂ A₁ : Finset (ZMod N))
    (hA : A.Nonempty) (hA₂ : A₂.Nonempty) (hA₁ : A₁.Nonempty) :
    ‖μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁‖_[1] = 1 := by
  rw [dL1Norm_dddconv, dL1Norm_ddconv]
  · simp [hA, hA₂, hA₁]
  · exact mu_nonneg
  · exact mu_nonneg
  · exact ddconv_nonneg mu_nonneg mu_nonneg
  · exact mu_nonneg

lemma dLinftyNorm_smoothed_boosted_mu_le
    (C X A : Finset (ZMod N)) (k : ℕ)
    (hX : X.Nonempty) :
    ‖(μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k)) ∗ᵈ μ_[ℝ] A‖_[∞] ≤
      ‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] := by
  have hXnonneg : 0 ≤ μ_[ℝ] X ∗ᵈ^ k := iterConv_nonneg mu_nonneg
  have hXsum : ∑ x, (μ_[ℝ] X ∗ᵈ^ k) x = 1 := by
    rw [sum_iterConv, sum_mu ℝ hX, one_pow]
  have hCAnonneg : 0 ≤ μ_[ℝ] C ∗ᵈ μ_[ℝ] A :=
    ddconv_nonneg mu_nonneg mu_nonneg
  calc
    ‖(μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k)) ∗ᵈ μ_[ℝ] A‖_[∞] =
        ‖(μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
          (μ_[ℝ] C ∗ᵈ μ_[ℝ] A)‖_[∞] := by
      rw [ddconv_assoc, ddconv_left_comm]
    _ ≤ ‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] :=
      dLinftyNorm_ddconv_le_of_nonnegative_probability
        _ _ hXnonneg hCAnonneg hXsum

theorem density_increment_of_large_boosted_inner_relative
    (A A₁ A₂ C X : Finset (ZMod N)) (scale k : ℕ)
    {alpha gain : ℝ}
    (halpha : 0 < alpha) (hdensity : alpha * scale = A.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hC : C.Nonempty) (hX : X.Nonempty)
    (hlarge :
      gain ≤ scale •
        ⟪μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
            (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
          μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ]) :
    gain * alpha ≤
      ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] := by
  rw [← le_div_iff₀ halpha]
  calc
    gain ≤ scale •
        ⟪μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
            (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂),
          μ_[ℝ] A ○ᵈ μ_[ℝ] A⟫_[ℝ] := hlarge
    _ = scale •
        ⟪(μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k)) ∗ᵈ μ_[ℝ] A,
          μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁⟫_[ℝ] := by
      congr 1
      have hassoc := (ddconv_dddconv_assoc
        (μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k))
        (μ_[ℝ] A₁) (μ_[ℝ] A₂)).symm
      rw [hassoc]
      exact inner_kernel_correlation_self_eq
        (μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k))
        (μ_[ℝ] A) (μ_[ℝ] A₁) (μ_[ℝ] A₂)
    _ ≤ scale •
        (‖(μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k)) ∗ᵈ μ_[ℝ] A‖_[∞] *
          ‖μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁‖_[1]) := by
      gcongr
      exact wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = scale •
        ‖(μ_[ℝ] C ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k)) ∗ᵈ μ_[ℝ] A‖_[∞] := by
      rw [dL1Norm_mu_ddconv_mu_dddconv_mu_eq_one A A₂ A₁ hA hA₂ hA₁,
        mul_one]
    _ ≤ scale • ‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] := by
      gcongr
      exact dLinftyNorm_smoothed_boosted_mu_le C X A k hX
    _ = ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] / alpha :=
      scale_smul_dLinfty_mu_ddconv_eq_indicator_div
        A C scale halpha hdensity hA hC

lemma large_smoothed_inner_of_mass_high_and_error
    {G : Type*} [Fintype G] [DecidableEq G]
    (f g f' : G → ℝ) (U : Finset G) (scale : ℕ)
    {a b error gain : ℝ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hb : 0 ≤ 1 + b)
    (hmass : 1 - a ≤ ∑ x ∈ U, f x)
    (hhigh : ∀ x ∈ U, 1 + b ≤ scale • g x)
    (herror : |⟪f', g⟫_[ℝ] - ⟪f, g⟫_[ℝ]| ≤ error)
    (hnumerical : gain + scale * error ≤ (1 + b) * (1 - a)) :
    gain ≤ scale • ⟪f', g⟫_[ℝ] := by
  have hbase :
      (1 + b) * (1 - a) ≤ scale • ⟪f, g⟫_[ℝ] :=
    lower_inner_of_mass_on_high_set f g U scale hf hg hb hmass hhigh le_rfl
  have hdiff : ⟪f, g⟫_[ℝ] - error ≤ ⟪f', g⟫_[ℝ] := by
    have hneg := neg_le_abs (⟪f', g⟫_[ℝ] - ⟪f, g⟫_[ℝ])
    linarith
  calc
    gain ≤ (1 + b) * (1 - a) - scale * error := by linarith
    _ ≤ scale • ⟪f, g⟫_[ℝ] - scale * error := by gcongr
    _ ≤ scale • ⟪f', g⟫_[ℝ] := by
      simpa only [nsmul_eq_mul, mul_sub] using
        (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg scale))

/-- The density-increment tail with an arbitrary preconstructed spectral
controller.  All Fourier analysis is independent of how the controller was
obtained; the local Chang--Sanders construction will supply `B` with a
rank-free entropy bound. -/
theorem exists_regular_boosted_density_increment_of_tested_mass_of_controller
    (R B : CyclicBohr.Set N)
    (A A₁ A₂ U X : Finset (ZMod N)) (scale k m : ℕ)
    {beta epsilon eta control : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hBradius : 0 < B.radius)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hU : U.Nonempty) (hX : X.Nonempty)
    (heta : 0 ≤ eta) (hcontrol0 : 0 ≤ control)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum X eta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ control)
    (hmass :
      1 - epsilon / 16 ≤ ∑ x ∈ U,
        (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hsmall :
      scale *
          ((control + 2 * eta ^ k) * (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
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
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate t).carrier‖_[∞] := by
  let F : ZMod N → ℂ :=
    (μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
      (μ_[ℂ] A ○ᵈ μ_[ℂ] A)
  obtain ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank,
      htlow, hthigh, hdeltaFormula, hdelta, hdeltat, hregular,
      hDsub, hsmooth⟩ :=
    CyclicImprovedBootstrapping.exists_regular_refined_bohr_smoothing_of_boostedFunction_of_controller
      R B hX F k m hRradius hRrank hm hBradius heta hcontrol0 hcontrol
      (by
        simpa only [F] using
          CyclicImprovedBootstrapping.sum_norm_fourier_improvedTestFunction_le
            hA hA₁ hA₂)
  refine ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank, htlow,
    hthigh, hdeltaFormula, hdelta, hdeltat, hregular, hDsub, ?_⟩
  apply density_increment_of_large_boosted_inner_relative
    A A₁ A₂ (D.dilate t).carrier X scale k hbeta hdensity
    hA hA₁ hA₂ (D.dilate t).carrier_nonempty hX
  apply large_smoothed_inner_of_mass_high_and_error
    (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂))
    (μ_[ℝ] A ○ᵈ μ_[ℝ] A)
    (μ_[ℝ] (D.dilate t).carrier ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
      (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) U scale
      (a := epsilon / 16) (b := epsilon / 8)
      (error := (control + 2 * eta ^ k) * (A.card : ℝ)⁻¹)
      (gain := 1 + epsilon / 64)
  · exact ddconv_nonneg (iterConv_nonneg mu_nonneg)
      (dddconv_nonneg mu_nonneg mu_nonneg)
  · exact dddconv_nonneg mu_nonneg mu_nonneg
  · linarith
  · exact hmass
  · exact hhigh
  · apply abs_inner_sub_inner_le_of_boosted_smoothing
      (D.dilate t).carrier X (D.dilate t).carrier_nonempty k A₁ A₂ A
    simpa only [F] using hsmooth
  · have hbase :
        1 + epsilon / 32 ≤
          (1 + epsilon / 8) * (1 - epsilon / 16) :=
      one_add_le_one_add_mul_one_sub <| by
        calc
          epsilon / 32 + epsilon / 16 + epsilon / 8 * (epsilon / 16) ≤
              epsilon / 32 + epsilon / 16 + epsilon / 8 * (1 / 16) := by
            gcongr
          _ ≤ epsilon / 8 := by linarith
    linarith

/-- Rank-preserving form of the controller density increment.  When the
controller already contains the ambient frequencies, regularization adds at
most the controller rank rather than adding the ambient rank a second time.
-/
theorem exists_regular_boosted_density_increment_of_tested_mass_of_controller_subset
    (R B : CyclicBohr.Set N)
    (A A₁ A₂ U X : Finset (ZMod N)) (scale k m : ℕ)
    {beta epsilon eta control : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hBradius : 0 < B.radius) (hfreq : R.frequencies ⊆ B.frequencies)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hU : U.Nonempty) (hX : X.Nonempty)
    (heta : 0 ≤ eta) (hcontrol0 : 0 ≤ control)
    (hcontrol : ∀ r ∈ CyclicChang.relativeLargeSpectrum X eta, ∀ x ∈ B,
      ‖1 - CyclicBohr.character r x‖ ≤ control)
    (hmass :
      1 - epsilon / 16 ≤ ∑ x ∈ U,
        (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hsmall :
      scale *
          ((control + 2 * eta ^ k) * (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
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
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate t).carrier‖_[∞] := by
  let F : ZMod N → ℂ :=
    (μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
      (μ_[ℂ] A ○ᵈ μ_[ℂ] A)
  obtain ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank,
      htlow, hthigh, hdeltaFormula, hdelta, hdeltat, hregular,
      hDsub, hsmooth⟩ :=
    CyclicImprovedBootstrapping.exists_regular_refined_bohr_smoothing_of_boostedFunction_of_controller_subset
      R B hX F k m hRradius hRrank hm hBradius hfreq heta hcontrol0 hcontrol
      (by
        simpa only [F] using
          CyclicImprovedBootstrapping.sum_norm_fourier_improvedTestFunction_le
            hA hA₁ hA₂)
  refine ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank, htlow,
    hthigh, hdeltaFormula, hdelta, hdeltat, hregular, hDsub, ?_⟩
  apply density_increment_of_large_boosted_inner_relative
    A A₁ A₂ (D.dilate t).carrier X scale k hbeta hdensity
    hA hA₁ hA₂ (D.dilate t).carrier_nonempty hX
  apply large_smoothed_inner_of_mass_high_and_error
    (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂))
    (μ_[ℝ] A ○ᵈ μ_[ℝ] A)
    (μ_[ℝ] (D.dilate t).carrier ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
      (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) U scale
      (a := epsilon / 16) (b := epsilon / 8)
      (error := (control + 2 * eta ^ k) * (A.card : ℝ)⁻¹)
      (gain := 1 + epsilon / 64)
  · exact ddconv_nonneg (iterConv_nonneg mu_nonneg)
      (dddconv_nonneg mu_nonneg mu_nonneg)
  · exact dddconv_nonneg mu_nonneg mu_nonneg
  · linarith
  · exact hmass
  · exact hhigh
  · apply abs_inner_sub_inner_le_of_boosted_smoothing
      (D.dilate t).carrier X (D.dilate t).carrier_nonempty k A₁ A₂ A
    simpa only [F] using hsmooth
  · have hbase :
        1 + epsilon / 32 ≤
          (1 + epsilon / 8) * (1 - epsilon / 16) :=
      one_add_le_one_add_mul_one_sub <| by
        calc
          epsilon / 32 + epsilon / 16 + epsilon / 8 * (epsilon / 16) ≤
              epsilon / 32 + epsilon / 16 + epsilon / 8 * (1 / 16) := by
            gcongr
          _ ≤ epsilon / 8 := by linarith
    linarith

theorem exists_regular_boosted_density_increment_of_tested_mass
    (R : CyclicBohr.Set N)
    (A A₁ A₂ U X : Finset (ZMod N)) (scale k m : ℕ)
    {beta epsilon eta rho : ℝ}
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank) (hm : 0 < m)
    (hbeta : 0 < beta) (hdensity : beta * scale = A.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hU : U.Nonempty) (hX : X.Nonempty)
    (heta : 0 < eta) (hrho : 0 < rho)
    (hmass :
      1 - epsilon / 16 ≤ ∑ x ∈ U,
        (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ
          (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hsmall :
      scale *
          (((CyclicChang.changRankBound X eta : ℝ) * rho +
            2 * eta ^ k) * (A.card : ℝ)⁻¹) ≤ epsilon / 64) :
    ∃ (D : CyclicBohr.Set N) (t delta : ℝ),
      D.radius = min R.radius rho ∧
      0 < D.radius ∧
      R.rank ≤ D.rank ∧
      D.rank ≤ R.rank + CyclicChang.changRankBound X eta ∧
      1 / 2 ≤ t ∧ t ≤ 1 ∧
      delta = (400 * (m : ℝ) * (D.rank : ℝ))⁻¹ ∧
      0 < delta ∧ delta < t ∧
      (10 * m) * (D.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (D.dilate (t - delta)).carrier.card ∧
      (D.dilate t).carrier ⊆ R.carrier ∧
      (1 + epsilon / 64) * beta ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ
          μ_[ℝ] (D.dilate t).carrier‖_[∞] := by
  let F : ZMod N → ℂ :=
    (μ_[ℂ] A₁ ○ᵈ μ_[ℂ] A₂) ∗ᵈ
      (μ_[ℂ] A ○ᵈ μ_[ℂ] A)
  obtain ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank,
      htlow, hthigh, hdeltaFormula, hdelta, hdeltat, hregular,
      hDsub, hsmooth⟩ :=
    CyclicImprovedBootstrapping.exists_regular_refined_bohr_smoothing_of_boostedFunction
      R hX F k m hRradius hRrank hm heta hrho
      (by
        simpa only [F] using
          CyclicImprovedBootstrapping.sum_norm_fourier_improvedTestFunction_le
            hA hA₁ hA₂)
  refine ⟨D, t, delta, hDradius, hDpos, hRrankD, hDrank, htlow,
    hthigh, hdeltaFormula, hdelta, hdeltat, hregular, hDsub, ?_⟩
  apply density_increment_of_large_boosted_inner_relative
    A A₁ A₂ (D.dilate t).carrier X scale k hbeta hdensity
    hA hA₁ hA₂ (D.dilate t).carrier_nonempty hX
  apply large_smoothed_inner_of_mass_high_and_error
    (μ_[ℝ] X ∗ᵈ^ k ∗ᵈ (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂))
    (μ_[ℝ] A ○ᵈ μ_[ℝ] A)
    (μ_[ℝ] (D.dilate t).carrier ∗ᵈ (μ_[ℝ] X ∗ᵈ^ k) ∗ᵈ
      (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂)) U scale
      (a := epsilon / 16) (b := epsilon / 8)
      (error := ((CyclicChang.changRankBound X eta : ℝ) * rho +
        2 * eta ^ k) * (A.card : ℝ)⁻¹)
      (gain := 1 + epsilon / 64)
  · exact ddconv_nonneg (iterConv_nonneg mu_nonneg)
      (dddconv_nonneg mu_nonneg mu_nonneg)
  · exact dddconv_nonneg mu_nonneg mu_nonneg
  · linarith
  · exact hmass
  · exact hhigh
  · apply abs_inner_sub_inner_le_of_boosted_smoothing
      (D.dilate t).carrier X (D.dilate t).carrier_nonempty k A₁ A₂ A
    simpa only [F] using hsmooth
  · have hbase :
        1 + epsilon / 32 ≤
          (1 + epsilon / 8) * (1 - epsilon / 16) :=
      one_add_le_one_add_mul_one_sub <| by
        calc
          epsilon / 32 + epsilon / 16 + epsilon / 8 * (epsilon / 16) ≤
              epsilon / 32 + epsilon / 16 + epsilon / 8 * (1 / 16) := by
            gcongr
          _ ≤ epsilon / 8 := by linarith
    have herr := hsmall
    change
      scale * (((CyclicChang.changRankBound X eta : ℝ) * rho +
        2 * eta ^ k) * (A.card : ℝ)⁻¹) ≤ epsilon / 64 at herr
    linarith

end CyclicImprovedDensityIncrement
end Erdos721
