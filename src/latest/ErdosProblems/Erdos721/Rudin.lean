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

import ErdosProblems.Erdos721.Fourier
import Mathlib.Combinatorics.Additive.Randomisation

/-!
# Rudin randomisation for Erdős Problem 721

This file packages Mathlib's character-randomisation identity in the finite
support form used by the proof of Rudin's inequality and Chang's spectral
lemma.  All products below range only over the stated dissociated set.
-/

namespace Erdos721

open Finset Fintype
open scoped BigOperators

namespace CyclicRudin

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Finite-support form of the exact randomisation identity. -/
theorem randomisation_finset
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (a : AddChar G ℂ → ℝ) (b : AddChar G ℂ → ℂ)
    (hb : ∀ ψ ∈ Δ, b ψ ≠ 0) :
    𝔼 x : G, ∏ ψ ∈ Δ, (a ψ + (b ψ * ψ x).re) = ∏ ψ ∈ Δ, a ψ := by
  let a' : AddChar G ℂ → ℝ := fun ψ ↦ if ψ ∈ Δ then a ψ else 1
  let b' : AddChar G ℂ → ℂ := fun ψ ↦ if ψ ∈ Δ then b ψ else 0
  have hsupp : {ψ | b' ψ ≠ 0} = (Δ : Set (AddChar G ℂ)) := by
    ext ψ
    by_cases hψ : ψ ∈ Δ
    · simp [b', hψ, hb ψ hψ]
    · simp [b', hψ]
  have hr := AddDissociated.randomisation a' b' (hsupp ▸ hΔ)
  have hterm (x : G) (ψ : AddChar G ℂ) :
      a' ψ + (b' ψ * ψ x).re =
        if ψ ∈ Δ then a ψ + (b ψ * ψ x).re else 1 := by
    by_cases hψ : ψ ∈ Δ <;> simp [a', b', hψ]
  simp_rw [hterm] at hr
  have haprod : ∏ ψ, a' ψ = ∏ ψ ∈ Δ, a ψ := by simp [a']
  rw [haprod] at hr
  have hprod (x : G) :
      (∏ ψ, if ψ ∈ Δ then a ψ + (b ψ * ψ x).re else 1) =
        ∏ ψ ∈ Δ, (a ψ + (b ψ * ψ x).re) :=
    Finset.prod_ite_mem_eq Δ _
  calc
    (𝔼 x : G, ∏ ψ ∈ Δ, (a ψ + (b ψ * ψ x).re)) =
        𝔼 x : G, ∏ ψ, if ψ ∈ Δ then a ψ + (b ψ * ψ x).re else 1 := by
      apply Finset.expect_congr rfl
      intro x _hx
      exact (hprod x).symm
    _ = ∏ ψ ∈ Δ, a ψ := hr

/-- A trigonometric polynomial supported on a finite set of characters. -/
def trigPoly (Δ : Finset (AddChar G ℂ)) (c : AddChar G ℂ → ℂ) (x : G) : ℂ :=
  ∑ ψ ∈ Δ, c ψ * ψ x

/-- Pointwise exponential majorant underlying Rudin's inequality. -/
lemma exp_re_trigPoly_le_prod
    (Δ : Finset (AddChar G ℂ)) (c : AddChar G ℂ → ℂ)
    (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1) {t : ℝ} (ht : 0 < t) (x : G) :
    Real.exp (((t : ℂ) * trigPoly Δ c x).re) ≤
      ∏ ψ ∈ Δ, (Real.cosh t + ((c ψ * (Real.sinh t : ℂ)) * ψ x).re) := by
  have hexp (z : ℂ) :
      Real.exp z.re ≤
        Real.cosh ‖z‖ + (z / ‖z‖).re * Real.sinh ‖z‖ := by
    calc
      Real.exp z.re = Real.exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0
        · simp
        · simp [hz]
      _ ≤ Real.cosh ‖z‖ + (z / ‖z‖).re * Real.sinh ‖z‖ :=
        Real.exp_mul_le_cosh_add_mul_sinh (by simpa using z.abs_re_div_norm_le_one) _
  have hone (ψ : AddChar G ℂ) (hψ : ψ ∈ Δ) :
      ‖(t : ℂ) * (c ψ * ψ x)‖ = t := by
    rw [norm_mul, norm_mul, hc ψ hψ, AddChar.norm_apply]
    simp [abs_of_pos ht]
  have hdiv (ψ : AddChar G ℂ) (hψ : ψ ∈ Δ) :
      ((t : ℂ) * (c ψ * ψ x)) / ‖(t : ℂ) * (c ψ * ψ x)‖ = c ψ * ψ x := by
    rw [hone ψ hψ]
    push_cast
    field_simp [ht.ne']
  calc
    Real.exp (((t : ℂ) * trigPoly Δ c x).re) =
        ∏ ψ ∈ Δ, Real.exp (((t : ℂ) * (c ψ * ψ x)).re) := by
      unfold trigPoly
      rw [Finset.mul_sum, Complex.re_sum, Real.exp_sum]
    _ ≤ ∏ ψ ∈ Δ,
        (Real.cosh ‖(t : ℂ) * (c ψ * ψ x)‖ +
          (((t : ℂ) * (c ψ * ψ x)) /
            ‖(t : ℂ) * (c ψ * ψ x)‖).re *
              Real.sinh ‖(t : ℂ) * (c ψ * ψ x)‖) := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun ψ _hψ ↦
        hexp ((t : ℂ) * (c ψ * ψ x))
    _ = ∏ ψ ∈ Δ,
        (Real.cosh t + ((c ψ * (Real.sinh t : ℂ)) * ψ x).re) := by
      apply Finset.prod_congr rfl
      intro ψ hψ
      rw [hdiv ψ hψ, hone ψ hψ]
      norm_num [Complex.mul_re, Complex.sinh_ofReal_re]
      ring

/-- Rudin's exponential moment estimate for a dissociated character set and
unit-modulus coefficients. -/
theorem rudin_exp_ineq
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    𝔼 x : G, Real.exp (((t : ℂ) * trigPoly Δ c x).re) ≤
      Real.exp (t ^ 2 * Δ.card / 2) := by
  have hb : ∀ ψ ∈ Δ, c ψ * (Real.sinh t : ℂ) ≠ 0 := by
    intro ψ hψ
    apply mul_ne_zero
    · exact norm_ne_zero_iff.mp (by rw [hc ψ hψ]; norm_num)
    · exact_mod_cast (Real.sinh_ne_zero.mpr ht.ne')
  calc
    (𝔼 x : G, Real.exp (((t : ℂ) * trigPoly Δ c x).re)) ≤
        𝔼 x : G, ∏ ψ ∈ Δ,
          (Real.cosh t + ((c ψ * (Real.sinh t : ℂ)) * ψ x).re) := by
      apply Finset.expect_le_expect
      intro x _hx
      exact exp_re_trigPoly_le_prod Δ c hc ht x
    _ = ∏ ψ ∈ Δ, Real.cosh t :=
      randomisation_finset Δ hΔ (fun _ ↦ Real.cosh t)
        (fun ψ ↦ c ψ * (Real.sinh t : ℂ)) hb
    _ ≤ ∏ _ψ ∈ Δ, Real.exp (t ^ 2 / 2) := by
      apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
      intro ψ _hψ
      exact Real.cosh_le_exp_half_sq t
    _ = Real.exp (t ^ 2 * Δ.card / 2) := by
      rw [Finset.prod_const]
      simp only [nsmul_eq_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

lemma trigPoly_neg (Δ : Finset (AddChar G ℂ)) (c : AddChar G ℂ → ℂ) (x : G) :
    trigPoly Δ (fun ψ ↦ -c ψ) x = -trigPoly Δ c x := by
  unfold trigPoly
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- Two-sided exponential moment estimate. -/
theorem rudin_exp_abs_ineq
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    𝔼 x : G, Real.exp |((t : ℂ) * trigPoly Δ c x).re| ≤
      2 * Real.exp (t ^ 2 * Δ.card / 2) := by
  have hcneg : ∀ ψ ∈ Δ, ‖-c ψ‖ = 1 := by
    intro ψ hψ
    simpa using hc ψ hψ
  calc
    (𝔼 x : G, Real.exp |((t : ℂ) * trigPoly Δ c x).re|) ≤
        𝔼 x : G,
          (Real.exp (((t : ℂ) * trigPoly Δ c x).re) +
            Real.exp (((t : ℂ) * trigPoly Δ (fun ψ ↦ -c ψ) x).re)) := by
      apply Finset.expect_le_expect
      intro x _hx
      rw [trigPoly_neg]
      norm_num
      simpa [abs_of_pos ht] using
        Real.exp_abs_le (t * (trigPoly Δ c x).re)
    _ = (𝔼 x : G, Real.exp (((t : ℂ) * trigPoly Δ c x).re)) +
          𝔼 x : G, Real.exp (((t : ℂ) * trigPoly Δ (fun ψ ↦ -c ψ) x).re) := by
      exact Finset.expect_add_distrib _ _ _
    _ ≤ Real.exp (t ^ 2 * Δ.card / 2) +
          Real.exp (t ^ 2 * Δ.card / 2) :=
      add_le_add (rudin_exp_ineq Δ hΔ c hc ht)
        (rudin_exp_ineq Δ hΔ (fun ψ ↦ -c ψ) hcneg ht)
    _ = 2 * Real.exp (t ^ 2 * Δ.card / 2) := by ring

/-- A direct finite-moment consequence of the two-sided exponential bound. -/
theorem rudin_scaled_moment_div_factorial
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    (p : ℕ) {t : ℝ} (ht : 0 < t) :
    (𝔼 x : G, |((t : ℂ) * trigPoly Δ c x).re| ^ p) / (p.factorial : ℝ) ≤
      2 * Real.exp (t ^ 2 * Δ.card / 2) := by
  calc
    (𝔼 x : G, |((t : ℂ) * trigPoly Δ c x).re| ^ p) / (p.factorial : ℝ) =
        𝔼 x : G,
          |((t : ℂ) * trigPoly Δ c x).re| ^ p / (p.factorial : ℝ) := by
      exact Finset.expect_div _ _ _
    _ ≤ 𝔼 x : G, Real.exp |((t : ℂ) * trigPoly Δ c x).re| := by
      apply Finset.expect_le_expect
      intro x _hx
      exact Real.pow_div_factorial_le_exp
        (x := |((t : ℂ) * trigPoly Δ c x).re|)
        (abs_nonneg (((t : ℂ) * trigPoly Δ c x).re)) p
    _ ≤ 2 * Real.exp (t ^ 2 * Δ.card / 2) :=
      rudin_exp_abs_ineq Δ hΔ c hc ht

/-- Multiplication by a nonnegative real scalar factors out of the real
`p`-moment of a trigonometric polynomial. -/
lemma expect_abs_re_scaled_pow
    (Δ : Finset (AddChar G ℂ)) (c : AddChar G ℂ → ℂ)
    (p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (𝔼 x : G, |((t : ℂ) * trigPoly Δ c x).re| ^ p) =
      t ^ p * (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) := by
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _hx
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [abs_mul, abs_of_nonneg ht, mul_pow]

/-- An exact unscaled finite-moment estimate, retaining the free positive
scale.  Optimizing this scale at `sqrt (p / #Δ)` gives the usual
`O(sqrt p * sqrt #Δ)` form of Rudin's inequality. -/
theorem rudin_moment_bound
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    (p : ℕ) {t : ℝ} (ht : 0 < t) :
    (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) ≤
      (p.factorial : ℝ) * (2 * Real.exp (t ^ 2 * Δ.card / 2)) / t ^ p := by
  have hscaled := rudin_scaled_moment_div_factorial Δ hΔ c hc p ht
  rw [expect_abs_re_scaled_pow Δ c p ht.le] at hscaled
  have hfac : (0 : ℝ) < p.factorial := by positivity
  have htp : (0 : ℝ) < t ^ p := pow_pos ht p
  rw [div_le_iff₀ hfac] at hscaled
  rw [le_div_iff₀ htp]
  calc
    (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) * t ^ p =
        t ^ p * (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) := by ring
    _ ≤ 2 * Real.exp (t ^ 2 * Δ.card / 2) * (p.factorial : ℝ) := hscaled
    _ = (p.factorial : ℝ) * (2 * Real.exp (t ^ 2 * Δ.card / 2)) := by ring

/-- Rudin's moment estimate at its optimizing scale.  This exact form avoids
introducing an `L^p`-seminorm and is convenient for the power-form Hölder
argument in Chang's lemma. -/
theorem rudin_moment_bound_at_sqrt
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    (p : ℕ) (hp : 0 < p) (hcard : 0 < Δ.card) :
    (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) ≤
      (p.factorial : ℝ) * (2 * Real.exp ((p : ℝ) / 2)) /
        (Real.sqrt ((p : ℝ) / Δ.card)) ^ p := by
  have hratio : (0 : ℝ) < (p : ℝ) / Δ.card := by positivity
  have hsqrt : 0 < Real.sqrt ((p : ℝ) / Δ.card) := Real.sqrt_pos.2 hratio
  have hbound := rudin_moment_bound Δ hΔ c hc p hsqrt
  convert hbound using 1
  congr 4
  rw [Real.sq_sqrt hratio.le]
  field_simp

/-- The scalar cancellation used when the optimizing Rudin scale is
substituted into its moment estimate. -/
lemma natCast_div_sqrt_div_eq_sqrt_mul {p d : ℕ} (hp : 0 < p) (hd : 0 < d) :
    (p : ℝ) / Real.sqrt ((p : ℝ) / d) = Real.sqrt ((p : ℝ) * d) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
  have hsd : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdR).ne'
  calc
    (p : ℝ) / Real.sqrt ((p : ℝ) / d) =
        (p : ℝ) / (Real.sqrt (p : ℝ) / Real.sqrt (d : ℝ)) := by
      rw [Real.sqrt_div hpR.le]
    _ = Real.sqrt (p : ℝ) * Real.sqrt (d : ℝ) := by
      field_simp
      rw [Real.sq_sqrt hpR.le]
    _ = Real.sqrt ((p : ℝ) * d) := (Real.sqrt_mul hpR.le _).symm

/-- A convenient power-form of Rudin's inequality.  The constant is kept
deliberately explicit; the important feature is the sharp
`sqrt (p * #Δ)` dependence. -/
theorem rudin_moment_bound_clean
    (Δ : Finset (AddChar G ℂ)) (hΔ : AddDissociated (Δ : Set (AddChar G ℂ)))
    (c : AddChar G ℂ → ℂ) (hc : ∀ ψ ∈ Δ, ‖c ψ‖ = 1)
    (p : ℕ) (hp : 0 < p) (hcard : 0 < Δ.card) :
    (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) ≤
      (2 * Real.exp (1 / 2 : ℝ) *
        Real.sqrt ((p : ℝ) * Δ.card)) ^ p := by
  have hopt := rudin_moment_bound_at_sqrt Δ hΔ c hc p hp hcard
  have hfac : (p.factorial : ℝ) ≤ (p : ℝ) ^ p := by
    exact_mod_cast p.factorial_le_pow
  have htwo : (2 : ℝ) ≤ 2 ^ p := le_self_pow₀ (by norm_num) hp.ne'
  have hden : 0 < Real.sqrt ((p : ℝ) / Δ.card) ^ p := by positivity
  calc
    (𝔼 x : G, |(trigPoly Δ c x).re| ^ p) ≤
        (p.factorial : ℝ) * (2 * Real.exp ((p : ℝ) / 2)) /
          (Real.sqrt ((p : ℝ) / Δ.card)) ^ p := hopt
    _ ≤ ((p : ℝ) ^ p) *
          ((2 : ℝ) ^ p * Real.exp ((p : ℝ) / 2)) /
            (Real.sqrt ((p : ℝ) / Δ.card)) ^ p := by
      gcongr
    _ = ((p : ℝ) * 2 * Real.exp (1 / 2 : ℝ) /
          Real.sqrt ((p : ℝ) / Δ.card)) ^ p := by
      have hexp : Real.exp ((p : ℝ) / 2) = Real.exp (1 / 2 : ℝ) ^ p := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hexp, div_pow, mul_pow, mul_pow]
      ring
    _ = (2 * Real.exp (1 / 2 : ℝ) *
          Real.sqrt ((p : ℝ) * Δ.card)) ^ p := by
      congr 1
      calc
        (p : ℝ) * 2 * Real.exp (1 / 2 : ℝ) /
            Real.sqrt ((p : ℝ) / Δ.card) =
            2 * Real.exp (1 / 2 : ℝ) *
              ((p : ℝ) / Real.sqrt ((p : ℝ) / Δ.card)) := by ring
        _ = 2 * Real.exp (1 / 2 : ℝ) *
              Real.sqrt ((p : ℝ) * Δ.card) := by
          rw [natCast_div_sqrt_div_eq_sqrt_mul hp hcard]

section Cyclic

variable {N : ℕ} [NeZero N]

/-- A set of cyclic frequency indices, transported to the actual character
group on which Mathlib's randomisation theorem is stated. -/
noncomputable def cyclicCharacterEmbedding :
    ZMod N ↪ AddChar (ZMod N) ℂ where
  toFun := CyclicBohr.character
  inj' := AddChar.zmodAddEquiv.injective

@[simp] lemma cyclicCharacterEmbedding_apply (r : ZMod N) :
    cyclicCharacterEmbedding r = CyclicBohr.character r := rfl

noncomputable def cyclicCharacterImage (Δ : Finset (ZMod N)) :
    Finset (AddChar (ZMod N) ℂ) :=
  Δ.map cyclicCharacterEmbedding

@[simp] lemma card_cyclicCharacterImage (Δ : Finset (ZMod N)) :
    (cyclicCharacterImage Δ).card = Δ.card := by
  simp [cyclicCharacterImage]

lemma addDissociated_cyclicCharacterImage {Δ : Finset (ZMod N)}
    (hΔ : AddDissociated (Δ : Set (ZMod N))) :
    AddDissociated (cyclicCharacterImage Δ : Set (AddChar (ZMod N) ℂ)) := by
  rw [← AddChar.zmodAddEquiv.addDissociated_preimage]
  rw [cyclicCharacterImage, Finset.coe_map]
  change AddDissociated
    (⇑AddChar.zmodAddEquiv ⁻¹' ⇑AddChar.zmodAddEquiv '' (Δ : Set (ZMod N)))
  rw [Set.preimage_image_eq _ AddChar.zmodAddEquiv.injective]
  exact hΔ

/-- Rudin's power-moment inequality in the cyclic-index notation used by the
Fourier and Bohr modules. -/
theorem cyclic_rudin_moment_bound_clean
    (Δ : Finset (ZMod N)) (hΔ : AddDissociated (Δ : Set (ZMod N)))
    (c : ZMod N → ℂ) (hc : ∀ r ∈ Δ, ‖c r‖ = 1)
    (p : ℕ) (hp : 0 < p) (hcard : 0 < Δ.card) :
    (𝔼 x : ZMod N,
      |(∑ r ∈ Δ, c r * CyclicBohr.character r x).re| ^ p) ≤
      (2 * Real.exp (1 / 2 : ℝ) *
        Real.sqrt ((p : ℝ) * Δ.card)) ^ p := by
  let c' : AddChar (ZMod N) ℂ → ℂ := fun ψ ↦ c (AddChar.zmodAddEquiv.symm ψ)
  have hc' : ∀ ψ ∈ cyclicCharacterImage Δ, ‖c' ψ‖ = 1 := by
    intro ψ hψ
    rw [cyclicCharacterImage] at hψ
    rw [Finset.mem_map] at hψ
    obtain ⟨r, hr, rfl⟩ := hψ
    simpa only [c', cyclicCharacterEmbedding_apply, CyclicBohr.character,
      AddEquiv.symm_apply_apply] using hc r hr
  have hpoly (x : ZMod N) :
      trigPoly (cyclicCharacterImage Δ) c' x =
        ∑ r ∈ Δ, c r * CyclicBohr.character r x := by
    unfold trigPoly cyclicCharacterImage
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [c', cyclicCharacterEmbedding_apply, CyclicBohr.character,
      AddEquiv.symm_apply_apply]
  have hrudin := rudin_moment_bound_clean
    (cyclicCharacterImage Δ) (addDissociated_cyclicCharacterImage hΔ)
      c' hc' p hp (by simpa using hcard)
  simpa only [hpoly, card_cyclicCharacterImage] using hrudin

end Cyclic

end CyclicRudin
end Erdos721
