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

import ErdosProblems.Erdos721.Bohr

/-!
# Normalized harmonic analysis on a finite cyclic group

This file supplies the exact normalizations used in the quantitative Roth
argument for Erdős Problem 721.  The average is normalized by `1 / N`, as are
convolution and the Fourier transform.  The elementary results below include
translation invariance, character orthogonality, Fourier inversion, and the
change of variables between the two standard three-term-progression counts.
-/

namespace Erdos721

open AddChar Finset
open scoped BigOperators

namespace CyclicFourier

variable {N : ℕ} [NeZero N]

/-- The normalized average of a complex-valued function on `ZMod N`. -/
noncomputable def average (f : ZMod N → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, f x

@[simp] lemma average_zero : average (fun _ : ZMod N ↦ (0 : ℂ)) = 0 := by
  simp [average]

@[simp] lemma average_one : average (fun _ : ZMod N ↦ (1 : ℂ)) = 1 := by
  simp [average, ZMod.card, NeZero.ne N]

lemma average_add (f g : ZMod N → ℂ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  unfold average
  rw [Finset.sum_add_distrib]
  ring

lemma average_const_mul (c : ℂ) (f : ZMod N → ℂ) :
    average (fun x ↦ c * f x) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

lemma average_mul_const (f : ZMod N → ℂ) (c : ℂ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp only [average, ← Finset.sum_mul]
  ring

@[simp] lemma average_const (c : ℂ) : average (fun _ : ZMod N ↦ c) = c := by
  simpa using average_const_mul c (fun _ : ZMod N ↦ (1 : ℂ))

/-- A finite sum may be interchanged with normalized averaging. -/
lemma average_sum {ι : Type*} [Fintype ι] (F : ι → ZMod N → ℂ) :
    average (fun x ↦ ∑ i : ι, F i x) = ∑ i : ι, average (F i) := by
  unfold average
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Fubini's identity for two normalized finite averages. -/
lemma average_comm (F : ZMod N → ZMod N → ℂ) :
    average (fun x ↦ average fun y ↦ F x y) =
      average (fun y ↦ average fun x ↦ F x y) := by
  unfold average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Complex conjugation commutes with normalized averaging. -/
lemma star_average (f : ZMod N → ℂ) :
    (starRingEnd ℂ) (average f) = average fun x ↦ (starRingEnd ℂ) (f x) := by
  simp [average, map_mul, map_sum]

/-- Normalized averaging is invariant under translation. -/
lemma average_add_left (f : ZMod N → ℂ) (a : ZMod N) :
    average (fun x ↦ f (a + x)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ fun _ ↦ rfl

/-- Normalized averaging is invariant under reflection. -/
lemma average_neg (f : ZMod N → ℂ) :
    average (fun x ↦ f (-x)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun _ ↦ rfl

/-- The normalized cyclic convolution. -/
noncomputable def convolution (f g : ZMod N → ℂ) (x : ZMod N) : ℂ :=
  average fun y ↦ f y * g (x - y)

/-- Cyclic convolution is commutative. -/
lemma convolution_comm (f g : ZMod N → ℂ) : convolution f g = convolution g f := by
  funext x
  unfold convolution average
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ by
    simp only [Equiv.subLeft_apply]
    rw [sub_sub_cancel]
    exact mul_comm _ _

/-- The average of a convolution is the product of the averages. -/
lemma average_convolution (f g : ZMod N → ℂ) :
    average (convolution f g) = average f * average g := by
  have htranslate (y : ZMod N) : ∑ x : ZMod N, g (x - y) = ∑ x : ZMod N, g x := by
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun _ ↦ rfl
  have hdouble :
      ∑ x : ZMod N, ∑ y : ZMod N, f y * g (x - y) =
        (∑ y : ZMod N, f y) * ∑ x : ZMod N, g x := by
    rw [Finset.sum_comm]
    calc
      ∑ y : ZMod N, ∑ x : ZMod N, f y * g (x - y) =
          ∑ y : ZMod N, f y * ∑ x : ZMod N, g (x - y) := by
            congr 1 with y
            rw [Finset.mul_sum]
      _ = ∑ y : ZMod N, f y * ∑ x : ZMod N, g x := by
            congr 1 with y
            rw [htranslate]
      _ = (∑ y : ZMod N, f y) * ∑ x : ZMod N, g x := by
            rw [Finset.sum_mul]
  simp only [average, convolution]
  rw [← Finset.mul_sum, hdouble]
  ring

/-- The standard character sum over the dual cyclic group. -/
lemma sum_character (x : ZMod N) :
    ∑ r : ZMod N, CyclicBohr.character r x =
      if x = 0 then (N : ℂ) else 0 := by
  have hzero : CyclicBohr.character x = 0 ↔ x = 0 := by
    simpa only [CyclicBohr.character] using
      (AddChar.zmodAddEquiv.map_eq_zero_iff (x := x))
  simpa only [CyclicBohr.character_comm, ZMod.card, hzero] using
    AddChar.sum_eq_ite (CyclicBohr.character x)

/-- Orthogonality of normalized cyclic characters. -/
lemma average_character (x : ZMod N) :
    average (fun r ↦ CyclicBohr.character r x) = if x = 0 then 1 else 0 := by
  rw [average, sum_character]
  split_ifs with hx
  · simp [NeZero.ne N]
  · simp

/-- The normalized Fourier transform, with the negative sign supplied by
complex conjugation of the character. -/
noncomputable def fourier (f : ZMod N → ℂ) (r : ZMod N) : ℂ :=
  average fun x ↦ (starRingEnd ℂ) (CyclicBohr.character r x) * f x

@[simp] lemma fourier_zero (f : ZMod N → ℂ) : fourier f 0 = average f := by
  simp [fourier, CyclicBohr.character_zero_index]

/-- Fourier inversion for the normalized transform. -/
theorem fourier_inversion (f : ZMod N → ℂ) (x : ZMod N) :
    ∑ r : ZMod N, fourier f r * CyclicBohr.character r x = f x := by
  simp only [fourier, average, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]
  have hchar (r y : ZMod N) :
      (starRingEnd ℂ) (CyclicBohr.character r y) * CyclicBohr.character r x =
        CyclicBohr.character r (x - y) := by
    have hswap :
        CyclicBohr.character (-r) y = CyclicBohr.character r (-y) := by
      rw [CyclicBohr.Set.character_neg_index, AddChar.map_neg_eq_conj]
    rw [← CyclicBohr.Set.character_neg_index, hswap, mul_comm,
      ← CyclicBohr.character_add]
    congr 1
    abel
  calc
    ∑ y : ZMod N, ∑ r : ZMod N,
        (N : ℂ)⁻¹ * ((starRingEnd ℂ) (CyclicBohr.character r y) *
          (f y * CyclicBohr.character r x)) =
        ∑ y : ZMod N, ((N : ℂ)⁻¹ * f y) *
          ∑ r : ZMod N, CyclicBohr.character r (x - y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      calc
        (N : ℂ)⁻¹ * ((starRingEnd ℂ) (CyclicBohr.character r y) *
            (f y * CyclicBohr.character r x)) =
            (N : ℂ)⁻¹ * f y *
              ((starRingEnd ℂ) (CyclicBohr.character r y) *
                CyclicBohr.character r x) := by ring
        _ = (N : ℂ)⁻¹ * f y * CyclicBohr.character r (x - y) := by
          rw [hchar]
    _ = ∑ y : ZMod N, ((N : ℂ)⁻¹ * f y) *
          (if x - y = 0 then (N : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [sum_character]
    _ = f x := by
      simp only [sub_eq_zero]
      simp
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]

/-- The normalized Fourier transform takes normalized convolution to
pointwise multiplication. -/
theorem fourier_convolution (f g : ZMod N → ℂ) (r : ZMod N) :
    fourier (convolution f g) r = fourier f r * fourier g r := by
  have hinner (y : ZMod N) :
      ∑ x : ZMod N,
          (starRingEnd ℂ) (CyclicBohr.character r x) * g (x - y) =
        (starRingEnd ℂ) (CyclicBohr.character r y) *
          ∑ z : ZMod N, (starRingEnd ℂ) (CyclicBohr.character r z) * g z := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by
      simp only [Equiv.subRight_apply]
      have hxy : y + (x - y) = x := by abel
      have hc : CyclicBohr.character r x =
          CyclicBohr.character r y * CyclicBohr.character r (x - y) := by
        rw [← CyclicBohr.character_add, hxy]
      rw [hc, map_mul]
      ring
  have hdouble :
      ∑ x : ZMod N, ∑ y : ZMod N,
          (starRingEnd ℂ) (CyclicBohr.character r x) * (f y * g (x - y)) =
        (∑ y : ZMod N,
            (starRingEnd ℂ) (CyclicBohr.character r y) * f y) *
          ∑ z : ZMod N, (starRingEnd ℂ) (CyclicBohr.character r z) * g z := by
    rw [Finset.sum_comm]
    calc
      ∑ y : ZMod N, ∑ x : ZMod N,
          (starRingEnd ℂ) (CyclicBohr.character r x) * (f y * g (x - y)) =
          ∑ y : ZMod N, f y *
            ∑ x : ZMod N,
              (starRingEnd ℂ) (CyclicBohr.character r x) * g (x - y) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = ∑ y : ZMod N,
          ((starRingEnd ℂ) (CyclicBohr.character r y) * f y) *
            ∑ z : ZMod N, (starRingEnd ℂ) (CyclicBohr.character r z) * g z := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [hinner]
        ring
      _ = (∑ y : ZMod N,
          (starRingEnd ℂ) (CyclicBohr.character r y) * f y) *
            ∑ z : ZMod N, (starRingEnd ℂ) (CyclicBohr.character r z) * g z := by
        rw [Finset.sum_mul]
  have hscale :
      ∑ x : ZMod N, (starRingEnd ℂ) (CyclicBohr.character r x) *
          ((N : ℂ)⁻¹ * ∑ y : ZMod N, f y * g (x - y)) =
        (N : ℂ)⁻¹ * ∑ x : ZMod N, ∑ y : ZMod N,
          (starRingEnd ℂ) (CyclicBohr.character r x) * (f y * g (x - y)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  simp only [fourier, convolution, average]
  rw [hscale, hdouble]
  ring

/-- Conjugating a Fourier coefficient reverses the conjugations in its
defining average. -/
lemma star_fourier (f : ZMod N → ℂ) (r : ZMod N) :
    (starRingEnd ℂ) (fourier f r) =
      average fun x ↦ CyclicBohr.character r x * (starRingEnd ℂ) (f x) := by
  rw [fourier, star_average]
  apply congrArg average
  funext x
  rw [map_mul]
  simp

/-- A negative-frequency Fourier coefficient can be written with the
unconjugated positive-frequency character. -/
lemma fourier_neg (f : ZMod N → ℂ) (r : ZMod N) :
    fourier f (-r) = average fun x ↦ CyclicBohr.character r x * f x := by
  unfold fourier
  apply congrArg average
  funext x
  rw [CyclicBohr.Set.character_neg_index]
  simp

/-- Parseval's identity in sesquilinear form for the normalized transform. -/
theorem parseval (f g : ZMod N → ℂ) :
    average (fun x ↦ (starRingEnd ℂ) (f x) * g x) =
      ∑ r : ZMod N, (starRingEnd ℂ) (fourier f r) * fourier g r := by
  have hpoint (x : ZMod N) :
      (starRingEnd ℂ) (f x) * g x =
        ∑ r : ZMod N, fourier g r *
          (CyclicBohr.character r x * (starRingEnd ℂ) (f x)) := by
    rw [← fourier_inversion g x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  calc
    average (fun x ↦ (starRingEnd ℂ) (f x) * g x) =
        average (fun x ↦ ∑ r : ZMod N, fourier g r *
          (CyclicBohr.character r x * (starRingEnd ℂ) (f x))) := by
      apply congrArg average
      funext x
      exact hpoint x
    _ = ∑ r : ZMod N,
          average (fun x ↦ fourier g r *
            (CyclicBohr.character r x * (starRingEnd ℂ) (f x))) :=
      average_sum _
    _ = ∑ r : ZMod N, fourier g r *
          average (fun x ↦ CyclicBohr.character r x * (starRingEnd ℂ) (f x)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact average_const_mul _ _
    _ = ∑ r : ZMod N, fourier g r * (starRingEnd ℂ) (fourier f r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [star_fourier]
    _ = ∑ r : ZMod N, (starRingEnd ℂ) (fourier f r) * fourier g r := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact mul_comm _ _

/-- Parseval in squared-norm form, still expressed in `ℂ` so that it follows
without any coercion loss from the sesquilinear identity. -/
theorem parseval_norm_sq (f : ZMod N → ℂ) :
    average (fun x ↦ ((‖f x‖ ^ 2 : ℝ) : ℂ)) =
      ∑ r : ZMod N, ((‖fourier f r‖ ^ 2 : ℝ) : ℂ) := by
  have hpoint (z : ℂ) :
      (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]
    norm_cast
  calc
    average (fun x ↦ ((‖f x‖ ^ 2 : ℝ) : ℂ)) =
        average (fun x ↦ (starRingEnd ℂ) (f x) * f x) := by
      apply congrArg average
      funext x
      exact (hpoint (f x)).symm
    _ = ∑ r : ZMod N, (starRingEnd ℂ) (fourier f r) * fourier f r := parseval f f
    _ = ∑ r : ZMod N, ((‖fourier f r‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact hpoint (fourier f r)

/-- Real-valued squared-norm form of Parseval. -/
theorem parseval_norm_sq_real (f : ZMod N → ℂ) :
    (N : ℝ)⁻¹ * ∑ x : ZMod N, ‖f x‖ ^ 2 =
      ∑ r : ZMod N, ‖fourier f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [average, Complex.ofReal_pow] using parseval_norm_sq f

/-- The complex indicator of a finite subset of the cyclic group. -/
def indicator (A : Finset (ZMod N)) (x : ZMod N) : ℂ :=
  if x ∈ A then 1 else 0

@[simp] lemma indicator_apply_mem {A : Finset (ZMod N)} {x : ZMod N} (hx : x ∈ A) :
    indicator A x = 1 := by simp [indicator, hx]

@[simp] lemma indicator_apply_notMem {A : Finset (ZMod N)} {x : ZMod N} (hx : x ∉ A) :
    indicator A x = 0 := by simp [indicator, hx]

/-- The average of an indicator is its density. -/
lemma average_indicator (A : Finset (ZMod N)) :
    average (indicator A) = (A.card : ℂ) / N := by
  unfold average indicator
  rw [Finset.sum_boole]
  simp [div_eq_mul_inv, mul_comm]

lemma sum_norm_sq_indicator (A : Finset (ZMod N)) :
    ∑ x : ZMod N, ‖indicator A x‖ ^ 2 = A.card := by
  calc
    ∑ x : ZMod N, ‖indicator A x‖ ^ 2 =
        ∑ x : ZMod N, if x ∈ A then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxA : x ∈ A <;> simp [indicator, hxA]
    _ = A.card := by rw [Finset.sum_boole]; simp

/-- Frequencies where a normalized Fourier coefficient has modulus at least
`η`. -/
noncomputable def largeSpectrum (f : ZMod N → ℂ) (η : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun r ↦ η ≤ ‖fourier f r‖

@[simp] lemma mem_largeSpectrum {f : ZMod N → ℂ} {η : ℝ} {r : ZMod N} :
    r ∈ largeSpectrum f η ↔ η ≤ ‖fourier f r‖ := by
  simp [largeSpectrum]

/-- The elementary Bessel bound for any subset of the large spectrum.  Chang's
lemma improves this cardinal estimate under dissociation. -/
theorem card_mul_sq_le_sum_norm_sq_of_subset_largeSpectrum
    (f : ZMod N → ℂ) {η : ℝ} (hη : 0 ≤ η) (S : Finset (ZMod N))
    (hS : S ⊆ largeSpectrum f η) :
    (S.card : ℝ) * η ^ 2 ≤ ∑ r : ZMod N, ‖fourier f r‖ ^ 2 := by
  calc
    (S.card : ℝ) * η ^ 2 = ∑ _r ∈ S, η ^ 2 := by simp
    _ ≤ ∑ r ∈ S, ‖fourier f r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact pow_le_pow_left₀ hη (mem_largeSpectrum.mp (hS hr)) 2
    _ ≤ ∑ r : ZMod N, ‖fourier f r‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro r _hr _hnot
      positivity

/-- Bessel's large-spectrum bound specialized to an indicator. -/
theorem card_mul_sq_le_density_of_subset_largeSpectrum_indicator
    (A : Finset (ZMod N)) {η : ℝ} (hη : 0 ≤ η) (S : Finset (ZMod N))
    (hS : S ⊆ largeSpectrum (indicator A) η) :
    (S.card : ℝ) * η ^ 2 ≤ (A.card : ℝ) / N := by
  calc
    (S.card : ℝ) * η ^ 2 ≤
        ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 :=
      card_mul_sq_le_sum_norm_sq_of_subset_largeSpectrum _ hη S hS
    _ = (N : ℝ)⁻¹ * ∑ x : ZMod N, ‖indicator A x‖ ^ 2 :=
      (parseval_norm_sq_real (indicator A)).symm
    _ = (A.card : ℝ) / N := by
      rw [sum_norm_sq_indicator]
      ring

/-- The elementary `L²` spectrum bound, combined with maximal dissociated-set
extraction, produces a Bohr set controlling every large Fourier frequency.
Chang's lemma improves the displayed rank from a reciprocal-density bound to
a logarithmic one. -/
theorem exists_bohr_controlling_largeSpectrum_indicator
    (A : Finset (ZMod N)) {η ρ : ℝ} (hη : 0 < η) (hρ : 0 ≤ ρ) :
    ∃ B : CyclicBohr.Set N,
      B.frequencies ⊆ largeSpectrum (indicator A) η ∧
      B.rank ≤ ⌈((A.card : ℝ) / N) / η ^ 2⌉₊ ∧
      ∀ r ∈ largeSpectrum (indicator A) η, ∀ x ∈ B,
        ‖1 - CyclicBohr.character r x‖ ≤
          (⌈((A.card : ℝ) / N) / η ^ 2⌉₊ : ℝ) * ρ := by
  apply CyclicBohr.Set.exists_small_bohr_controlling_of_dissociated_card_le
      (largeSpectrum (indicator A) η)
      ⌈((A.card : ℝ) / N) / η ^ 2⌉₊ ρ hρ
  intro Δ hΔ _hdis
  have hBessel :=
    card_mul_sq_le_density_of_subset_largeSpectrum_indicator A hη.le Δ hΔ
  have hcardReal :
      (Δ.card : ℝ) ≤ ((A.card : ℝ) / N) / η ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hη)]
    exact hBessel
  have hceil :
      (Δ.card : ℝ) ≤ (⌈((A.card : ℝ) / N) / η ^ 2⌉₊ : ℝ) :=
    hcardReal.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The balanced function of a set. -/
noncomputable def balanced (A : Finset (ZMod N)) (x : ZMod N) : ℂ :=
  indicator A x - (A.card : ℂ) / N

@[simp] lemma average_balanced (A : Finset (ZMod N)) : average (balanced A) = 0 := by
  unfold balanced
  calc
    average (fun x ↦ indicator A x - (A.card : ℂ) / N) =
        average (indicator A) + average (fun _ ↦ -((A.card : ℂ) / N)) := by
      simpa only [sub_eq_add_neg] using
        average_add (indicator A) (fun _ ↦ -((A.card : ℂ) / N))
    _ = 0 := by rw [average_indicator]; simp

/-- The normalized weighted count of ordered three-term progressions
`(x, x+d, x+2d)`.  The common difference may be zero. -/
noncomputable def threeAPCount (f g h : ZMod N → ℂ) : ℂ :=
  average fun x ↦ average fun d ↦ f x * g (x + d) * h (x + d + d)

/-- The same normalized count written using the first and middle terms. -/
noncomputable def threeAPEquationCount (f g h : ZMod N → ℂ) : ℂ :=
  average fun a ↦ average fun b ↦ f a * g b * h (b + b - a)

/-- The progression parametrization `(x,d)` and the equation
parametrization `(a,b)` give exactly the same count. -/
theorem threeAPCount_eq_equationCount (f g h : ZMod N → ℂ) :
    threeAPCount f g h = threeAPEquationCount f g h := by
  unfold threeAPCount threeAPEquationCount
  apply congrArg average
  funext x
  let q : ZMod N → ℂ := fun b ↦ f x * g b * h (b + b - x)
  calc
    average (fun d ↦ f x * g (x + d) * h (x + d + d)) =
        average (fun d ↦ q (x + d)) := by
      apply congrArg average
      funext d
      dsimp only [q]
      congr 2
      abel
    _ = average q := average_add_left q x

/-- The equation-form progression count is an average of a convolution. -/
lemma threeAPEquationCount_eq_average_convolution (f g h : ZMod N → ℂ) :
    threeAPEquationCount f g h =
      average fun b ↦ g b * convolution f h (b + b) := by
  unfold threeAPEquationCount
  rw [average_comm]
  apply congrArg average
  funext b
  unfold convolution
  calc
    average (fun a ↦ f a * g b * h (b + b - a)) =
        average (fun a ↦ g b * (f a * h (b + b - a))) := by
      apply congrArg average
      funext a
      ring
    _ = g b * average (fun a ↦ f a * h (b + b - a)) :=
      average_const_mul _ _

/-- Exact Fourier expansion of the normalized ordered three-term-progression
count.  No parity assumption on `N` is needed. -/
theorem threeAPCount_eq_sum_fourier (f g h : ZMod N → ℂ) :
    threeAPCount f g h =
      ∑ r : ZMod N,
        fourier f r * fourier g (-(r + r)) * fourier h r := by
  have hchar (r b : ZMod N) :
      CyclicBohr.character r (b + b) = CyclicBohr.character (r + r) b := by
    rw [CyclicBohr.character_add, CyclicBohr.character_add_index]
  rw [threeAPCount_eq_equationCount,
    threeAPEquationCount_eq_average_convolution]
  calc
    average (fun b ↦ g b * convolution f h (b + b)) =
        average (fun b ↦ ∑ r : ZMod N,
          (fourier f r * fourier h r) *
            (g b * CyclicBohr.character r (b + b))) := by
      apply congrArg average
      funext b
      rw [← fourier_inversion (convolution f h) (b + b), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [fourier_convolution]
      ring
    _ = ∑ r : ZMod N, average (fun b ↦
          (fourier f r * fourier h r) *
            (g b * CyclicBohr.character r (b + b))) := average_sum _
    _ = ∑ r : ZMod N, (fourier f r * fourier h r) *
          average (fun b ↦ g b * CyclicBohr.character r (b + b)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact average_const_mul _ _
    _ = ∑ r : ZMod N, (fourier f r * fourier h r) *
          fourier g (-(r + r)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      congr 1
      rw [fourier_neg]
      apply congrArg average
      funext b
      rw [hchar]
      ring
    _ = ∑ r : ZMod N,
        fourier f r * fourier g (-(r + r)) * fourier h r := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring

end CyclicFourier
end Erdos721
