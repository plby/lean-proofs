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

import ErdosProblems.Erdos721.Rudin

/-!
# Chang's large-spectrum lemma for Erdős Problem 721

This file proves the logarithmic-rank spectral statement used in the cyclic
Bohr-set density-increment argument.  It is developed from the normalized
Fourier transform and the sharp power-form Rudin inequality in the preceding
modules.
-/

namespace Erdos721

open AddChar Finset
open scoped BigOperators

namespace CyclicChang

variable {N : ℕ} [NeZero N]

/-- The real density of a finite subset of the cyclic group. -/
noncomputable def density (A : Finset (ZMod N)) : ℝ := (A.card : ℝ) / N

lemma density_nonneg (A : Finset (ZMod N)) : 0 ≤ density A := by
  unfold density
  positivity

lemma density_le_one (A : Finset (ZMod N)) : density A ≤ 1 := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [density, div_le_one hN]
  exact_mod_cast A.card_le_univ.trans_eq (by simp [ZMod.card])

lemma density_pos {A : Finset (ZMod N)} (hA : A.Nonempty) : 0 < density A := by
  unfold density
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hA)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))

/-- The spectrum at threshold `η` times the density of `A`. -/
noncomputable def relativeLargeSpectrum (A : Finset (ZMod N)) (η : ℝ) :
    Finset (ZMod N) :=
  CyclicFourier.largeSpectrum (CyclicFourier.indicator A) (η * density A)

@[simp] lemma mem_relativeLargeSpectrum {A : Finset (ZMod N)} {η : ℝ} {r : ZMod N} :
    r ∈ relativeLargeSpectrum A η ↔
      η * density A ≤
        ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ := by
  simp [relativeLargeSpectrum]

/-- A unit complex scalar which rotates `z` onto its nonnegative norm. -/
noncomputable def aligningPhase (z : ℂ) : ℂ :=
  Classical.choose (Complex.exists_norm_eq_mul_self z)

lemma norm_aligningPhase (z : ℂ) : ‖aligningPhase z‖ = 1 :=
  (Classical.choose_spec (Complex.exists_norm_eq_mul_self z)).1

lemma aligningPhase_mul (z : ℂ) : aligningPhase z * z = (‖z‖ : ℂ) :=
  (Classical.choose_spec (Complex.exists_norm_eq_mul_self z)).2.symm

/-- The phase-aligned trigonometric polynomial attached to a frequency set. -/
noncomputable def alignedPoly (A : Finset (ZMod N)) (Δ : Finset (ZMod N))
    (x : ZMod N) : ℂ :=
  ∑ r ∈ Δ,
    aligningPhase ((starRingEnd ℂ)
      (CyclicFourier.fourier (CyclicFourier.indicator A) r)) *
      CyclicBohr.character r x

lemma average_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → ZMod N → ℂ) :
    CyclicFourier.average (fun x ↦ ∑ i ∈ s, F i x) =
      ∑ i ∈ s, CyclicFourier.average (F i) := by
  unfold CyclicFourier.average
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Phase alignment expresses the sum of Fourier magnitudes as an average of
the indicator against a trigonometric polynomial. -/
lemma sum_norm_fourier_eq_average_alignedPoly
    (A Δ : Finset (ZMod N)) :
    ((∑ r ∈ Δ,
      ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ : ℝ) : ℂ) =
      CyclicFourier.average (fun x ↦
        CyclicFourier.indicator A x * alignedPoly A Δ x) := by
  have hstar (r : ZMod N) :
      (starRingEnd ℂ) (CyclicFourier.fourier (CyclicFourier.indicator A) r) =
        CyclicFourier.average (fun x ↦
          CyclicBohr.character r x * CyclicFourier.indicator A x) := by
    rw [CyclicFourier.star_fourier]
    apply congrArg CyclicFourier.average
    funext x
    by_cases hx : x ∈ A <;> simp [CyclicFourier.indicator, hx]
  calc
    ((∑ r ∈ Δ,
        ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ : ℝ) : ℂ) =
        ∑ r ∈ Δ,
          aligningPhase ((starRingEnd ℂ)
            (CyclicFourier.fourier (CyclicFourier.indicator A) r)) *
          (starRingEnd ℂ)
            (CyclicFourier.fourier (CyclicFourier.indicator A) r) := by
      push_cast
      apply Finset.sum_congr rfl
      intro r _hr
      rw [aligningPhase_mul]
      simp
    _ = ∑ r ∈ Δ,
        CyclicFourier.average (fun x ↦
          aligningPhase ((starRingEnd ℂ)
            (CyclicFourier.fourier (CyclicFourier.indicator A) r)) *
          (CyclicBohr.character r x * CyclicFourier.indicator A x)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [hstar, CyclicFourier.average_const_mul]
    _ = CyclicFourier.average (fun x ↦
        ∑ r ∈ Δ,
          aligningPhase ((starRingEnd ℂ)
            (CyclicFourier.fourier (CyclicFourier.indicator A) r)) *
          (CyclicBohr.character r x * CyclicFourier.indicator A x)) := by
      exact (average_finset_sum Δ _).symm
    _ = CyclicFourier.average (fun x ↦
        CyclicFourier.indicator A x * alignedPoly A Δ x) := by
      apply congrArg CyclicFourier.average
      funext x
      unfold alignedPoly
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Every frequency in a relative large spectrum contributes its threshold
to the phase-aligned sum. -/
lemma card_mul_threshold_le_sum_norm_fourier
    (A : Finset (ZMod N)) {η : ℝ} (hη : 0 ≤ η)
    (Δ : Finset (ZMod N)) (hΔ : Δ ⊆ relativeLargeSpectrum A η) :
    (Δ.card : ℝ) * (η * density A) ≤
      ∑ r ∈ Δ, ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ := by
  calc
    (Δ.card : ℝ) * (η * density A) = ∑ _r ∈ Δ, η * density A := by simp
    _ ≤ ∑ r ∈ Δ,
        ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact mem_relativeLargeSpectrum.mp (hΔ hr)

/-- The aligned Fourier sum is bounded by the normalized first moment of the
real part of the aligned polynomial on `A`. -/
lemma sum_norm_fourier_le_expect_indicator_abs_re
    (A Δ : Finset (ZMod N)) :
    (∑ r ∈ Δ,
      ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ : ℝ) ≤
      𝔼 x : ZMod N, if x ∈ A then |(alignedPoly A Δ x).re| else 0 := by
  have halign := sum_norm_fourier_eq_average_alignedPoly A Δ
  have hre := congrArg Complex.re halign
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc
    (∑ r ∈ Δ,
        ‖CyclicFourier.fourier (CyclicFourier.indicator A) r‖ : ℝ) =
        (N : ℝ)⁻¹ * ∑ x : ZMod N,
          (CyclicFourier.indicator A x * alignedPoly A Δ x).re := by
      simpa [CyclicFourier.average] using hre
    _ ≤ (N : ℝ)⁻¹ * ∑ x : ZMod N,
          (if x ∈ A then |(alignedPoly A Δ x).re| else 0) := by
      gcongr with x
      by_cases hx : x ∈ A
      · simp [CyclicFourier.indicator, hx, le_abs_self]
      · simp [CyclicFourier.indicator, hx]
    _ = 𝔼 x : ZMod N,
          if x ∈ A then |(alignedPoly A Δ x).re| else 0 := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [ZMod.card]
      ring

/-- Large-spectrum membership and phase alignment give the lower half of
Chang's Hölder argument. -/
lemma card_mul_threshold_le_expect_indicator_abs_re
    (A : Finset (ZMod N)) {η : ℝ} (hη : 0 ≤ η)
    (Δ : Finset (ZMod N)) (hΔ : Δ ⊆ relativeLargeSpectrum A η) :
    (Δ.card : ℝ) * (η * density A) ≤
      𝔼 x : ZMod N, if x ∈ A then |(alignedPoly A Δ x).re| else 0 :=
  (card_mul_threshold_le_sum_norm_fourier A hη Δ hΔ).trans
    (sum_norm_fourier_le_expect_indicator_abs_re A Δ)

/-- Power-form Hölder on a finite subset, with normalized counting measure.
This formulation keeps all exponents natural and is exactly what is needed
to combine phase alignment with Rudin's moment inequality. -/
lemma expect_indicator_pow_le_density_mul_expect_pow
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x)
    (p : ℕ) (hp : 0 < p) :
    (𝔼 x : ZMod N, if x ∈ A then f x else 0) ^ p ≤
      density A ^ (p - 1) * (𝔼 x : ZMod N, (f x) ^ p) := by
  have hsum :
      (∑ x : ZMod N, if x ∈ A then f x else 0) = ∑ x ∈ A, f x := by
    classical
    simp
  have hpform : p - 1 + 1 = p := by omega
  have hpow :
      (∑ x ∈ A, f x) ^ p ≤
        (A.card : ℝ) ^ (p - 1) * ∑ x ∈ A, (f x) ^ p := by
    rw [← hpform]
    exact pow_sum_le_card_mul_sum_pow
      (fun x _hx ↦ hf x) (p - 1)
  have hsubset :
      ∑ x ∈ A, (f x) ^ p ≤ ∑ x : ZMod N, (f x) ^ p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro x _hx _hnot
    exact pow_nonneg (hf x) p
  have hraw :
      (∑ x ∈ A, f x) ^ p ≤
        (A.card : ℝ) ^ (p - 1) * ∑ x : ZMod N, (f x) ^ p :=
    hpow.trans (mul_le_mul_of_nonneg_left hsubset (by positivity))
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  simp_rw [Fintype.expect_eq_sum_div_card, ZMod.card, hsum, density]
  rw [div_pow, div_pow]
  calc
    (∑ x ∈ A, f x) ^ p / (N : ℝ) ^ p ≤
        ((A.card : ℝ) ^ (p - 1) * ∑ x : ZMod N, f x ^ p) /
          (N : ℝ) ^ p := div_le_div_of_nonneg_right hraw (by positivity)
    _ = ((A.card : ℝ) ^ (p - 1) / (N : ℝ) ^ (p - 1)) *
          ((∑ x : ZMod N, f x ^ p) / (N : ℝ)) := by
      have hNpow : (N : ℝ) ^ p = (N : ℝ) ^ (p - 1) * N := by
        calc
          (N : ℝ) ^ p = (N : ℝ) ^ (p - 1 + 1) := by rw [hpform]
          _ = (N : ℝ) ^ (p - 1) * N := by rw [pow_succ]
      rw [hNpow]
      field_simp

/-- The exact power inequality at the heart of Chang's lemma.  The left side
comes from the large Fourier coefficients; the right side combines Hölder
with the sharp Rudin moment bound. -/
lemma chang_power_inequality
    (A : Finset (ZMod N)) {η : ℝ} (hη : 0 ≤ η)
    (Δ : Finset (ZMod N)) (hΔspec : Δ ⊆ relativeLargeSpectrum A η)
    (hΔdiss : AddDissociated (Δ : Set (ZMod N)))
    (hΔnonempty : Δ.Nonempty) (p : ℕ) (hp : 0 < p) :
    ((Δ.card : ℝ) * (η * density A)) ^ p ≤
      density A ^ (p - 1) *
        (2 * Real.exp (1 / 2 : ℝ) *
          Real.sqrt ((p : ℝ) * Δ.card)) ^ p := by
  let f : ZMod N → ℝ := fun x ↦ |(alignedPoly A Δ x).re|
  have hlow := card_mul_threshold_le_expect_indicator_abs_re
    A hη Δ hΔspec
  have hleftnonneg :
      0 ≤ (Δ.card : ℝ) * (η * density A) :=
    mul_nonneg (by positivity) (mul_nonneg hη (density_nonneg A))
  have hholder := expect_indicator_pow_le_density_mul_expect_pow
    A f (fun x ↦ abs_nonneg _) p hp
  have hphase : ∀ r ∈ Δ,
      ‖aligningPhase ((starRingEnd ℂ)
        (CyclicFourier.fourier (CyclicFourier.indicator A) r))‖ = 1 := by
    intro r _hr
    exact norm_aligningPhase _
  have hrudin := CyclicRudin.cyclic_rudin_moment_bound_clean
    Δ hΔdiss
      (fun r ↦ aligningPhase ((starRingEnd ℂ)
        (CyclicFourier.fourier (CyclicFourier.indicator A) r)))
      hphase p hp (Finset.card_pos.mpr hΔnonempty)
  calc
    ((Δ.card : ℝ) * (η * density A)) ^ p ≤
        (𝔼 x : ZMod N, if x ∈ A then f x else 0) ^ p :=
      pow_le_pow_left₀ hleftnonneg hlow p
    _ ≤ density A ^ (p - 1) *
        (𝔼 x : ZMod N, (f x) ^ p) := hholder
    _ ≤ density A ^ (p - 1) *
        (2 * Real.exp (1 / 2 : ℝ) *
          Real.sqrt ((p : ℝ) * Δ.card)) ^ p := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [f, alignedPoly] using hrudin
      · exact pow_nonneg (density_nonneg A) (p - 1)

/-- Algebraic cancellation for the power inequality.  Supplying
`α⁻² ≤ exp (2p)` removes the sole density loss and leaves a linear dependence
on the moment parameter. -/
lemma card_le_of_chang_power
    {d α η K : ℝ} (hd : 0 < d) (hα : 0 < α) (hη : 0 < η)
    (hK : 0 ≤ K) (p : ℕ) (hp : 0 < p)
    (hpower : (d * (η * α)) ^ p ≤
      α ^ (p - 1) * (K * Real.sqrt ((p : ℝ) * d)) ^ p)
    (hinv : α⁻¹ ^ 2 ≤ Real.exp (2 * (p : ℝ))) :
    d ≤ K ^ 2 * (p : ℝ) * Real.exp 2 / η ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpd : (0 : ℝ) ≤ (p : ℝ) * d := mul_nonneg hpR.le hd.le
  have hsqrt : Real.sqrt ((p : ℝ) * d) ^ 2 = (p : ℝ) * d :=
    Real.sq_sqrt hpd
  have hαpow : 0 < α ^ (p - 1) := pow_pos hα _
  have hαsucc : α ^ (p - 1) * α = α ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hcancel :
      (d * η) ^ p * α ≤
        (K * Real.sqrt ((p : ℝ) * d)) ^ p := by
    apply le_of_mul_le_mul_left ?_ hαpow
    calc
      α ^ (p - 1) * ((d * η) ^ p * α) =
          (d * η) ^ p * (α ^ (p - 1) * α) := by ring
      _ = (d * η) ^ p * α ^ p := by rw [hαsucc]
      _ = ((d * η) * α) ^ p := (mul_pow (d * η) α p).symm
      _ = (d * (η * α)) ^ p := by ring
      _ ≤ α ^ (p - 1) *
          (K * Real.sqrt ((p : ℝ) * d)) ^ p := hpower
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (pow_nonneg (mul_nonneg hd.le hη.le) p) hα.le) hcancel 2
  have hnormalized :
      d ^ p * (((d * η ^ 2) ^ p) * α ^ 2) ≤
        d ^ p * ((K ^ 2 * (p : ℝ)) ^ p) := by
    calc
      d ^ p * (((d * η ^ 2) ^ p) * α ^ 2) =
          ((d * η) ^ p * α) ^ 2 := by
        simp only [mul_pow, pow_two]
        ring
      _ ≤ ((K * Real.sqrt ((p : ℝ) * d)) ^ p) ^ 2 := hsquare
      _ = d ^ p * ((K ^ 2 * (p : ℝ)) ^ p) := by
        rw [← pow_mul, mul_comm p 2, pow_mul]
        rw [mul_pow, hsqrt, mul_pow]
        ring
  have hcore :
      ((d * η ^ 2) ^ p) * α ^ 2 ≤ (K ^ 2 * (p : ℝ)) ^ p := by
    exact le_of_mul_le_mul_left hnormalized (pow_pos hd p)
  have hdiv :
      (d * η ^ 2) ^ p ≤ (K ^ 2 * (p : ℝ)) ^ p * α⁻¹ ^ 2 := by
    calc
      (d * η ^ 2) ^ p ≤ (K ^ 2 * (p : ℝ)) ^ p / α ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hα)).2 hcore
      _ = (K ^ 2 * (p : ℝ)) ^ p * α⁻¹ ^ 2 := by
        simp only [div_eq_mul_inv, inv_pow]
  have hboundpow :
      (d * η ^ 2) ^ p ≤
        (K ^ 2 * (p : ℝ) * Real.exp 2) ^ p := by
    calc
      (d * η ^ 2) ^ p ≤
          (K ^ 2 * (p : ℝ)) ^ p * α⁻¹ ^ 2 := hdiv
      _ ≤ (K ^ 2 * (p : ℝ)) ^ p * Real.exp (2 * (p : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (K ^ 2 * (p : ℝ) * Real.exp 2) ^ p := by
        have hexp : Real.exp (2 * (p : ℝ)) = Real.exp 2 ^ p := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        rw [hexp, mul_pow]
        ring
  have hroot : d * η ^ 2 ≤ K ^ 2 * (p : ℝ) * Real.exp 2 :=
    le_of_pow_le_pow_left₀ hp.ne' (by positivity) hboundpow
  rw [le_div_iff₀ (sq_pos_of_pos hη)]
  exact hroot

/-- The integer moment used in Chang's argument. -/
noncomputable def changMoment (α : ℝ) : ℕ :=
  ⌈Real.log α⁻¹⌉₊ + 1

lemma changMoment_pos (α : ℝ) : 0 < changMoment α := by
  simp [changMoment]

lemma log_inv_le_changMoment {α : ℝ} :
    Real.log α⁻¹ ≤ (changMoment α : ℝ) := by
  calc
    Real.log α⁻¹ ≤ (⌈Real.log α⁻¹⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (changMoment α : ℝ) := by
      simp [changMoment]

/-- The selected moment absorbs the density loss in the power inequality. -/
lemma inv_sq_le_exp_two_mul_changMoment {α : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) :
    α⁻¹ ^ 2 ≤ Real.exp (2 * (changMoment α : ℝ)) := by
  have hinvpos : 0 < α⁻¹ := inv_pos.mpr hα
  have hinvexp : α⁻¹ ≤ Real.exp (changMoment α : ℝ) := by
    calc
      α⁻¹ = Real.exp (Real.log α⁻¹) := (Real.exp_log hinvpos).symm
      _ ≤ Real.exp (changMoment α : ℝ) :=
        Real.exp_le_exp.mpr log_inv_le_changMoment
  calc
    α⁻¹ ^ 2 ≤ Real.exp (changMoment α : ℝ) ^ 2 :=
      pow_le_pow_left₀ hinvpos.le hinvexp 2
    _ = Real.exp (2 * (changMoment α : ℝ)) := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- The explicit natural-number rank bound produced by Chang's argument. -/
noncomputable def changRankBound (A : Finset (ZMod N)) (η : ℝ) : ℕ :=
  ⌈(2 * Real.exp (1 / 2 : ℝ)) ^ 2 * (changMoment (density A) : ℝ) *
      Real.exp 2 / η ^ 2⌉₊

/-- Every dissociated subset of the relative large spectrum obeys the
logarithmic Chang rank bound. -/
theorem dissociated_card_le_changRankBound
    (A : Finset (ZMod N)) (hA : A.Nonempty) {η : ℝ} (hη : 0 < η)
    (Δ : Finset (ZMod N)) (hΔspec : Δ ⊆ relativeLargeSpectrum A η)
    (hΔdiss : AddDissociated (Δ : Set (ZMod N))) :
    Δ.card ≤ changRankBound A η := by
  obtain hΔempty | hΔnonempty := Δ.eq_empty_or_nonempty
  · subst Δ
    simp [changRankBound]
  have hα := density_pos hA
  have hpower := chang_power_inequality A hη.le Δ hΔspec hΔdiss
    hΔnonempty (changMoment (density A)) (changMoment_pos _)
  have hreal : (Δ.card : ℝ) ≤
      (2 * Real.exp (1 / 2 : ℝ)) ^ 2 *
        (changMoment (density A) : ℝ) * Real.exp 2 / η ^ 2 :=
    card_le_of_chang_power
      (by exact_mod_cast Finset.card_pos.mpr hΔnonempty) hα hη
      (by positivity) (changMoment (density A)) (changMoment_pos _) hpower
      (inv_sq_le_exp_two_mul_changMoment hα (density_le_one A))
  have hceil : (Δ.card : ℝ) ≤ (changRankBound A η : ℝ) :=
    hreal.trans (by
      unfold changRankBound
      exact Nat.le_ceil _)
  exact_mod_cast hceil

/-- Chang's lemma in the construction-facing Bohr-set form: a Bohr set of
logarithmic rank controls every relative large-spectrum character. -/
theorem exists_bohr_controlling_relativeLargeSpectrum
    (A : Finset (ZMod N)) (hA : A.Nonempty) {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 ≤ ρ) :
    ∃ B : CyclicBohr.Set N,
      B.frequencies ⊆ relativeLargeSpectrum A η ∧
      B.rank ≤ changRankBound A η ∧
      ∀ r ∈ relativeLargeSpectrum A η, ∀ x ∈ B,
        ‖1 - CyclicBohr.character r x‖ ≤
          (changRankBound A η : ℝ) * ρ := by
  apply CyclicBohr.Set.exists_small_bohr_controlling_of_dissociated_card_le
    (relativeLargeSpectrum A η) (changRankBound A η) ρ hρ
  intro Δ hΔspec hΔdiss
  exact dissociated_card_le_changRankBound A hA hη Δ hΔspec hΔdiss

/-- Chang's Bohr set with its exact chosen radius and the sharp rank-times-
radius character control retained. -/
theorem exists_bohr_controlling_relativeLargeSpectrum_sharp
    (A : Finset (ZMod N)) (hA : A.Nonempty) {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 ≤ ρ) :
    ∃ B : CyclicBohr.Set N,
      B.radius = ρ ∧
      B.frequencies ⊆ relativeLargeSpectrum A η ∧
      B.rank ≤ changRankBound A η ∧
      ∀ r ∈ relativeLargeSpectrum A η, ∀ x ∈ B,
        ‖1 - CyclicBohr.character r x‖ ≤ (B.rank : ℝ) * ρ := by
  apply CyclicBohr.Set.exists_small_bohr_controlling_of_dissociated_card_le_sharp
    (relativeLargeSpectrum A η) (changRankBound A η) ρ hρ
  intro Δ hΔspec hΔdiss
  exact dissociated_card_le_changRankBound A hA hη Δ hΔspec hΔdiss

end CyclicChang
end Erdos721
