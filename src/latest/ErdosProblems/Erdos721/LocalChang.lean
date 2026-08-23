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
# The local Chang--Sanders entropy bound

The global form of Chang's lemma measures the size of a set against the
whole ambient group.  In the integer Kelley--Meka iteration this is not
enough: an almost-period set is dense only inside a Bohr carrier.  This file
starts the local replacement.  It defines Riesz-product dissociativity with
respect to the uniform probability measure on an arbitrary finite carrier
and proves the local form of Chang's entropy estimate.  The subsequent
annihilation argument uses this bound with a smoothed Bohr probability
measure.
-/

namespace Erdos721

open AddChar Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalChang

variable {N : ℕ} [NeZero N]

/-- The normalized average of a real-valued function over a nonempty finite
set.  We keep the definition algebraic, so all later arguments reduce to
finite sums. -/
noncomputable def finsetMean (S : Finset (ZMod N))
    (f : ZMod N → ℝ) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x

lemma finsetMean_const (S : Finset (ZMod N)) (hS : S.Nonempty) (c : ℝ) :
    finsetMean S (fun _ ↦ c) = c := by
  unfold finsetMean
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [hcard]

lemma finsetMean_nonneg (S : Finset (ZMod N)) (f : ZMod N → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    0 ≤ finsetMean S f := by
  unfold finsetMean
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x hx ↦ hf x hx)

lemma finsetMean_mono (S : Finset (ZMod N)) (f g : ZMod N → ℝ)
    (hfg : ∀ x ∈ S, f x ≤ g x) :
    finsetMean S f ≤ finsetMean S g := by
  unfold finsetMean
  gcongr with x hx
  exact hfg x hx

/-- A Riesz product over cyclic frequency indices. -/
noncomputable def rieszProduct (Δ : Finset (ZMod N))
    (ω : ZMod N → ℂ) (x : ZMod N) : ℝ :=
  ∏ r ∈ Δ, (1 + (ω r * CyclicBohr.character r x).re)

lemma rieszProduct_nonneg (Δ : Finset (ZMod N))
    (ω : ZMod N → ℂ) (hω : ∀ r ∈ Δ, ‖ω r‖ ≤ 1) (x : ZMod N) :
    0 ≤ rieszProduct Δ ω x := by
  unfold rieszProduct
  apply Finset.prod_nonneg
  intro r hr
  have hre : -(1 : ℝ) ≤ (ω r * CyclicBohr.character r x).re := by
    calc
      -(1 : ℝ) ≤ -‖ω r‖ := neg_le_neg (hω r hr)
      _ = -‖ω r * CyclicBohr.character r x‖ := by
        rw [norm_mul, CyclicBohr.norm_character, mul_one]
      _ ≤ (ω r * CyclicBohr.character r x).re :=
        neg_le_of_abs_le (Complex.abs_re_le_norm _)
  linarith

/-- `K`-dissociativity relative to the uniform measure on `S`, in the
Riesz-product sense used by Sanders. -/
def LocallyDissociated (S Δ : Finset (ZMod N)) (K : ℝ) : Prop :=
  ∀ ω : ZMod N → ℂ, (∀ r ∈ Δ, ‖ω r‖ ≤ 1) →
    finsetMean S (rieszProduct Δ ω) ≤ Real.exp K

lemma locallyDissociated_mono_parameter {S Δ : Finset (ZMod N)}
    {K L : ℝ} (hKL : K ≤ L) (h : LocallyDissociated S Δ K) :
    LocallyDissociated S Δ L := by
  intro ω hω
  exact (h ω hω).trans (Real.exp_le_exp.mpr hKL)

lemma locallyDissociated_empty (S : Finset (ZMod N)) (hS : S.Nonempty)
    {K : ℝ} (hK : 0 ≤ K) :
    LocallyDissociated S ∅ K := by
  intro ω _hω
  rw [show rieszProduct (N := N) ∅ ω = fun _ ↦ 1 by
    funext x
    simp [rieszProduct]]
  rw [finsetMean_const S hS]
  simpa using Real.exp_le_exp.mpr hK

/-- The coefficient used to align the Fourier coefficient of `X` at `r`.
It has unit norm, including when the Fourier coefficient vanishes. -/
noncomputable def localAligningPhase (X : Finset (ZMod N))
    (r : ZMod N) : ℂ :=
  CyclicChang.aligningPhase
    ((starRingEnd ℂ)
      (CyclicFourier.fourier (CyclicFourier.indicator X) r))

lemma norm_localAligningPhase (X : Finset (ZMod N)) (r : ZMod N) :
    ‖localAligningPhase X r‖ = 1 := by
  exact CyclicChang.norm_aligningPhase _

lemma localAlignedPoly_eq (X Δ : Finset (ZMod N)) (x : ZMod N) :
    CyclicChang.alignedPoly X Δ x =
      ∑ r ∈ Δ, localAligningPhase X r * CyclicBohr.character r x := by
  rfl

/-- On a relative large spectrum, the phase-aligned polynomial has mean at
least `eta * |Δ|` over the set itself. -/
lemma eta_mul_card_le_finsetMean_re_alignedPoly
    (X : Finset (ZMod N)) (hX : X.Nonempty)
    {eta : ℝ} (heta : 0 ≤ eta)
    (Δ : Finset (ZMod N))
    (hΔ : Δ ⊆ CyclicChang.relativeLargeSpectrum X eta) :
    eta * (Δ.card : ℝ) ≤
      finsetMean X (fun x ↦ (CyclicChang.alignedPoly X Δ x).re) := by
  have hsum := CyclicChang.card_mul_threshold_le_sum_norm_fourier
    X heta Δ hΔ
  have halign := CyclicChang.sum_norm_fourier_eq_average_alignedPoly X Δ
  have hre := congrArg Complex.re halign
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hXcard : (0 : ℝ) < X.card := by
    exact_mod_cast hX.card_pos
  have hmeanEq :
      finsetMean X (fun x ↦ (CyclicChang.alignedPoly X Δ x).re) =
        (N : ℝ) / X.card *
          ∑ r ∈ Δ,
            ‖CyclicFourier.fourier
              (CyclicFourier.indicator X) r‖ := by
    have hre' :
        (∑ r ∈ Δ,
          ‖CyclicFourier.fourier
            (CyclicFourier.indicator X) r‖) =
          (N : ℝ)⁻¹ * ∑ x : ZMod N,
            (CyclicFourier.indicator X x *
              CyclicChang.alignedPoly X Δ x).re := by
      simpa [CyclicFourier.average] using hre
    have hsumRe :
        (∑ x : ZMod N,
          (CyclicFourier.indicator X x *
            CyclicChang.alignedPoly X Δ x).re) =
          ∑ x ∈ X, (CyclicChang.alignedPoly X Δ x).re := by
      classical
      simp only [CyclicFourier.indicator]
      calc
        (∑ x : ZMod N,
            ((if x ∈ X then (1 : ℂ) else 0) *
              CyclicChang.alignedPoly X Δ x).re) =
            ∑ x : ZMod N,
              if x ∈ X then (CyclicChang.alignedPoly X Δ x).re else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxX : x ∈ X <;> simp [hxX]
        _ = ∑ x ∈ X, (CyclicChang.alignedPoly X Δ x).re := by simp
    unfold finsetMean
    rw [← hsumRe, hre']
    field_simp
  rw [hmeanEq]
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (div_nonneg hN.le hXcard.le)
  unfold CyclicChang.density at hscaled
  have hcancel :
      (N : ℝ) / X.card *
          ((Δ.card : ℝ) * (eta * ((X.card : ℝ) / N))) =
        eta * (Δ.card : ℝ) := by
    field_simp
  rw [hcancel] at hscaled
  exact hscaled

/-- Jensen's inequality for the uniform average on a finite set. -/
lemma exp_finsetMean_le_finsetMean_exp
    (S : Finset (ZMod N)) (hS : S.Nonempty) (f : ZMod N → ℝ) :
    Real.exp (finsetMean S f) ≤
      finsetMean S (fun x ↦ Real.exp (f x)) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hweight :
      ∑ _x ∈ S, (S.card : ℝ)⁻¹ = 1 := by
    simp
    field_simp
  have hjensen := convexOn_exp.map_sum_le
    (t := S) (w := fun _ : ZMod N ↦ (S.card : ℝ)⁻¹)
    (p := f)
    (fun _ _ ↦ inv_nonneg.mpr hcard.le) hweight
    (fun _ _ ↦ Set.mem_univ _)
  simpa only [finsetMean, smul_eq_mul, Function.comp_apply,
    ← Finset.mul_sum] using hjensen

/-- Restricting a nonnegative average from `S` to `X` costs the reciprocal
relative density `|S|/|X|`. -/
lemma finsetMean_le_card_ratio_mul_finsetMean
    (X S : Finset (ZMod N)) (hX : X.Nonempty) (hXS : X ⊆ S)
    (f : ZMod N → ℝ) (hf : ∀ x ∈ S, 0 ≤ f x) :
    finsetMean X f ≤
    ((S.card : ℝ) / X.card) * finsetMean S f := by
  have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hScard : (0 : ℝ) < S.card := by
    exact_mod_cast (hX.mono hXS).card_pos
  have hsum : ∑ x ∈ X, f x ≤ ∑ x ∈ S, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hXS
      (fun x hxS _hxX ↦ hf x hxS)
  unfold finsetMean
  calc
    (X.card : ℝ)⁻¹ * ∑ x ∈ X, f x ≤
        (X.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by gcongr
    _ = ((S.card : ℝ) / X.card) *
        ((S.card : ℝ)⁻¹ * ∑ x ∈ S, f x) := by
      field_simp

private lemma cyclic_exp_alignedPoly_le_raw_product
    (X Δ : Finset (ZMod N)) {t : ℝ} (ht : 0 < t) (x : ZMod N) :
    Real.exp (t * (CyclicChang.alignedPoly X Δ x).re) ≤
      ∏ r ∈ Δ,
        (Real.cosh t +
          ((localAligningPhase X r * (Real.sinh t : ℂ)) *
            CyclicBohr.character r x).re) := by
  let c' : AddChar (ZMod N) ℂ → ℂ := fun ψ ↦
    localAligningPhase X (AddChar.zmodAddEquiv.symm ψ)
  have hc' : ∀ ψ ∈ CyclicRudin.cyclicCharacterImage Δ, ‖c' ψ‖ = 1 := by
    intro ψ hψ
    rw [CyclicRudin.cyclicCharacterImage, Finset.mem_map] at hψ
    obtain ⟨r, hr, rfl⟩ := hψ
    simpa only [c', CyclicRudin.cyclicCharacterEmbedding_apply,
      CyclicBohr.character, AddEquiv.symm_apply_apply] using
        norm_localAligningPhase X r
  have hpoly :
      CyclicRudin.trigPoly (CyclicRudin.cyclicCharacterImage Δ) c' x =
        CyclicChang.alignedPoly X Δ x := by
    rw [localAlignedPoly_eq]
    unfold CyclicRudin.trigPoly CyclicRudin.cyclicCharacterImage
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [c', CyclicRudin.cyclicCharacterEmbedding_apply,
      CyclicBohr.character, AddEquiv.symm_apply_apply]
  have hraw := CyclicRudin.exp_re_trigPoly_le_prod
    (CyclicRudin.cyclicCharacterImage Δ) c' hc' ht x
  rw [hpoly] at hraw
  have hleft :
      (((t : ℂ) * CyclicChang.alignedPoly X Δ x).re) =
        t * (CyclicChang.alignedPoly X Δ x).re := by simp
  rw [hleft] at hraw
  calc
    Real.exp (t * (CyclicChang.alignedPoly X Δ x).re) ≤
        ∏ ψ ∈ CyclicRudin.cyclicCharacterImage Δ,
          (Real.cosh t +
            ((c' ψ * (Real.sinh t : ℂ)) * ψ x).re) := hraw
    _ = ∏ r ∈ Δ,
          (Real.cosh t +
            ((localAligningPhase X r * (Real.sinh t : ℂ)) *
              CyclicBohr.character r x).re) := by
      unfold CyclicRudin.cyclicCharacterImage
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro r hr
      simp only [c', CyclicRudin.cyclicCharacterEmbedding_apply,
        CyclicBohr.character, AddEquiv.symm_apply_apply]

/-- The exponential of an aligned character sum is bounded by a scalar
Gaussian factor times a Riesz product. -/
lemma exp_alignedPoly_le_cosh_rieszProduct
    (X Δ : Finset (ZMod N)) {t : ℝ} (ht : 0 < t) (x : ZMod N) :
    Real.exp (t * (CyclicChang.alignedPoly X Δ x).re) ≤
      (Real.cosh t) ^ Δ.card *
        rieszProduct Δ
          (fun r ↦ (Real.tanh t : ℂ) * localAligningPhase X r) x := by
  have hraw := cyclic_exp_alignedPoly_le_raw_product X Δ ht x
  calc
    Real.exp (t * (CyclicChang.alignedPoly X Δ x).re) ≤
        ∏ r ∈ Δ,
          (Real.cosh t +
            ((localAligningPhase X r * (Real.sinh t : ℂ)) *
              CyclicBohr.character r x).re) := hraw
    _ = ∏ r ∈ Δ,
        (Real.cosh t *
          (1 + (((Real.tanh t : ℂ) * localAligningPhase X r) *
            CyclicBohr.character r x).re)) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hcosh : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
      have hsinh : (Real.sinh t : ℂ) =
          (Real.cosh t : ℂ) * (Real.tanh t : ℂ) := by
        have hsinhR : Real.sinh t = Real.cosh t * Real.tanh t := by
          rw [Real.tanh_eq_sinh_div_cosh]
          field_simp
        exact_mod_cast hsinhR
      rw [hsinh]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero]
      ring
    _ = (Real.cosh t) ^ Δ.card *
        rieszProduct Δ
          (fun r ↦ (Real.tanh t : ℂ) * localAligningPhase X r) x := by
      rw [Finset.prod_mul_distrib]
      simp [rieszProduct]

lemma norm_tanh_mul_localAligningPhase_le_one
    (X : Finset (ZMod N)) {t : ℝ} (r : ZMod N) :
    ‖(Real.tanh t : ℂ) * localAligningPhase X r‖ ≤ 1 := by
  rw [norm_mul, norm_localAligningPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  exact (Real.abs_tanh_lt_one t).le

/-- Local Chang entropy: a Riesz-dissociated subset of the relative large
spectrum has cardinality logarithmic in the reciprocal relative density.
The deliberately explicit constant is more than sufficient for the later
rank recurrence. -/
theorem locallyDissociated_card_bound
    (X S : Finset (ZMod N)) (hX : X.Nonempty) (hXS : X ⊆ S)
    {eta K : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (Δ : Finset (ZMod N))
    (hΔspec : Δ ⊆ CyclicChang.relativeLargeSpectrum X eta)
    (hΔdiss : LocallyDissociated S Δ K) :
    (Δ.card : ℝ) ≤
      2 * (Real.log ((S.card : ℝ) / X.card) + K) / eta ^ 2 := by
  have hS : S.Nonempty := hX.mono hXS
  have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hratio : 1 ≤ (S.card : ℝ) / X.card := by
    rw [one_le_div hXcard]
    exact_mod_cast Finset.card_le_card hXS
  have hmean := eta_mul_card_le_finsetMean_re_alignedPoly
    X hX heta0.le Δ hΔspec
  have hjensen := exp_finsetMean_le_finsetMean_exp X hX
    (fun x ↦ eta * (CyclicChang.alignedPoly X Δ x).re)
  have hmeanScale :
      finsetMean X (fun x ↦ eta * (CyclicChang.alignedPoly X Δ x).re) =
        eta * finsetMean X
          (fun x ↦ (CyclicChang.alignedPoly X Δ x).re) := by
    unfold finsetMean
    rw [← Finset.mul_sum]
    ring
  have hlow :
      Real.exp (eta ^ 2 * (Δ.card : ℝ)) ≤
        finsetMean X
          (fun x ↦ Real.exp
            (eta * (CyclicChang.alignedPoly X Δ x).re)) := by
    calc
      Real.exp (eta ^ 2 * (Δ.card : ℝ)) ≤
          Real.exp (finsetMean X
            (fun x ↦ eta * (CyclicChang.alignedPoly X Δ x).re)) := by
        apply Real.exp_le_exp.mpr
        rw [hmeanScale]
        nlinarith
      _ ≤ _ := hjensen
  let ω : ZMod N → ℂ := fun r ↦
    (Real.tanh eta : ℂ) * localAligningPhase X r
  have hω : ∀ r ∈ Δ, ‖ω r‖ ≤ 1 := by
    intro r hr
    exact norm_tanh_mul_localAligningPhase_le_one X r
  have hrieszNonneg : ∀ x ∈ S, 0 ≤ rieszProduct Δ ω x := by
    intro x hx
    exact rieszProduct_nonneg Δ ω hω x
  have hrestrict := finsetMean_le_card_ratio_mul_finsetMean
    X S hX hXS
    (fun x ↦ Real.exp
      (eta * (CyclicChang.alignedPoly X Δ x).re))
    (fun x hx ↦ (Real.exp_pos _).le)
  have hpoint (x : ZMod N) :
      Real.exp (eta * (CyclicChang.alignedPoly X Δ x).re) ≤
        (Real.cosh eta) ^ Δ.card * rieszProduct Δ ω x := by
    exact exp_alignedPoly_le_cosh_rieszProduct X Δ heta0 x
  have hmeanPoint :
      finsetMean S
          (fun x ↦ Real.exp
            (eta * (CyclicChang.alignedPoly X Δ x).re)) ≤
        (Real.cosh eta) ^ Δ.card * finsetMean S (rieszProduct Δ ω) := by
    calc
      finsetMean S
          (fun x ↦ Real.exp
            (eta * (CyclicChang.alignedPoly X Δ x).re)) ≤
          finsetMean S
            (fun x ↦ (Real.cosh eta) ^ Δ.card * rieszProduct Δ ω x) :=
        finsetMean_mono S _ _ (fun x hx ↦ hpoint x)
      _ = (Real.cosh eta) ^ Δ.card *
          finsetMean S (rieszProduct Δ ω) := by
        unfold finsetMean
        rw [← Finset.mul_sum]
        ring
  have hcosh :
      (Real.cosh eta) ^ Δ.card ≤
        Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) := by
    calc
      (Real.cosh eta) ^ Δ.card ≤
          (Real.exp (eta ^ 2 / 2)) ^ Δ.card := by
        gcongr
        exact Real.cosh_le_exp_half_sq eta
      _ = Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]
        push_cast
        congr 1
        ring
  have hupper :
      finsetMean X
          (fun x ↦ Real.exp
            (eta * (CyclicChang.alignedPoly X Δ x).re)) ≤
        ((S.card : ℝ) / X.card) *
          Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2 + K) := by
    calc
      finsetMean X
          (fun x ↦ Real.exp
            (eta * (CyclicChang.alignedPoly X Δ x).re)) ≤
          ((S.card : ℝ) / X.card) *
            finsetMean S
              (fun x ↦ Real.exp
                (eta * (CyclicChang.alignedPoly X Δ x).re)) := hrestrict
      _ ≤ ((S.card : ℝ) / X.card) *
          ((Real.cosh eta) ^ Δ.card *
            finsetMean S (rieszProduct Δ ω)) := by gcongr
      _ ≤ ((S.card : ℝ) / X.card) *
          (Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) * Real.exp K) := by
        have hmeanRnonneg :
            0 ≤ finsetMean S (rieszProduct Δ ω) :=
          finsetMean_nonneg S _ hrieszNonneg
        have hproduct :
            (Real.cosh eta) ^ Δ.card *
                finsetMean S (rieszProduct Δ ω) ≤
              Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) * Real.exp K := by
          calc
            (Real.cosh eta) ^ Δ.card *
                  finsetMean S (rieszProduct Δ ω) ≤
                Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) *
                  finsetMean S (rieszProduct Δ ω) :=
              mul_le_mul_of_nonneg_right hcosh hmeanRnonneg
            _ ≤ Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2) *
                Real.exp K :=
              mul_le_mul_of_nonneg_left (hΔdiss ω hω)
                (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hproduct
          (div_nonneg hScard.le hXcard.le)
      _ = ((S.card : ℝ) / X.card) *
          Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2 + K) := by
        rw [Real.exp_add]
  have hexp :
      Real.exp (eta ^ 2 * (Δ.card : ℝ)) ≤
        ((S.card : ℝ) / X.card) *
          Real.exp (eta ^ 2 * (Δ.card : ℝ) / 2 + K) :=
    hlow.trans hupper
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp,
    Real.log_mul (div_pos hScard hXcard).ne' (Real.exp_pos _).ne',
    Real.log_exp] at hlog
  rw [le_div_iff₀ (sq_pos_of_pos heta0)]
  nlinarith

end CyclicLocalChang
end Erdos721
