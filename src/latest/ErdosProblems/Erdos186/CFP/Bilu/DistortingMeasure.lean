/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The measure of Bilu's distorting set

This file formalizes the Fourier-analytic part of Proposition 8.1 in
Yuri Bilu's exposition of Freiman's theorem.  Frequencies are integral
points `Fin m → ℤ`, and integration is over the unit torus with
normalized Haar measure.  The unit torus is measure-isomorphic, up to its
null boundary, to the half-open cube `[0,1)^m`, so this is precisely the
Lebesgue volume used in the paper.

The key input is character orthogonality.  It is proved below from Haar
translation invariance: a nontrivial character has a translate equal to
its negative.  The remaining estimate is Bilu's Cauchy--Schwarz argument.
-/

namespace Erdos186.CFP.Bilu.DistortingMeasure

open scoped BigOperators ENNReal NNReal
open MeasureTheory

/-- The `m`-dimensional unit torus. -/
abbrev Torus (m : ℕ) := Fin m → AddCircle (1 : ℝ)

/-- Normalized Haar measure on the unit torus. -/
noncomputable def torusMeasure (m : ℕ) : Measure (Torus m) :=
  Measure.pi fun _ : Fin m ↦ AddCircle.haarAddCircle

noncomputable instance torusMeasure_isProbabilityMeasure (m : ℕ) :
    IsProbabilityMeasure (torusMeasure m) := by
  dsimp [torusMeasure]
  infer_instance

noncomputable instance torusMeasure_isAddRightInvariant (m : ℕ) :
    Measure.IsAddRightInvariant (torusMeasure m) := by
  dsimp [torusMeasure]
  infer_instance

/-- The torus character associated to an integral frequency. -/
noncomputable def character {m : ℕ} (x : Fin m → ℤ) (a : Torus m) : ℂ :=
  ∏ i, fourier (x i) (a i)

@[simp]
theorem character_zero {m : ℕ} (a : Torus m) :
    character (0 : Fin m → ℤ) a = 1 := by
  simp [character]

theorem character_add_argument {m : ℕ} (x : Fin m → ℤ) (a b : Torus m) :
    character x (a + b) = character x a * character x b := by
  rw [character, character, character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Pi.add_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  rfl

theorem character_add_frequency {m : ℕ} (x y : Fin m → ℤ) (a : Torus m) :
    character (x + y) a = character x a * character y a := by
  simp only [character, Pi.add_apply, fourier_add,
    Finset.prod_mul_distrib]

theorem character_neg {m : ℕ} (x : Fin m → ℤ) (a : Torus m) :
    character (-x) a = starRingEnd ℂ (character x a) := by
  simp only [character, Pi.neg_apply, fourier_neg, map_prod]

theorem character_norm {m : ℕ} (x : Fin m → ℤ) (a : Torus m) :
    ‖character x a‖ = 1 := by
  simp [character, Circle.norm_coe]

theorem continuous_character {m : ℕ} (x : Fin m → ℤ) :
    Continuous (character x) := by
  unfold character
  fun_prop

theorem integrable_character {m : ℕ} (x : Fin m → ℤ) :
    Integrable (character x) (torusMeasure m) := by
  apply Integrable.of_bound (continuous_character x).aestronglyMeasurable 1
  filter_upwards [] with a
  exact (character_norm x a).le

/-- A nonzero integral frequency defines a character whose normalized
Haar integral vanishes.  This is the character-orthogonality step in
Bilu's proof. -/
theorem integral_character {m : ℕ} (x : Fin m → ℤ) :
    ∫ a, character x a ∂torusMeasure m = if x = 0 then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [torusMeasure]
  · simp only [hx, if_false]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      simpa [Function.ne_iff] using hx
    let b : Torus m := fun j ↦
      if j = i then ((1 / 2 / (x i : ℝ) : ℝ) : AddCircle (1 : ℝ)) else 0
    have hb : character x b = -1 := by
      rw [character, Finset.prod_eq_single i]
      · simpa [b] using
          (fourier_add_half_inv_index (T := (1 : ℝ)) hi (by norm_num)
            (0 : AddCircle (1 : ℝ)))
      · intro j hj hji
        simp [b, hji]
      · simp
    let I : ℂ := ∫ a, character x a ∂torusMeasure m
    have hI : I = -I := by
      calc
        I = ∫ a, character x (a + b) ∂torusMeasure m := by
          exact (integral_add_right_eq_self (character x) b).symm
        _ = ∫ a, -(character x a) ∂torusMeasure m := by
          apply integral_congr_ae
          filter_upwards [] with a
          rw [character_add_argument, hb, mul_neg, mul_one]
        _ = -I := by rw [integral_neg]
    have htwo : (2 : ℂ) * I = 0 := by
      linear_combination hI
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Orthogonality in the form used to expand finite trigonometric
polynomials. -/
theorem integral_character_sub {m : ℕ} (x y : Fin m → ℤ) :
    ∫ a, character (x - y) a ∂torusMeasure m = if x = y then 1 else 0 := by
  rw [integral_character]
  simp only [sub_eq_zero]

/-! ## Finite Fourier polynomials and their second moments -/

/-- The exponential sum attached to a finite set of integral frequencies. -/
noncomputable def trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) (a : Torus m) : ℂ :=
  ∑ x ∈ K, character x a

theorem continuous_trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) :
    Continuous (trigPolynomial K) := by
  unfold trigPolynomial
  exact continuous_finsetSum K fun x hx ↦ continuous_character x

theorem integrable_trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) :
    Integrable (trigPolynomial K) (torusMeasure m) := by
  apply Integrable.of_bound (continuous_trigPolynomial K).aestronglyMeasurable K.card
  filter_upwards [] with a
  calc
    ‖trigPolynomial K a‖ ≤ ∑ x ∈ K, ‖character x a‖ := norm_sum_le _ _
    _ = K.card := by simp [character_norm]

theorem norm_trigPolynomial_le_card {m : ℕ} (K : Finset (Fin m → ℤ)) (a : Torus m) :
    ‖trigPolynomial K a‖ ≤ K.card := by
  calc
    ‖trigPolynomial K a‖ ≤ ∑ x ∈ K, ‖character x a‖ := norm_sum_le _ _
    _ = K.card := by simp [character_norm]

theorem star_mul_trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) (a : Torus m) :
    starRingEnd ℂ (trigPolynomial K a) * trigPolynomial K a =
      ∑ x ∈ K, ∑ y ∈ K, character (x - y) a := by
  simp only [trigPolynomial, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [← character_neg y a, ← character_add_frequency]
  apply congrArg (fun z ↦ character z a)
  abel

/-- Parseval orthogonality for the finite exponential sum. -/
theorem integral_star_mul_trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) :
    ∫ a, starRingEnd ℂ (trigPolynomial K a) * trigPolynomial K a ∂torusMeasure m =
      (K.card : ℂ) := by
  rw [show (∫ a, starRingEnd ℂ (trigPolynomial K a) * trigPolynomial K a
      ∂torusMeasure m) =
      ∫ a, ∑ x ∈ K, ∑ y ∈ K, character (x - y) a ∂torusMeasure m by
        apply integral_congr_ae
        filter_upwards [] with a
        exact star_mul_trigPolynomial K a]
  rw [integral_finsetSum K (fun x hx ↦
    integrable_finsetSum K fun y hy ↦ integrable_character (x - y))]
  calc
    ∑ x ∈ K, ∫ a, ∑ y ∈ K, character (x - y) a ∂torusMeasure m =
        ∑ x ∈ K, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_finsetSum K (fun y hy ↦ integrable_character (x - y))]
      simp only [integral_character, sub_eq_zero]
      rw [Finset.sum_eq_single_of_mem x hx]
      · simp
      · intro y hy hyx
        simp [hyx.symm]
    _ = (K.card : ℂ) := by simp

/-- The real `L²` identity corresponding to `integral_star_mul_trigPolynomial`. -/
theorem integral_norm_sq_trigPolynomial {m : ℕ} (K : Finset (Fin m → ℤ)) :
    ∫ a, ‖trigPolynomial K a‖ ^ 2 ∂torusMeasure m = (K.card : ℝ) := by
  calc
    ∫ a, ‖trigPolynomial K a‖ ^ 2 ∂torusMeasure m =
        ∫ a, Complex.re
          (starRingEnd ℂ (trigPolynomial K a) * trigPolynomial K a) ∂torusMeasure m := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq, Complex.mul_re]
    _ = Complex.re (∫ a, starRingEnd ℂ (trigPolynomial K a) *
        trigPolynomial K a ∂torusMeasure m) := by
      have hf : Integrable (fun a ↦ star (trigPolynomial K a) * trigPolynomial K a)
          (torusMeasure m) := by
        apply Integrable.of_bound
          ((continuous_trigPolynomial K).star.mul
            (continuous_trigPolynomial K)).aestronglyMeasurable (K.card ^ 2)
        filter_upwards [] with a
        change ‖star (trigPolynomial K a) * trigPolynomial K a‖ ≤ (K.card : ℝ) ^ 2
        rw [norm_mul, norm_star]
        simpa [pow_two] using
          (mul_self_le_mul_self (norm_nonneg _) (norm_trigPolynomial_le_card K a))
      change (∫ a, RCLike.re (star (trigPolynomial K a) * trigPolynomial K a)
          ∂torusMeasure m) =
        RCLike.re (∫ a, star (trigPolynomial K a) * trigPolynomial K a ∂torusMeasure m)
      exact integral_re hf
    _ = (K.card : ℝ) := by rw [integral_star_mul_trigPolynomial]; simp

/-! ## The sumset pairing -/

/-- The (unweighted) finite sumset `K + K`. -/
def sumset {m : ℕ} (K : Finset (Fin m → ℤ)) : Finset (Fin m → ℤ) :=
  K.image₂ (fun x y ↦ x + y) K

theorem add_mem_sumset {m : ℕ} {K : Finset (Fin m → ℤ)}
    {x y : Fin m → ℤ} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ sumset K := by
  exact Finset.mem_image₂.mpr ⟨x, hx, y, hy, rfl⟩

theorem pairing_integrand_expansion {m : ℕ} (K : Finset (Fin m → ℤ)) (a : Torus m) :
    trigPolynomial K a * trigPolynomial K a *
        starRingEnd ℂ (trigPolynomial (sumset K) a) =
      ∑ z ∈ sumset K, ∑ y ∈ K, ∑ x ∈ K, character (x + y - z) a := by
  simp only [trigPolynomial, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  rw [← character_neg x a, ← character_add_frequency z y a,
    ← character_add_frequency (z + y) (-x) a]
  apply congrArg (fun w ↦ character w a)
  abel

theorem pairing_integrand_expansion_ordered {m : ℕ}
    (K : Finset (Fin m → ℤ)) (a : Torus m) :
    trigPolynomial K a * trigPolynomial K a *
        starRingEnd ℂ (trigPolynomial (sumset K) a) =
      ∑ x ∈ K, ∑ y ∈ K, ∑ z ∈ sumset K, character (x + y - z) a := by
  rw [pairing_integrand_expansion]
  calc
    ∑ z ∈ sumset K, ∑ y ∈ K, ∑ x ∈ K, character (x + y - z) a =
        ∑ y ∈ K, ∑ z ∈ sumset K, ∑ x ∈ K, character (x + y - z) a := by
      exact Finset.sum_comm
    _ = ∑ y ∈ K, ∑ x ∈ K, ∑ z ∈ sumset K, character (x + y - z) a := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x ∈ K, ∑ y ∈ K, ∑ z ∈ sumset K, character (x + y - z) a := by
      exact Finset.sum_comm

/-- Bilu's exact Fourier pairing: every ordered pair `(x,y)` contributes
once, at the distinct sumset frequency `x+y`. -/
theorem integral_sumset_pairing {m : ℕ} (K : Finset (Fin m → ℤ)) :
    ∫ a, trigPolynomial K a * trigPolynomial K a *
        starRingEnd ℂ (trigPolynomial (sumset K) a) ∂torusMeasure m =
      (K.card : ℂ) ^ 2 := by
  rw [show (∫ a, trigPolynomial K a * trigPolynomial K a *
      starRingEnd ℂ (trigPolynomial (sumset K) a) ∂torusMeasure m) =
      ∫ a, ∑ x ∈ K, ∑ y ∈ K, ∑ z ∈ sumset K,
        character (x + y - z) a ∂torusMeasure m by
        apply integral_congr_ae
        filter_upwards [] with a
        exact pairing_integrand_expansion_ordered K a]
  rw [integral_finsetSum K (fun x hx ↦
    integrable_finsetSum K fun y hy ↦
      integrable_finsetSum (sumset K) fun z hz ↦ integrable_character (x + y - z))]
  calc
    ∑ x ∈ K, ∫ a, ∑ y ∈ K, ∑ z ∈ sumset K,
        character (x + y - z) a ∂torusMeasure m =
        ∑ x ∈ K, (K.card : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_finsetSum K (fun y hy ↦
        integrable_finsetSum (sumset K) fun z hz ↦
          integrable_character (x + y - z))]
      calc
        ∑ y ∈ K, ∫ a, ∑ z ∈ sumset K,
            character (x + y - z) a ∂torusMeasure m =
            ∑ y ∈ K, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [integral_finsetSum (sumset K) (fun z hz ↦
            integrable_character (x + y - z))]
          simp only [integral_character, sub_eq_zero]
          rw [Finset.sum_eq_single_of_mem (x + y) (add_mem_sumset hx hy)]
          · simp
          · intro z hz hne
            simp [Ne.symm hne]
        _ = (K.card : ℂ) := by simp
    _ = (K.card : ℂ) ^ 2 := by simp [pow_two]

/-- Cauchy--Schwarz for two finite torus polynomials, with Parseval
evaluating both factors. -/
theorem integral_norm_mul_le_sqrt_card_mul_sqrt_card {m : ℕ}
    (K L : Finset (Fin m → ℤ)) :
    ∫ a, ‖trigPolynomial K a‖ * ‖trigPolynomial L a‖ ∂torusMeasure m ≤
      Real.sqrt K.card * Real.sqrt L.card := by
  have hK : MemLp (fun a ↦ ‖trigPolynomial K a‖) 2 (torusMeasure m) := by
    apply MemLp.of_bound (continuous_trigPolynomial K).norm.aestronglyMeasurable K.card
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_trigPolynomial_le_card K a
  have hL : MemLp (fun a ↦ ‖trigPolynomial L a‖) 2 (torusMeasure m) := by
    apply MemLp.of_bound (continuous_trigPolynomial L).norm.aestronglyMeasurable L.card
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_trigPolynomial_le_card L a
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := torusMeasure m)
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := fun a ↦ ‖trigPolynomial K a‖) (g := fun a ↦ ‖trigPolynomial L a‖)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun a ↦ norm_nonneg _) (ae_of_all _ fun a ↦ norm_nonneg _)
    (by simpa using hK) (by simpa using hL)
  calc
    ∫ a, ‖trigPolynomial K a‖ * ‖trigPolynomial L a‖ ∂torusMeasure m ≤
        (∫ a, ‖trigPolynomial K a‖ ^ 2 ∂torusMeasure m) ^ (1 / (2 : ℝ)) *
          (∫ a, ‖trigPolynomial L a‖ ^ 2 ∂torusMeasure m) ^ (1 / (2 : ℝ)) := by
      simpa only [Real.rpow_two] using h
    _ = Real.sqrt K.card * Real.sqrt L.card := by
      rw [integral_norm_sq_trigPolynomial, integral_norm_sq_trigPolynomial]
      simp only [Real.sqrt_eq_rpow]

/-! ## Bilu's distorting set estimate -/

/-- Frequencies at which the exponential sum is larger than `δ |K|`. -/
def distortingSet {m : ℕ} (δ : ℝ) (K : Finset (Fin m → ℤ)) : Set (Torus m) :=
  {a | δ * K.card < ‖trigPolynomial K a‖}

theorem measurableSet_distortingSet {m : ℕ} (δ : ℝ)
    (K : Finset (Fin m → ℤ)) : MeasurableSet (distortingSet δ K) := by
  exact measurableSet_lt measurable_const (continuous_trigPolynomial K).norm.measurable

theorem integrable_pairingNorm {m : ℕ} (K : Finset (Fin m → ℤ)) :
    Integrable (fun a ↦ ‖trigPolynomial K a‖ ^ 2 *
      ‖trigPolynomial (sumset K) a‖) (torusMeasure m) := by
  apply Integrable.of_bound
    (((continuous_trigPolynomial K).norm.pow 2).mul
      (continuous_trigPolynomial (sumset K)).norm).aestronglyMeasurable
    (K.card ^ 2 * (sumset K).card)
  filter_upwards [] with a
  change ‖‖trigPolynomial K a‖ ^ 2 * ‖trigPolynomial (sumset K) a‖‖ ≤
    (K.card : ℝ) ^ 2 * (sumset K).card
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_trigPolynomial_le_card K a) 2)
    (norm_trigPolynomial_le_card (sumset K) a) (norm_nonneg _)
    (by positivity)

theorem integrable_normProduct {m : ℕ} (K L : Finset (Fin m → ℤ)) :
    Integrable (fun a ↦ ‖trigPolynomial K a‖ * ‖trigPolynomial L a‖)
      (torusMeasure m) := by
  apply Integrable.of_bound
    ((continuous_trigPolynomial K).norm.mul
      (continuous_trigPolynomial L).norm).aestronglyMeasurable (K.card * L.card)
  filter_upwards [] with a
  change ‖‖trigPolynomial K a‖ * ‖trigPolynomial L a‖‖ ≤
    (K.card : ℝ) * L.card
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (norm_trigPolynomial_le_card K a)
    (norm_trigPolynomial_le_card L a) (norm_nonneg _) (by positivity)

/-- The norm of Bilu's exact pairing gives the lower side of the
integral estimate. -/
theorem card_sq_le_integral_pairingNorm {m : ℕ}
    (K : Finset (Fin m → ℤ)) :
    (K.card : ℝ) ^ 2 ≤ ∫ a, ‖trigPolynomial K a‖ ^ 2 *
      ‖trigPolynomial (sumset K) a‖ ∂torusMeasure m := by
  calc
    (K.card : ℝ) ^ 2 =
        ‖∫ a, trigPolynomial K a * trigPolynomial K a *
          starRingEnd ℂ (trigPolynomial (sumset K) a) ∂torusMeasure m‖ := by
      rw [integral_sumset_pairing]
      simp
    _ ≤ ∫ a, ‖trigPolynomial K a * trigPolynomial K a *
          starRingEnd ℂ (trigPolynomial (sumset K) a)‖ ∂torusMeasure m :=
      norm_integral_le_integral_norm _
    _ = ∫ a, ‖trigPolynomial K a‖ ^ 2 *
        ‖trigPolynomial (sumset K) a‖ ∂torusMeasure m := by
      apply integral_congr_ae
      filter_upwards [] with a
      simp only [norm_mul, pow_two]
      change ‖trigPolynomial K a‖ * ‖trigPolynomial K a‖ *
        ‖star (trigPolynomial (sumset K) a)‖ = _
      rw [norm_star]

/-- The non-strict numerical form of Proposition 8.1.  The strict form
below uses the fact that the omitted part of the Cauchy--Schwarz integral
has positive mass. -/
theorem distortingSet_measure_lower_bound {m : ℕ}
    (K : Finset (Fin m → ℤ)) (σ δ : ℝ)
    (hK : K.Nonempty) (hσ : 0 < σ)
    (hδ : 0 ≤ δ)
    (hsum : ((sumset K).card : ℝ) ≤ σ * K.card) :
    (1 - δ * Real.sqrt σ) / (σ * K.card) ≤
      (torusMeasure m).real (distortingSet δ K) := by
  let P : Torus m → ℂ := trigPolynomial K
  let Q : Torus m → ℂ := trigPolynomial (sumset K)
  let M : Set (Torus m) := distortingSet δ K
  have hkpos : 0 < (K.card : ℝ) := by exact_mod_cast hK.card_pos
  have hk0 : 0 ≤ (K.card : ℝ) := hkpos.le
  have hs0 : 0 ≤ ((sumset K).card : ℝ) := by positivity
  have hM : MeasurableSet M := measurableSet_distortingSet δ K
  have hf : Integrable (fun a ↦ ‖P a‖ ^ 2 * ‖Q a‖) (torusMeasure m) :=
    integrable_pairingNorm K
  have hg : Integrable (fun a ↦ ‖P a‖ * ‖Q a‖) (torusMeasure m) :=
    integrable_normProduct K (sumset K)
  have hPM (a : Torus m) : ‖P a‖ ≤ K.card := norm_trigPolynomial_le_card K a
  have hQM (a : Torus m) : ‖Q a‖ ≤ (sumset K).card :=
    norm_trigPolynomial_le_card (sumset K) a
  have hinside : ∫ a in M, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
      (torusMeasure m).real M * (σ * (K.card : ℝ) ^ 3) := by
    calc
      ∫ a in M, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
          ∫ _a in M, σ * (K.card : ℝ) ^ 3 ∂torusMeasure m := by
        apply setIntegral_mono_on hf.integrableOn (integrable_const _).integrableOn hM
        intro a ha
        have h1 : ‖P a‖ ^ 2 ≤ (K.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hPM a) 2
        have h2 : ‖P a‖ ^ 2 * ‖Q a‖ ≤
            (K.card : ℝ) ^ 2 * (sumset K).card :=
          mul_le_mul h1 (hQM a) (norm_nonneg _) (sq_nonneg _)
        nlinarith
      _ = (torusMeasure m).real M * (σ * (K.card : ℝ) ^ 3) := by
        simp [smul_eq_mul]
  have houtside : ∫ a in Mᶜ, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
      δ * K.card * ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m := by
    calc
      ∫ a in Mᶜ, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
          ∫ a in Mᶜ, (δ * K.card) * (‖P a‖ * ‖Q a‖) ∂torusMeasure m := by
        apply setIntegral_mono_on hf.integrableOn
          (hg.const_mul (δ * K.card)).integrableOn hM.compl
        intro a ha
        have ha' : ‖P a‖ ≤ δ * K.card := by
          exact le_of_not_gt ha
        calc
          ‖P a‖ ^ 2 * ‖Q a‖ = ‖P a‖ * (‖P a‖ * ‖Q a‖) := by ring
          _ ≤ (δ * K.card) * (‖P a‖ * ‖Q a‖) :=
            mul_le_mul_of_nonneg_right ha'
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = δ * K.card * ∫ a in Mᶜ, ‖P a‖ * ‖Q a‖ ∂torusMeasure m := by
        rw [integral_const_mul]
      _ ≤ δ * K.card * ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m := by
        apply mul_le_mul_of_nonneg_left
        · exact setIntegral_le_integral hg (ae_of_all _ fun a ↦
            mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · positivity
  have hcs : ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m ≤
      Real.sqrt σ * K.card := by
    calc
      ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m ≤
          Real.sqrt K.card * Real.sqrt (sumset K).card :=
        integral_norm_mul_le_sqrt_card_mul_sqrt_card K (sumset K)
      _ ≤ Real.sqrt K.card * Real.sqrt (σ * K.card) := by
        gcongr
      _ = Real.sqrt σ * K.card := by
        rw [Real.sqrt_mul (le_of_lt hσ)]
        calc
          Real.sqrt K.card * (Real.sqrt σ * Real.sqrt K.card) =
              Real.sqrt σ * (Real.sqrt K.card * Real.sqrt K.card) := by ring
          _ = Real.sqrt σ * K.card := by rw [Real.mul_self_sqrt hk0]
  have hupper : ∫ a, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
      (torusMeasure m).real M * (σ * (K.card : ℝ) ^ 3) +
        δ * Real.sqrt σ * (K.card : ℝ) ^ 2 := by
    rw [← integral_add_compl hM hf]
    calc
      (∫ a in M, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m) +
          ∫ a in Mᶜ, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m ≤
          (torusMeasure m).real M * (σ * (K.card : ℝ) ^ 3) +
            δ * K.card * ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m :=
        add_le_add hinside houtside
      _ ≤ (torusMeasure m).real M * (σ * (K.card : ℝ) ^ 3) +
          δ * Real.sqrt σ * (K.card : ℝ) ^ 2 := by
        have hterm :
            δ * K.card * ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m ≤
              δ * Real.sqrt σ * (K.card : ℝ) ^ 2 := by
          calc
          δ * K.card * ∫ a, ‖P a‖ * ‖Q a‖ ∂torusMeasure m ≤
              δ * K.card * (Real.sqrt σ * K.card) := by
            exact mul_le_mul_of_nonneg_left hcs (mul_nonneg hδ hk0)
          _ = δ * Real.sqrt σ * (K.card : ℝ) ^ 2 := by ring
        exact add_le_add_right hterm _
  have hlower : (K.card : ℝ) ^ 2 ≤
      ∫ a, ‖P a‖ ^ 2 * ‖Q a‖ ∂torusMeasure m :=
    card_sq_le_integral_pairingNorm K
  have hden : 0 < σ * (K.card : ℝ) := mul_pos hσ hkpos
  apply (div_le_iff₀ hden).2
  have := hlower.trans hupper
  apply le_of_mul_le_mul_right
  ring_nf at this ⊢
  · nlinarith
  · exact hkpos

/-- **Bilu, Proposition 8.1 (normalized-Haar form).**

If `K` is nonempty, `|K+K| ≤ σ |K|`, and
`0 < δ < 1 / √σ`, then the set on which the exponential sum of
`K` is `δ`-distorting has normalized volume at least
`(1 - δ √σ) / (σ |K|)`.  The upper restriction on `δ` records the
source's nontrivial range; the estimate itself remains valid outside that
range as `distortingSet_measure_lower_bound` shows. -/
theorem bilu_proposition_8_1 {m : ℕ}
    (K : Finset (Fin m → ℤ)) (σ δ : ℝ)
    (hK : K.Nonempty) (hσ : 0 < σ)
    (hδpos : 0 < δ) (_hδlt : δ < 1 / Real.sqrt σ)
    (hsum : ((sumset K).card : ℝ) ≤ σ * K.card) :
    (1 - δ * Real.sqrt σ) / (σ * K.card) ≤
      (torusMeasure m).real (distortingSet δ K) := by
  exact distortingSet_measure_lower_bound K σ δ hK hσ hδpos.le hsum

end Erdos186.CFP.Bilu.DistortingMeasure

#print axioms Erdos186.CFP.Bilu.DistortingMeasure.integral_character
#print axioms Erdos186.CFP.Bilu.DistortingMeasure.bilu_proposition_8_1
