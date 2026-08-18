/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.OneDimensionalDiscrepancy

/-!
# The finite Fejer kernel on the unit additive circle

This file gives a completely finite construction of the Fejer kernel used
to smooth arc indicators.  Frequencies are grouped from the square of a
finite geometric character sum; in particular positivity and the tail
estimate do not appeal to convergence of a Fourier series.
-/

open scoped BigOperators ComplexConjugate ENNReal Real
open Finset Function MeasureTheory Set

namespace Erdos1124.OneDimensionalDiscrepancy

noncomputable section

/-- The frequency contributed by one pair in the square of a geometric sum. -/
def fejerPairFrequency {N : ℕ} (p : Fin N × Fin N) : ℤ :=
  (p.1.val : ℤ) - p.2.val

/-- The finite frequency support of the Fejer kernel of order `N`. -/
def fejerFrequencies (N : ℕ) : Finset ℤ := by
  classical
  exact (Finset.univ : Finset (Fin N × Fin N)).image fejerPairFrequency

/-- The (real) coefficient of a frequency in the Fejer kernel. -/
def fejerCoefficient (N : ℕ) (h : ℤ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun p : Fin N × Fin N =>
    fejerPairFrequency p = h).card : ℝ) / N

/-- The Fejer kernel, normalized to have Haar integral one. -/
def fejerPolynomial (N : ℕ) (x : Circle) : ℝ :=
  (∑ h ∈ fejerFrequencies N,
    (fejerCoefficient N h : ℂ) * character (h • x)).re

private lemma fejer_grouped (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N =>
          fejerPairFrequency p = h), character (fejerPairFrequency p • x)) =
      ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) := by
  classical
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [Finset.filter_eq_self.2]
  intro p hp
  simp only [fejerFrequencies, Finset.mem_image]
  exact ⟨p, Finset.mem_univ _, rfl⟩

private lemma fejer_pair_sum_eq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (∑ j : Fin N, character ((j.val : ℤ) • x)) *
        (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) := by
  calc
    _ = ∑ j : Fin N, ∑ k : Fin N,
        character (fejerPairFrequency (j, k) • x) := by
      exact Fintype.sum_prod_type (γ := ℂ)
        (fun p : Fin N × Fin N => character (fejerPairFrequency p • x))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← character_add]
      congr 2
      simp only [fejerPairFrequency, sub_eq_add_neg, add_smul]

private lemma fejer_neg_sum_eq_conj (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
      star (∑ k : Fin N, character ((k.val : ℤ) • x)) := by
  change (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
    (starRingEnd ℂ) (∑ k : Fin N, character ((k.val : ℤ) • x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AddCircle.toCircle ((-(k.val : ℤ)) • x) =
    (starRingEnd ℂ) (AddCircle.toCircle ((k.val : ℤ) • x))
  rw [neg_smul, AddCircle.toCircle_neg]
  exact _root_.Circle.coe_inv_eq_conj _

private lemma fejer_fin_sum_eq_geo (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((k.val : ℤ) • x)) =
      geometricCharacterSum N x := by
  rw [geometricCharacterSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natCast_zsmul]

private lemma fejer_pair_sum_eq_norm_sq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (‖geometricCharacterSum N x‖ ^ 2 : ℝ) := by
  rw [fejer_pair_sum_eq, fejer_neg_sum_eq_conj, fejer_fin_sum_eq_geo]
  change geometricCharacterSum N x *
    (starRingEnd ℂ) (geometricCharacterSum N x) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _ |>.symm

/-- The grouped finite Fourier sum is the normalized squared geometric sum. -/
lemma complex_fejerPolynomial_eq (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x) =
      ((‖geometricCharacterSum N x‖ ^ 2 / N : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_div]
  push_cast
  have hpair := fejer_pair_sum_eq_norm_sq N x
  rw [← Complex.ofReal_pow, ← hpair, ← fejer_grouped N x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h hh
  rw [fejerCoefficient, Complex.ofReal_div]
  push_cast
  rw [div_mul_eq_mul_div]
  congr 1
  calc
    (#{p : Fin N × Fin N | fejerPairFrequency p = h} : ℂ) *
        character (h • x) =
        ∑ p with fejerPairFrequency p = h, character (h • x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ p with fejerPairFrequency p = h,
        character (fejerPairFrequency p • x) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

/-- Pointwise square formula for the Fejer kernel. -/
lemma fejerPolynomial_eq (N : ℕ) (x : Circle) :
    fejerPolynomial N x = ‖geometricCharacterSum N x‖ ^ 2 / N := by
  have h := congrArg Complex.re (complex_fejerPolynomial_eq N x)
  simpa only [fejerPolynomial, Complex.ofReal_re] using h

/-- The Fejer kernel is pointwise nonnegative. -/
lemma fejerPolynomial_nonneg (N : ℕ) (x : Circle) :
    0 ≤ fejerPolynomial N x := by
  rw [fejerPolynomial_eq]
  positivity

/-- Away from zero the Fejer kernel has a uniform inverse-square tail. -/
lemma fejerPolynomial_le_of_distance {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {x : Circle} (hx : η ≤ integerDistance x) :
    fejerPolynomial N x ≤ 1 / (4 * N * η ^ 2) := by
  rw [fejerPolynomial_eq]
  have hgeom :=
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hnorm := norm_nonneg (geometricCharacterSum N x)
  have hdist := integerDistance_nonneg x
  have hbound : 2 * η * ‖geometricCharacterSum N x‖ ≤ 1 := by nlinarith
  have hsquare : 4 * η ^ 2 * ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 := by
    have hs := mul_self_le_mul_self (mul_nonneg (by positivity) hnorm) hbound
    nlinarith
  have hn2 : ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 / (4 * η ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η ^ 2)]
    nlinarith
  calc
    ‖geometricCharacterSum N x‖ ^ 2 / (N : ℝ) ≤
        (1 / (4 * η ^ 2)) / N := by gcongr
    _ = 1 / (4 * N * η ^ 2) := by field_simp

private lemma integral_character (h : ℤ) :
    ∫ x : Circle, character (h • x) ∂circleHaar = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp
  · simp only [hh, ↓reduceIte]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hh (by norm_num))

/-- The Fejer kernel has normalized Haar integral one. -/
lemma integral_fejerPolynomial {N : ℕ} (hN : 0 < N) :
    ∫ x : Circle, fejerPolynomial N x ∂circleHaar = 1 := by
  simp_rw [fejerPolynomial]
  have hterm : ∀ h ∈ fejerFrequencies N,
      Integrable (fun x : Circle =>
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    intro h hh
    apply Integrable.const_mul
    apply Integrable.of_bound (fourier h).continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => (norm_character (h • x)).le
  have hint : Integrable (fun x : Circle =>
      ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    have hi := integrable_finsetSum' (fejerFrequencies N) hterm
    have heq : (∑ h ∈ fejerFrequencies N,
        fun x : Circle => (fejerCoefficient N h : ℂ) * character (h • x)) =
        fun x : Circle => ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) := by
      funext x
      exact Finset.sum_apply x (fejerFrequencies N) _
    rw [← heq]
    exact hi
  calc
    (∫ x : Circle, (∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)).re ∂circleHaar) =
        (∫ x : Circle, ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) ∂circleHaar).re :=
      integral_re hint
    _ = 1 := by
      rw [integral_finset_sum (fejerFrequencies N) hterm]
      simp_rw [integral_const_mul, integral_character]
      rw [Finset.sum_eq_single 0]
      · rw [if_pos rfl, mul_one]
        unfold fejerCoefficient fejerPairFrequency
        have hdiag : (Finset.univ.filter fun p : Fin N × Fin N =>
            (p.1.val : ℤ) - p.2.val = 0).card = N := by
          rw [show (Finset.univ.filter fun p : Fin N × Fin N =>
              (p.1.val : ℤ) - p.2.val = 0) =
              Finset.univ.image (fun j : Fin N => (j, j)) by
            ext p
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_image]
            constructor
            · intro hp
              have : p.1 = p.2 := by
                apply Fin.ext
                omega
              exact ⟨p.1, by ext <;> simp [this]⟩
            · rintro ⟨j, -, rfl⟩
              simp]
          calc
            (Finset.univ.image (fun j : Fin N => (j, j))).card =
                (Finset.univ : Finset (Fin N)).card :=
              Finset.card_image_of_injective _ fun i j h => by
                simpa using congrArg Prod.fst h
            _ = N := by simp
        rw [hdiag, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
        norm_num
      · intro h hh hne
        rw [if_neg hne, mul_zero]
      · intro hz
        exfalso
        apply hz
        unfold fejerFrequencies
        apply Finset.mem_image.2
        exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _,
          by simp [fejerPairFrequency]⟩

/-! ## Finite Fourier expansion of Fejer smoothing -/

/-- Convolution with the Fejer kernel. -/
def fejerSmooth (N : ℕ) (f : Circle → ℝ) (x : Circle) : ℝ :=
  ∫ y : Circle, f y * fejerPolynomial N (x - y) ∂circleHaar

/-- A Fourier coefficient of the Fejer smoothing of `f`. -/
def fejerSmoothCoefficient (N : ℕ) (f : Circle → ℝ) (h : ℤ) : ℂ :=
  (fejerCoefficient N h : ℂ) *
    ∫ y : Circle, (f y : ℂ) * character ((-h) • y) ∂circleHaar

private lemma fejer_character_sub (h : ℤ) (x y : Circle) :
    character (h • (x - y)) =
      character (h • x) * character ((-h) • y) := by
  rw [smul_sub, sub_eq_add_neg, character_add, ← neg_smul]

private lemma integrable_complex_mul_character {f : Circle → ℝ}
    (hf : Integrable f circleHaar) (h : ℤ) :
    Integrable (fun y : Circle =>
      (f y : ℂ) * character (h • y)) circleHaar := by
  apply Integrable.mul_bdd hf.ofReal
  · exact (fourier h).continuous.aestronglyMeasurable
  · exact ae_of_all _ fun y => (norm_character (h • y)).le

/-- Fejer convolution is exactly a finite Fourier polynomial. -/
lemma fejerSmooth_eq_fullFourier (N : ℕ) {f : Circle → ℝ}
    (hf : Integrable f circleHaar) (x : Circle) :
    fejerSmooth N f x =
      realTrigTail (fejerFrequencies N) (fejerSmoothCoefficient N f) x := by
  unfold fejerSmooth realTrigTail
  let q : ℤ → Circle → ℂ := fun h y =>
    (f y : ℂ) * ((fejerCoefficient N h : ℂ) * character (h • (x-y)))
  have hq : ∀ h ∈ fejerFrequencies N, Integrable (q h) circleHaar := by
    intro h hh
    unfold q
    have hi := integrable_complex_mul_character hf (-h)
    have hi' : Integrable
        (fun y : Circle => ((fejerCoefficient N h : ℂ) * character (h • x)) *
          ((f y : ℂ) * character ((-h) • y))) circleHaar := hi.const_mul _
    apply hi'.congr
    filter_upwards [] with y
    rw [fejer_character_sub]
    ring
  have hsum : Integrable
      (fun y : Circle => ∑ h ∈ fejerFrequencies N, q h y) circleHaar := by
    have hi := integrable_finsetSum' (fejerFrequencies N) hq
    have heq : (∑ h ∈ fejerFrequencies N, q h) =
        fun y : Circle => ∑ h ∈ fejerFrequencies N, q h y := by
      funext y
      exact Finset.sum_apply y (fejerFrequencies N) q
    rw [← heq]
    exact hi
  calc
    (∫ y : Circle, f y * fejerPolynomial N (x-y) ∂circleHaar) =
        ∫ y : Circle, (∑ h ∈ fejerFrequencies N, q h y).re ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with y
      unfold q
      rw [← Finset.mul_sum]
      change f y * fejerPolynomial N (x-y) =
        ((f y : ℂ) * (∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • (x-y)))).re
      rw [complex_fejerPolynomial_eq, fejerPolynomial_eq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    _ = (∫ y : Circle, ∑ h ∈ fejerFrequencies N, q h y
          ∂circleHaar).re := integral_re hsum
    _ = (∑ h ∈ fejerFrequencies N,
        fejerSmoothCoefficient N f h * character (h • x)).re := by
      rw [integral_finset_sum (fejerFrequencies N) hq]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      unfold q fejerSmoothCoefficient
      rw [show (∫ y : Circle,
          (f y : ℂ) * ((fejerCoefficient N h : ℂ) *
            character (h • (x-y))) ∂circleHaar) =
          ∫ y : Circle, ((fejerCoefficient N h : ℂ) * character (h • x)) *
            ((f y : ℂ) * character ((-h) • y)) ∂circleHaar by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [fejer_character_sub]
        ring]
      rw [integral_const_mul]
      ring

/-! ## Haar measure of arcs -/

lemma measurableSet_arc (a : Circle) (ℓ : ℝ) : MeasurableSet (arc a ℓ) := by
  unfold arc
  change MeasurableSet ((fun x : Circle =>
    ((AddCircle.equivIco 1 0) (x - a) : ℝ)) ⁻¹' Iio ℓ)
  exact measurableSet_Iio.preimage <| measurable_subtype_coe.comp <|
    (AddCircle.measurableEquivIco 1 0).measurable.comp
      (measurable_id.sub measurable_const)

lemma integrable_arcIndicator (a : Circle) (ℓ : ℝ) :
    Integrable (arcIndicator a ℓ) circleHaar := by
  apply Integrable.of_bound _ 1
  · exact ae_of_all _ fun x => by
      by_cases hx : x ∈ arc a ℓ <;> simp [arcIndicator, hx]
  · change AEStronglyMeasurable
      ((arc a ℓ).indicator (fun _ : Circle => (1 : ℝ))) circleHaar
    exact (aestronglyMeasurable_indicator_iff (measurableSet_arc a ℓ)).2
      aestronglyMeasurable_const

private lemma integral_arcIndicator_zero {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    ∫ x : Circle, arcIndicator 0 ℓ x ∂circleHaar = ℓ := by
  rw [circleHaar_eq_volume, ← AddCircle.integral_preimage 1 0]
  simp only [zero_add]
  have hae : (fun x : ℝ => arcIndicator 0 ℓ (x : Circle)) =ᵐ[
      (volume : Measure ℝ).restrict (Ioc 0 1)]
      (Ioo 0 ℓ).indicator (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_le ((volume : Measure ℝ).ae_ne 1)] with x hx hx1
    have hx1' : x ≠ 1 := by simpa only [Set.mem_setOf_eq] using hx1
    have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1'⟩
    rw [arcIndicator]
    have heq := AddCircle.equivIco_coe_eq
      (p := (1 : ℝ)) (a := (0 : ℝ)) (x := x)
      (by simpa only [zero_add] using hxIco)
    simp only [arc, sub_zero, heq, Set.mem_setOf_eq,
      Set.indicator_apply, Set.mem_Ioo]
    split_ifs <;> simp_all
  rw [integral_congr_ae hae, setIntegral_indicator measurableSet_Ioo]
  rw [inter_eq_right.2]
  · simp [hℓ0]
  · intro x hx
    exact ⟨hx.1, hx.2.le.trans hℓ1⟩

private lemma arcIndicator_add_left (a x : Circle) (ℓ : ℝ) :
    arcIndicator a ℓ (a + x) = arcIndicator 0 ℓ x := by
  simp only [arcIndicator]
  congr 1
  simp [arc]

lemma integral_arcIndicator (a : Circle) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    ∫ x : Circle, arcIndicator a ℓ x ∂circleHaar = ℓ := by
  have hi := MeasurePreserving.integral_comp
    (measurePreserving_add_left circleHaar a)
    (MeasurableEquiv.addLeft a).measurableEmbedding (arcIndicator a ℓ)
  calc
    (∫ x : Circle, arcIndicator a ℓ x ∂circleHaar) =
        ∫ x : Circle, arcIndicator 0 ℓ x ∂circleHaar := by
      rw [← hi]
      apply integral_congr_ae
      exact ae_of_all _ fun x => arcIndicator_add_left a x ℓ
    _ = ℓ := integral_arcIndicator_zero hℓ0 hℓ1

lemma circleHaarReal_arc (a : Circle) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    circleHaar.real (arc a ℓ) = ℓ := by
  have hi := integral_arcIndicator a hℓ0 hℓ1
  have hind := integral_indicator_const (μ := circleHaar) (1 : ℝ)
    (measurableSet_arc a ℓ)
  rw [smul_eq_mul, mul_one] at hind
  calc
    circleHaar.real (arc a ℓ) =
        ∫ x : Circle, (arc a ℓ).indicator (fun _ => (1 : ℝ)) x ∂circleHaar :=
      hind.symm
    _ = ∫ x : Circle, arcIndicator a ℓ x ∂circleHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        by_cases hx : x ∈ arc a ℓ <;> simp [arcIndicator, Set.indicator, hx]
    _ = ℓ := hi

/-! ## Elementary geometry of expanded arcs -/

/-- A point within circle-distance `η` of an arc lies in the arc expanded by
`η` at each end. -/
lemma mem_expanded_arc_of_integerDistance_lt
    {a x y : Circle} {ℓ η : ℝ} (hη : 0 < η) (hsize : ℓ + 2 * η ≤ 1)
    (hx : x ∈ arc a ℓ) (hxy : integerDistance (x - y) < η) :
    y ∈ arc (a - (η : Circle)) (ℓ + 2 * η) := by
  let r : ℝ := ((AddCircle.equivIco 1 0) (x - a) : ℝ)
  let e : ℝ := ((AddCircle.equivIco 1 (-(1 / 2 : ℝ))) (y - x) : ℝ)
  have hrmem : r ∈ Ico (0 : ℝ) 1 := by
    simpa [r] using (AddCircle.equivIco 1 0 (x - a)).property
  have hemem : e ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    have hp := (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) (y - x)).property
    dsimp [e]
    constructor
    · exact hp.1
    · linarith [hp.2]
  have hrcoe : (r : Circle) = x - a := by
    simpa [r] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
      (y := x - a))
  have hecoe : (e : Circle) = y - x := by
    simpa [e] using (AddCircle.coe_equivIco (p := (1 : ℝ))
      (a := (-(1 / 2 : ℝ))) (y := y - x))
  have heabs : |e| = integerDistance (y - x) := by
    symm
    rw [integerDistance, ← hecoe]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 <| by
      rw [abs_le]
      constructor <;> linarith [hemem.1, hemem.2]
  have hdist : integerDistance (y - x) < η := by
    calc
      integerDistance (y - x) = integerDistance (-(y - x)) :=
        (integerDistance_neg _).symm
      _ = integerDistance (x - y) := by rw [neg_sub]
      _ < η := hxy
  have he : -η < e ∧ e < η := by
    rw [← abs_lt, heabs]
    exact hdist
  have hrlt : r < ℓ := by
    simpa only [arc, r, mem_setOf_eq] using hx
  let s : ℝ := η + r + e
  have hspos : 0 < s := by dsimp [s]; linarith [hrmem.1, he.1]
  have hsupper : s < ℓ + 2 * η := by dsimp [s]; linarith [hrlt, he.2]
  have hsIco : s ∈ Ico (0 : ℝ) 1 := ⟨hspos.le, hsupper.trans_le hsize⟩
  have hscoe : (s : Circle) = y - (a - (η : Circle)) := by
    dsimp [s]
    push_cast
    rw [hrcoe, hecoe]
    abel
  change ((AddCircle.equivIco 1 0) (y - (a - (η : Circle))) : ℝ) <
    ℓ + 2 * η
  rw [← hscoe, AddCircle.equivIco_coe_eq (by simpa only [zero_add] using hsIco)]
  exact hsupper

/-! ## Coefficient and integral bounds -/

private lemma fejer_fiber_card_le (N : ℕ) (h : ℤ) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      fejerPairFrequency p = h).card ≤ N := by
  let s := Finset.univ.filter fun p : Fin N × Fin N => fejerPairFrequency p = h
  calc
    s.card ≤ (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq hpq
        apply Prod.ext hpq
        apply Fin.ext
        have hpf := (Finset.mem_filter.mp hp).2
        have hqf := (Finset.mem_filter.mp hq).2
        unfold fejerPairFrequency at hpf hqf
        omega
    _ = N := by simp

lemma fejerCoefficient_nonneg (N : ℕ) (h : ℤ) :
    0 ≤ fejerCoefficient N h := by
  unfold fejerCoefficient
  positivity

lemma fejerCoefficient_le_one {N : ℕ} (hN : 0 < N) (h : ℤ) :
    fejerCoefficient N h ≤ 1 := by
  unfold fejerCoefficient
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast fejer_fiber_card_le N h

/-- For a function bounded by one, every coefficient of its Fejer smoothing
has norm at most one. -/
lemma norm_fejerSmoothCoefficient_le_one {N : ℕ} (hN : 0 < N)
    {f : Circle → ℝ} (_hf : Integrable f circleHaar)
    (hfbd : ∀ x, |f x| ≤ 1) (h : ℤ) :
    ‖fejerSmoothCoefficient N f h‖ ≤ 1 := by
  unfold fejerSmoothCoefficient
  rw [norm_mul]
  have hcoef : ‖(fejerCoefficient N h : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerCoefficient_nonneg N h)]
    exact fejerCoefficient_le_one hN h
  have hint : ‖∫ y : Circle,
      (f y : ℂ) * character ((-h) • y) ∂circleHaar‖ ≤ 1 := by
    have hi := norm_integral_le_of_norm_le_const
      (μ := circleHaar) (f := fun y : Circle =>
        (f y : ℂ) * character ((-h) • y))
      (ae_of_all _ fun y => by
        rw [norm_mul, norm_character, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        exact hfbd y)
    simpa using hi
  nlinarith [norm_nonneg ((fejerCoefficient N h : ℂ)),
    norm_nonneg (∫ y : Circle,
      (f y : ℂ) * character ((-h) • y) ∂circleHaar)]

lemma continuous_fejerPolynomial (N : ℕ) : Continuous (fejerPolynomial N) := by
  rw [show fejerPolynomial N = fun x =>
      ‖geometricCharacterSum N x‖ ^ 2 / N by
    funext x
    exact fejerPolynomial_eq N x]
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  unfold geometricCharacterSum
  apply continuous_finset_sum
  intro n hn
  unfold character
  exact continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (continuous_nsmul n))

lemma norm_geometricCharacterSum_le_card (N : ℕ) (x : Circle) :
    ‖geometricCharacterSum N x‖ ≤ N := by
  unfold geometricCharacterSum
  calc
    ‖∑ n ∈ range N, character (n • x)‖ ≤
        ∑ n ∈ range N, ‖character (n • x)‖ := norm_sum_le _ _
    _ = N := by simp

lemma fejerPolynomial_le_card (N : ℕ) (x : Circle) :
    fejerPolynomial N x ≤ N := by
  rw [fejerPolynomial_eq]
  by_cases hN : N = 0
  · simp [hN]
  · rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))]
    have h := norm_geometricCharacterSum_le_card N x
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h

lemma integrable_fejerPolynomial_comp_sub (N : ℕ) (x : Circle) :
    Integrable (fun y : Circle => fejerPolynomial N (x-y)) circleHaar := by
  apply Integrable.of_bound
    ((continuous_fejerPolynomial N).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable N
  exact ae_of_all _ fun y => by
    change |fejerPolynomial N (x-y)| ≤ (N : ℝ)
    rw [abs_of_nonneg (fejerPolynomial_nonneg N _)]
    exact fejerPolynomial_le_card N _

lemma fejerPolynomial_neg (N : ℕ) (x : Circle) :
    fejerPolynomial N (-x) = fejerPolynomial N x := by
  rw [fejerPolynomial_eq, fejerPolynomial_eq]
  congr 2
  unfold geometricCharacterSum
  calc
    ‖∑ n ∈ range N, character (n • -x)‖ =
        ‖star (∑ n ∈ range N, character (n • x))‖ := by
      congr 1
      change _ = (starRingEnd ℂ) _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [smul_neg, character_neg]
      rfl
    _ = _ := Complex.norm_conj _

lemma integral_fejerPolynomial_comp_sub {N : ℕ} (hN : 0 < N) (x : Circle) :
    ∫ y : Circle, fejerPolynomial N (x-y) ∂circleHaar = 1 := by
  calc
    ∫ y : Circle, fejerPolynomial N (x-y) ∂circleHaar =
        ∫ y : Circle, fejerPolynomial N (y-x) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show x-y = -(y-x) by abel, fejerPolynomial_neg]
    _ = ∫ y : Circle, fejerPolynomial N y ∂circleHaar := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fejerPolynomial N) (-x)
    _ = 1 := integral_fejerPolynomial hN

/-- The real indicator of a measurable set. -/
def realSetIndicator (E : Set Circle) (x : Circle) : ℝ := by
  classical
  exact if x ∈ E then 1 else 0

lemma integrable_realSetIndicator {E : Set Circle} (hE : MeasurableSet E) :
    Integrable (realSetIndicator E) circleHaar := by
  have hi : Integrable ((E.indicator fun _ : Circle => (1 : ℝ))) circleHaar :=
    (integrable_const (1 : ℝ)).indicator hE
  apply hi.congr
  filter_upwards [] with x
  simp [realSetIndicator, Set.indicator]

/-- If every point outside `E` is at least `η` from `x`, smoothing the
indicator of `E` is at least one minus the Fejer tail. -/
lemma fejerSmooth_indicator_upper {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {E : Set Circle} (hE : MeasurableSet E)
    {x : Circle} (hfar : ∀ y, y ∉ E → η ≤ integerDistance (x-y)) :
    1 ≤ fejerSmooth N (realSetIndicator E) x + 1 / (4*N*η^2) := by
  let K : Circle → ℝ := fun y => fejerPolynomial N (x-y)
  let f : Circle → ℝ := fun y => realSetIndicator E y * K y
  let t : ℝ := 1 / (4*N*η^2)
  have hK : Integrable K circleHaar := integrable_fejerPolynomial_comp_sub N x
  have hf : Integrable f circleHaar := by
    have hi := hK.indicator hE
    apply hi.congr
    filter_upwards [] with y
    simp [f, K, realSetIndicator, Set.indicator]
  have ht : Integrable (fun y : Circle => t) circleHaar := integrable_const t
  have hmono : K ≤ fun y => f y + t := by
    intro y
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    by_cases hy : y ∈ E
    · dsimp [f]
      simp [realSetIndicator, hy]
      exact ht0
    · dsimp [f]
      simp only [realSetIndicator, hy, if_false, zero_mul, zero_add]
      exact fejerPolynomial_le_of_distance hN hη (hfar y hy)
  have hi := integral_mono hK (hf.add ht) hmono
  rw [integral_fejerPolynomial_comp_sub hN x] at hi
  change 1 ≤ ∫ y : Circle, f y + (fun _ : Circle => t) y ∂circleHaar at hi
  rw [integral_add hf ht, integral_const] at hi
  simpa [fejerSmooth, f, K, t] using hi

/-- If every point of `E` is at least `η` from `x`, smoothing the indicator
of `E` is at most the Fejer tail. -/
lemma fejerSmooth_indicator_lower {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {E : Set Circle} (hE : MeasurableSet E)
    {x : Circle} (hfar : ∀ y, y ∈ E → η ≤ integerDistance (x-y)) :
    fejerSmooth N (realSetIndicator E) x ≤ 1 / (4*N*η^2) := by
  let K : Circle → ℝ := fun y => fejerPolynomial N (x-y)
  let f : Circle → ℝ := fun y => realSetIndicator E y * K y
  let t : ℝ := 1 / (4*N*η^2)
  have hK : Integrable K circleHaar := integrable_fejerPolynomial_comp_sub N x
  have hf : Integrable f circleHaar := by
    have hi := hK.indicator hE
    apply hi.congr
    filter_upwards [] with y
    simp [f, K, realSetIndicator, Set.indicator]
  have ht : Integrable (fun _ : Circle => t) circleHaar := integrable_const t
  have hmono : f ≤ fun _ => t := by
    intro y
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    by_cases hy : y ∈ E
    · dsimp [f]
      simp only [realSetIndicator, hy, if_true, one_mul]
      exact fejerPolynomial_le_of_distance hN hη (hfar y hy)
    · dsimp [f]
      simp [realSetIndicator, hy]
      exact ht0
  have hi := integral_mono hf ht hmono
  rw [integral_const] at hi
  simpa [fejerSmooth, f, K, t] using hi

/-! ## Removing the constant Fourier coefficient -/

/-- The nonzero support of the Fejer polynomial. -/
def fejerNonzeroFrequencies (N : ℕ) : Finset ℤ :=
  (fejerFrequencies N).erase 0

lemma fejerNonzeroFrequencies_ne_zero {N : ℕ} {h : ℤ}
    (hh : h ∈ fejerNonzeroFrequencies N) : h ≠ 0 := by
  exact (Finset.mem_erase.mp hh).1

lemma abs_lt_card_of_mem_fejerNonzeroFrequencies {N : ℕ} {h : ℤ}
    (hh : h ∈ fejerNonzeroFrequencies N) : |(h : ℝ)| < N := by
  have hfull := (Finset.mem_erase.mp hh).2
  rcases Finset.mem_image.mp hfull with ⟨p, hp, rfl⟩
  unfold fejerPairFrequency
  have hj := p.1.isLt
  have hk := p.2.isLt
  rw [Int.cast_sub]
  rw [abs_lt]
  have hjr : (((p.1.val : ℤ) : ℝ)) < N := by exact_mod_cast hj
  have hkr : (((p.2.val : ℤ) : ℝ)) < N := by exact_mod_cast hk
  have hj0 : 0 ≤ (((p.1.val : ℤ) : ℝ)) := by positivity
  have hk0 : 0 ≤ (((p.2.val : ℤ) : ℝ)) := by positivity
  constructor <;> linarith

lemma card_fejerNonzeroFrequencies_le_sq (N : ℕ) :
    (fejerNonzeroFrequencies N).card ≤ N^2 := by
  calc
    _ ≤ (fejerFrequencies N).card := Finset.card_erase_le
    _ ≤ (Finset.univ : Finset (Fin N × Fin N)).card := by
      unfold fejerFrequencies
      exact Finset.card_image_le
    _ = N^2 := by simp [pow_two]

lemma zero_mem_fejerFrequencies {N : ℕ} (hN : 0 < N) :
    0 ∈ fejerFrequencies N := by
  unfold fejerFrequencies
  apply Finset.mem_image.2
  exact ⟨(⟨0,hN⟩,⟨0,hN⟩), Finset.mem_univ _,
    by simp [fejerPairFrequency]⟩

lemma fejerCoefficient_zero {N : ℕ} (hN : 0 < N) :
    fejerCoefficient N 0 = 1 := by
  unfold fejerCoefficient fejerPairFrequency
  have hdiag : (Finset.univ.filter fun p : Fin N × Fin N =>
      (p.1.val : ℤ) - p.2.val = 0).card = N := by
    rw [show (Finset.univ.filter fun p : Fin N × Fin N =>
        (p.1.val : ℤ) - p.2.val = 0) =
        Finset.univ.image (fun j : Fin N => (j,j)) by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hp
        have heq : p.1 = p.2 := by
          apply Fin.ext
          omega
        exact ⟨p.1, by ext <;> simp [heq]⟩
      · rintro ⟨j,-,rfl⟩
        simp]
    calc
      (Finset.univ.image (fun j : Fin N => (j,j))).card =
          (Finset.univ : Finset (Fin N)).card :=
        Finset.card_image_of_injective _ fun i j h => by
          simpa using congrArg Prod.fst h
      _ = N := by simp
  rw [hdiag, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]

lemma fejerSmoothCoefficient_zero {N : ℕ} (hN : 0 < N)
    {f : Circle → ℝ} :
    fejerSmoothCoefficient N f 0 =
      ((∫ x : Circle, f x ∂circleHaar : ℝ) : ℂ) := by
  unfold fejerSmoothCoefficient
  rw [fejerCoefficient_zero hN]
  simp only [neg_zero, zero_smul, character_zero, mul_one]
  norm_num
  exact integral_ofReal

/-- The convolution is its mean plus a trigonometric polynomial supported on
nonzero frequencies. -/
lemma fejerSmooth_eq_const_add_tail {N : ℕ} (hN : 0 < N)
    {f : Circle → ℝ} (hf : Integrable f circleHaar) (x : Circle) :
    fejerSmooth N f x = (∫ y : Circle, f y ∂circleHaar) +
      realTrigTail (fejerNonzeroFrequencies N)
        (fejerSmoothCoefficient N f) x := by
  rw [fejerSmooth_eq_fullFourier N hf]
  unfold realTrigTail fejerNonzeroFrequencies
  rw [← Finset.sum_erase_add (fejerFrequencies N)
    (fun h => fejerSmoothCoefficient N f h * character (h • x))
    (zero_mem_fejerFrequencies hN)]
  rw [fejerSmoothCoefficient_zero hN]
  norm_num
  ring

/-! ## Pointwise arc sandwich -/

private lemma fejerSmooth_realSetIndicator_nonneg (N : ℕ)
    (E : Set Circle) (x : Circle) :
    0 ≤ fejerSmooth N (realSetIndicator E) x := by
  unfold fejerSmooth
  apply integral_nonneg
  intro y
  exact mul_nonneg (by unfold realSetIndicator; split_ifs <;> positivity)
    (fejerPolynomial_nonneg N (x - y))

/-- The smoothing of the expanded arc, plus the Fejer tail, is a pointwise
upper bound for the original arc indicator. -/
lemma arcIndicator_le_expanded_fejerSmooth {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {a : Circle} {ℓ : ℝ}
    (hsize : ℓ + 2 * η ≤ 1) (x : Circle) :
    arcIndicator a ℓ x ≤
      fejerSmooth N
          (realSetIndicator (arc (a - (η : Circle)) (ℓ + 2 * η))) x +
        1 / (4 * N * η ^ 2) := by
  by_cases hx : x ∈ arc a ℓ
  · have hix : arcIndicator a ℓ x = 1 := by simp [arcIndicator, hx]
    rw [hix]
    apply fejerSmooth_indicator_upper hN hη
      (measurableSet_arc (a - (η : Circle)) (ℓ + 2 * η))
    intro y hy
    by_contra hdist
    exact hy (mem_expanded_arc_of_integerDistance_lt hη hsize hx
      (lt_of_not_ge hdist))
  · have hix : arcIndicator a ℓ x = 0 := by simp [arcIndicator, hx]
    rw [hix]
    have hs := fejerSmooth_realSetIndicator_nonneg N
      (arc (a - (η : Circle)) (ℓ + 2 * η)) x
    positivity

/-- The smoothing of the contracted arc, minus the Fejer tail, is a
pointwise lower bound for the original arc indicator. -/
lemma contracted_fejerSmooth_le_arcIndicator {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {a : Circle} {ℓ : ℝ}
    (hℓ : ℓ ≤ 1) (x : Circle) :
    fejerSmooth N
        (realSetIndicator (arc (a + (η : Circle)) (ℓ - 2 * η))) x -
        1 / (4 * N * η ^ 2) ≤ arcIndicator a ℓ x := by
  by_cases hx : x ∈ arc a ℓ
  · have hix : arcIndicator a ℓ x = 1 := by simp [arcIndicator, hx]
    rw [hix]
    have hs : fejerSmooth N
        (realSetIndicator (arc (a + (η : Circle)) (ℓ - 2 * η))) x ≤ 1 := by
      unfold fejerSmooth
      calc
        (∫ y : Circle,
            realSetIndicator (arc (a + (η : Circle)) (ℓ - 2 * η)) y *
              fejerPolynomial N (x - y) ∂circleHaar) ≤
            ∫ y : Circle, fejerPolynomial N (x - y) ∂circleHaar := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun y => mul_nonneg
              (by unfold realSetIndicator; split_ifs <;> positivity)
              (fejerPolynomial_nonneg N (x - y))
          · exact integrable_fejerPolynomial_comp_sub N x
          · exact ae_of_all _ fun y => by
              have hK := fejerPolynomial_nonneg N (x - y)
              by_cases hy : y ∈ arc (a + (η : Circle)) (ℓ - 2 * η)
              · simp [realSetIndicator, hy]
              · simp [realSetIndicator, hy, hK]
        _ = 1 := integral_fejerPolynomial_comp_sub hN x
    have ht : 0 ≤ 1 / (4 * (N : ℝ) * η ^ 2) := by positivity
    linarith
  · have hs := fejerSmooth_indicator_lower hN hη
      (measurableSet_arc (a + (η : Circle)) (ℓ - 2 * η)) (x := x)
    have hfar : ∀ y, y ∈ arc (a + (η : Circle)) (ℓ - 2 * η) →
        η ≤ integerDistance (x - y) := by
      intro y hy
      by_contra hdist
      apply hx
      have hdist' : integerDistance (y - x) < η := by
        rw [show y - x = -(x-y) by abel, integerDistance_neg]
        exact lt_of_not_ge hdist
      have hsize : (ℓ - 2 * η) + 2 * η ≤ 1 := by linarith
      have hm := mem_expanded_arc_of_integerDistance_lt hη (x := y) (y := x)
        (a := a + (η : Circle)) (ℓ := ℓ - 2 * η) hsize hy hdist'
      simpa only [sub_add_cancel, add_sub_cancel_right] using hm
    have := hs hfar
    have hix : arcIndicator a ℓ x = 0 := by simp [arcIndicator, hx]
    rw [hix]
    linarith

/-! ## The unconditional discrepancy estimate -/

lemma realSetIndicator_arc (a : Circle) (ℓ : ℝ) :
    realSetIndicator (arc a ℓ) = arcIndicator a ℓ := by
  funext x
  simp [realSetIndicator, arcIndicator]

lemma integrable_realSetIndicator_arc (a : Circle) (ℓ : ℝ) :
    Integrable (realSetIndicator (arc a ℓ)) circleHaar := by
  rw [realSetIndicator_arc]
  exact integrable_arcIndicator a ℓ

lemma integral_realSetIndicator_arc (a : Circle) {ℓ : ℝ}
    (h0 : 0 ≤ ℓ) (h1 : ℓ ≤ 1) :
    ∫ x : Circle, realSetIndicator (arc a ℓ) x ∂circleHaar = ℓ := by
  rw [realSetIndicator_arc]
  exact integral_arcIndicator a h0 h1

lemma exists_fejer_upper_sandwich {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {a : Circle} {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (_hℓ1 : ℓ ≤ 1) :
    ∃ b S c,
      b - ℓ ≤ 2*η + 1/(4*N*η^2) ∧
      (∀ x, arcIndicator a ℓ x ≤ b + realTrigTail S c x) ∧
      S ⊆ fejerNonzeroFrequencies N ∧
      (∀ h ∈ S, ‖c h‖ ≤ 1) := by
  by_cases hsize : ℓ + 2*η ≤ 1
  · let f := realSetIndicator (arc (a-(η:Circle)) (ℓ+2*η))
    let c := fejerSmoothCoefficient N f
    refine ⟨ℓ + 2*η + 1/(4*N*η^2), fejerNonzeroFrequencies N, c,
      by ring_nf; rfl, ?_, Finset.Subset.rfl, ?_⟩
    · intro x
      have hp := arcIndicator_le_expanded_fejerSmooth hN hη
        (a := a) (ℓ := ℓ) hsize x
      have hf : Integrable f circleHaar := by
        dsimp [f]
        exact integrable_realSetIndicator_arc _ _
      rw [fejerSmooth_eq_const_add_tail hN hf] at hp
      have hi : (∫ y : Circle, f y ∂circleHaar) = ℓ+2*η := by
        dsimp [f]
        exact integral_realSetIndicator_arc _ (by linarith) hsize
      rw [hi] at hp
      dsimp [c]
      linarith
    · intro h hh
      dsimp [c, f]
      apply norm_fejerSmoothCoefficient_le_one hN
        (integrable_realSetIndicator_arc _ _)
      intro x
      by_cases hx : x ∈ arc (a - (η : Circle)) (ℓ + 2 * η) <;>
        simp [realSetIndicator, hx]
  · refine ⟨1, ∅, fun _ => 0, ?_, ?_, by simp, by simp⟩
    · have ht : 0 ≤ 1/(4*(N:ℝ)*η^2) := by positivity
      have hs : 1 < ℓ + 2*η := lt_of_not_ge hsize
      linarith
    · intro x
      simp only [realTrigTail, Finset.sum_empty, Complex.zero_re, add_zero]
      unfold arcIndicator
      split_ifs <;> norm_num

lemma exists_fejer_lower_sandwich {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {a : Circle} {ℓ : ℝ}
    (_hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    ∃ b S c,
      ℓ - b ≤ 2*η + 1/(4*N*η^2) ∧
      (∀ x, b + realTrigTail S c x ≤ arcIndicator a ℓ x) ∧
      S ⊆ fejerNonzeroFrequencies N ∧
      (∀ h ∈ S, ‖c h‖ ≤ 1) := by
  by_cases hsize : 2*η ≤ ℓ
  · let f := realSetIndicator (arc (a+(η:Circle)) (ℓ-2*η))
    let c := fejerSmoothCoefficient N f
    refine ⟨ℓ - 2*η - 1/(4*N*η^2), fejerNonzeroFrequencies N, c,
      by ring_nf; rfl, ?_, Finset.Subset.rfl, ?_⟩
    · intro x
      have hp := contracted_fejerSmooth_le_arcIndicator hN hη
        (a := a) (ℓ := ℓ) hℓ1 x
      have hf : Integrable f circleHaar := by
        dsimp [f]
        exact integrable_realSetIndicator_arc _ _
      rw [fejerSmooth_eq_const_add_tail hN hf] at hp
      have hi : (∫ y : Circle, f y ∂circleHaar) = ℓ-2*η := by
        dsimp [f]
        apply integral_realSetIndicator_arc
        · linarith
        · linarith
      rw [hi] at hp
      dsimp [c]
      linarith
    · intro h hh
      dsimp [c, f]
      apply norm_fejerSmoothCoefficient_le_one hN
        (integrable_realSetIndicator_arc _ _)
      intro x
      by_cases hx : x ∈ arc (a + (η : Circle)) (ℓ - 2 * η) <;>
        simp [realSetIndicator, hx]
  · refine ⟨0, ∅, fun _ => 0, ?_, ?_, by simp, by simp⟩
    · have ht : 0 ≤ 1/(4*(N:ℝ)*η^2) := by positivity
      have hs : ℓ < 2*η := lt_of_not_ge hsize
      linarith
    · intro x
      simp only [realTrigTail, Finset.sum_empty, Complex.zero_re, add_zero]
      unfold arcIndicator
      split_ifs <;> norm_num

lemma frequencyCost_le_normalizedCharacterSum {F : Finset Circle}
    (hF : F.Nonempty) (c : ℤ → ℂ) (h : ℤ) (hc : ‖c h‖ ≤ 1) :
    frequencyCost F c h ≤ normalizedCharacterSum F h := by
  unfold frequencyCost normalizedCharacterSum
  gcongr
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hc (norm_nonneg (∑ x ∈ F, character (h • x)))

/-- A weak but fully quantitative Fejer form of the one-dimensional
Erdos--Turan inequality.  Its coefficients are merely bounded by one; this is
sufficient for the high-dimensional orbit construction used here. -/
theorem abs_arcMass_sub_le_fejer {F : Finset Circle} (hF : F.Nonempty)
    {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    (a : Circle) {ℓ : ℝ} (hℓ : ℓ ∈ Icc (0:ℝ) 1) :
    |arcMass F a ℓ - ℓ| ≤
      2*η + 1/(4*N*η^2) +
        2 * ∑ h ∈ fejerNonzeroFrequencies N,
          normalizedCharacterSum F h := by
  obtain ⟨bp, Sp, cp, hbp, hup, hSp, hcp⟩ :=
    exists_fejer_upper_sandwich hN hη hℓ.1 hℓ.2
  obtain ⟨bm, Sm, cm, hbm, hlo, hSm, hcm⟩ :=
    exists_fejer_lower_sandwich hN hη hℓ.1 hℓ.2
  have hdelta : 0 ≤ 2*η + 1/(4*(N:ℝ)*η^2) := by positivity
  have hmain := abs_arcMass_sub_le_of_fourier_sandwich hF a ℓ
    (2*η + 1/(4*N*η^2)) bp bm Sp Sm cp cm
    hdelta hbp hbm hup hlo
  have hp : ∑ h ∈ Sp, frequencyCost F cp h ≤
      ∑ h ∈ fejerNonzeroFrequencies N, normalizedCharacterSum F h := by
    calc
      _ ≤ ∑ h ∈ Sp, normalizedCharacterSum F h := by
        gcongr with h hh
        exact frequencyCost_le_normalizedCharacterSum hF cp h (hcp h hh)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSp
        (fun h _ _ => normalizedCharacterSum_nonneg F h)
  have hm : ∑ h ∈ Sm, frequencyCost F cm h ≤
      ∑ h ∈ fejerNonzeroFrequencies N, normalizedCharacterSum F h := by
    calc
      _ ≤ ∑ h ∈ Sm, normalizedCharacterSum F h := by
        gcongr with h hh
        exact frequencyCost_le_normalizedCharacterSum hF cm h (hcm h hh)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSm
        (fun h _ _ => normalizedCharacterSum_nonneg F h)
  linarith

/-- Uniform interval discrepancy bound obtained from the finite Fejer
sandwich. -/
theorem intervalDiscrepancy_le_fejer (F : Finset Circle) (hF : F.Nonempty)
    {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    intervalDiscrepancy F ≤
      2*η + 1/(4*N*η^2) +
        2 * ∑ h ∈ fejerNonzeroFrequencies N,
          normalizedCharacterSum F h := by
  apply intervalDiscrepancy_le_of_arc_bound
  intro a ℓ hℓ
  exact abs_arcMass_sub_le_fejer hF hN hη a hℓ

/-! ## A power-saving orbit corollary -/

lemma abs_int_lt_fejer_order {M : ℕ} {h : ℤ}
    (hh : h ∈ fejerFrequencies M) : |(h : ℝ)| < M := by
  rw [fejerFrequencies, Finset.mem_image] at hh
  obtain ⟨p, -, rfl⟩ := hh
  unfold fejerPairFrequency
  rw [abs_lt]
  have hp1 : (p.1.val : ℤ) < (M : ℤ) := by exact_mod_cast p.1.isLt
  have hp2 : (p.2.val : ℤ) < (M : ℤ) := by exact_mod_cast p.2.isLt
  constructor
  · exact_mod_cast (show -(M : ℤ) < (p.1.val : ℤ) - p.2.val by omega)
  · exact_mod_cast (show (p.1.val : ℤ) - p.2.val < (M : ℤ) by omega)

lemma card_fejerNonzeroFrequencies_le (M : ℕ) :
    (fejerNonzeroFrequencies M).card ≤ M ^ 2 := by
  calc
    (fejerNonzeroFrequencies M).card ≤ (fejerFrequencies M).card := by
      exact Finset.card_erase_le
    _ ≤ (Finset.univ : Finset (Fin M × Fin M)).card := by
      unfold fejerFrequencies
      exact Finset.card_image_le
    _ = M ^ 2 := by simp [pow_two]

lemma distanceProduct_pos_of_uniform_lower {d : ℕ} {u : Fin d → Circle}
    {c : ℝ} (hc : 0 < c)
    (hu : ∀ h : ℤ, h ≠ 0 →
      c * |(h : ℝ)| ^ (-(3 : ℝ)) ≤ distanceProduct u h)
    {h : ℤ} (hh : h ≠ 0) :
    0 < distanceProduct u h := by
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  exact (mul_pos hc (Real.rpow_pos_of_pos habs _)).trans_le (hu h hh)

lemma normalizedCharacterSum_negativeOrbitFinset_le_cubic
    {u : Fin 32 → Circle} (hfree : FreeTuple.CircleFree u)
    {c : ℝ} (hc : 0 < c)
    (hu : ∀ h : ℤ, h ≠ 0 →
      c * |(h : ℝ)| ^ (-(3 : ℝ)) ≤ distanceProduct u h)
    {N : ℕ} (hN : 0 < N) (x : Circle) {h : ℤ} (hh : h ≠ 0) :
    normalizedCharacterSum (negativeOrbitFinset u N x) h ≤
      c⁻¹ * |(h : ℝ)| ^ 3 / (N : ℝ) ^ 32 := by
  have hprod : 0 < distanceProduct u h :=
    distanceProduct_pos_of_uniform_lower hc hu hh
  have hz : ∀ i : Fin 32, h • u i ≠ 0 := by
    intro i hi
    have hzero : distanceProduct u h = 0 := by
      unfold distanceProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi, integerDistance]
    linarith
  have hbase := normalizedCharacterSum_negativeOrbitFinset_le hfree hN x h hz
  have htwo : 1 ≤ (2 : ℝ) ^ (32 : ℕ) := one_le_pow₀ (by norm_num)
  have hfactor : 0 < (2 : ℝ) ^ (32 : ℕ) * distanceProduct u h :=
    mul_pos (by positivity) hprod
  have hinv_two : ((2 : ℝ) ^ (32 : ℕ) * distanceProduct u h)⁻¹ ≤
      (distanceProduct u h)⁻¹ := by
    exact (inv_le_inv₀ hfactor hprod).2 (by nlinarith)
  have habs : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
  have hlower := hu h hh
  have hrpow : |(h : ℝ)| ^ (-(3 : ℝ)) = (|(h : ℝ)| ^ 3)⁻¹ := by
    rw [show (-(3 : ℝ)) = -(3 : ℕ) by norm_num, Real.rpow_neg_natCast]
    simp
  rw [hrpow] at hlower
  have hcinv : (distanceProduct u h)⁻¹ ≤ c⁻¹ * |(h : ℝ)| ^ 3 := by
    have hcub : 0 < |(h : ℝ)| ^ 3 := by positivity
    have hcprod : 0 < c * (|(h : ℝ)| ^ 3)⁻¹ := mul_pos hc (inv_pos.mpr hcub)
    have hlower' : c * (|(h : ℝ)| ^ 3)⁻¹ ≤ distanceProduct u h := hlower
    have hi := (inv_le_inv₀ hprod hcprod).2 hlower'
    calc
      (distanceProduct u h)⁻¹ ≤ (c * (|(h : ℝ)| ^ 3)⁻¹)⁻¹ := hi
      _ = c⁻¹ * |(h : ℝ)| ^ 3 := by field_simp
  calc
    normalizedCharacterSum (negativeOrbitFinset u N x) h ≤
        (((2 : ℝ) ^ 32 * distanceProduct u h)⁻¹ / (N : ℝ) ^ 32) := hbase
    _ ≤ (distanceProduct u h)⁻¹ / (N : ℝ) ^ 32 := by gcongr
    _ ≤ c⁻¹ * |(h : ℝ)| ^ 3 / (N : ℝ) ^ 32 := by gcongr

lemma sum_normalizedCharacterSum_negativeOrbitFinset_le
    {u : Fin 32 → Circle} (hfree : FreeTuple.CircleFree u)
    {c : ℝ} (hc : 0 < c)
    (hu : ∀ h : ℤ, h ≠ 0 →
      c * |(h : ℝ)| ^ (-(3 : ℝ)) ≤ distanceProduct u h)
    {N : ℕ} (hN : 0 < N) (x : Circle) :
    (∑ h ∈ fejerNonzeroFrequencies (N ^ 6),
      normalizedCharacterSum (negativeOrbitFinset u N x) h) ≤
        c⁻¹ / (N : ℝ) ^ 2 := by
  let M : ℕ := N ^ 6
  have hM : 0 < M := by dsimp [M]; positivity
  have hterm : ∀ h ∈ fejerNonzeroFrequencies M,
      normalizedCharacterSum (negativeOrbitFinset u N x) h ≤
        c⁻¹ * (M : ℝ) ^ 3 / (N : ℝ) ^ 32 := by
    intro h hh
    have hh0 : h ≠ 0 := (Finset.mem_erase.mp hh).1
    have habs := abs_int_lt_fejer_order (Finset.mem_erase.mp hh).2
    have hcub : |(h : ℝ)| ^ 3 ≤ (M : ℝ) ^ 3 := by
      gcongr
    have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    calc
      normalizedCharacterSum (negativeOrbitFinset u N x) h ≤
          c⁻¹ * |(h : ℝ)| ^ 3 / (N : ℝ) ^ 32 :=
        normalizedCharacterSum_negativeOrbitFinset_le_cubic
          hfree hc hu hN x hh0
      _ ≤ c⁻¹ * (M : ℝ) ^ 3 / (N : ℝ) ^ 32 := by gcongr
  calc
    (∑ h ∈ fejerNonzeroFrequencies (N ^ 6),
        normalizedCharacterSum (negativeOrbitFinset u N x) h) =
        ∑ h ∈ fejerNonzeroFrequencies M,
          normalizedCharacterSum (negativeOrbitFinset u N x) h := by rfl
    _ ≤ ∑ _h ∈ fejerNonzeroFrequencies M,
          (c⁻¹ * (M : ℝ) ^ 3 / (N : ℝ) ^ 32) := by
      gcongr with h hh
      exact hterm h hh
    _ = (fejerNonzeroFrequencies M).card *
          (c⁻¹ * (M : ℝ) ^ 3 / (N : ℝ) ^ 32) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) ^ 2 *
          (c⁻¹ * (M : ℝ) ^ 3 / (N : ℝ) ^ 32) := by
      gcongr
      exact_mod_cast card_fejerNonzeroFrequencies_le M
    _ = c⁻¹ / (N : ℝ) ^ 2 := by
      dsimp [M]
      push_cast
      field_simp

theorem intervalDiscrepancy_negativeOrbitFinset_le_cubic
    {u : Fin 32 → Circle} (hfree : FreeTuple.CircleFree u)
    {c : ℝ} (hc : 0 < c)
    (hu : ∀ h : ℤ, h ≠ 0 →
      c * |(h : ℝ)| ^ (-(3 : ℝ)) ≤ distanceProduct u h)
    {N : ℕ} (hN : 0 < N) (x : Circle) :
    intervalDiscrepancy (negativeOrbitFinset u N x) ≤
      ((9 / 4 : ℝ) + 2 * c⁻¹) / (N : ℝ) ^ 2 := by
  have hF : (negativeOrbitFinset u N x).Nonempty := by
    rw [← Finset.card_pos, card_negativeOrbitFinset hfree]
    positivity
  let η : ℝ := 1 / (N : ℝ) ^ 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hM : 0 < N ^ 6 := by positivity
  have H := intervalDiscrepancy_le_fejer
    (negativeOrbitFinset u N x) hF hM hη
  have hsum := sum_normalizedCharacterSum_negativeOrbitFinset_le
    hfree hc hu hN x
  change intervalDiscrepancy (negativeOrbitFinset u N x) ≤
    ((9 / 4 : ℝ) + 2 * c⁻¹) / (N : ℝ) ^ 2
  dsimp [η] at H
  norm_cast at H
  have hNr : (0 : ℝ) < N := by positivity
  calc
    intervalDiscrepancy (negativeOrbitFinset u N x) ≤
        2 * (1 / (N : ℝ) ^ 2) +
          1 / (4 * (N : ℝ) ^ 6 * (1 / (N : ℝ) ^ 2) ^ 2) +
          2 * ∑ h ∈ fejerNonzeroFrequencies (N ^ 6),
            normalizedCharacterSum (negativeOrbitFinset u N x) h := by
      simpa using H
    _ ≤ 2 * (1 / (N : ℝ) ^ 2) +
          1 / (4 * (N : ℝ) ^ 6 * (1 / (N : ℝ) ^ 2) ^ 2) +
          2 * (c⁻¹ / (N : ℝ) ^ 2) := by gcongr
    _ = ((9 / 4 : ℝ) + 2 * c⁻¹) / (N : ℝ) ^ 2 := by
      field_simp
      ring

/-- The `h⁻³` Diophantine distance-product lower bound gives a uniform
quadratic discrepancy saving for the 32-dimensional orbit boxes. -/
theorem exists_uniform_intervalDiscrepancy_negativeOrbitFinset
    {u : Fin 32 → Circle} (hfree : FreeTuple.CircleFree u)
    {c : ℝ} (hc : 0 < c)
    (hu : ∀ h : ℤ, h ≠ 0 →
      c * |(h : ℝ)| ^ (-(3 : ℝ)) ≤ distanceProduct u h) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ x : Circle,
      intervalDiscrepancy (negativeOrbitFinset u N x) ≤
        K * (N : ℝ) ^ (-(2 : ℝ)) := by
  refine ⟨(9 / 4 : ℝ) + 2 * c⁻¹, by positivity, fun N hN x => ?_⟩
  have H := intervalDiscrepancy_negativeOrbitFinset_le_cubic hfree hc hu hN x
  rw [show (-(2 : ℝ)) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast]
  simp only [zpow_neg, zpow_ofNat]
  simpa [div_eq_mul_inv, mul_assoc] using H

end

end Erdos1124.OneDimensionalDiscrepancy
