/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos1124.FreeTuple

/-!
# One-dimensional discrepancy for the circle-squaring argument

This file develops the one-dimensional Fourier-algebra layer of the
Marks--Unger proof of Laczkovich's theorem.  We use the additive unit circle
`UnitAddCircle = ℝ / ℤ`, its normalized Haar measure, and Mathlib's Fourier
characters.

The central proved estimates are the exact finite geometric-series identity,
the character-denominator lower bound in terms of distance to the integers,
and the resulting `1 / (2 * ‖z‖)` estimate.  We also formalize the product
factorization of the exponential sum over a rectangular orbit box.
-/

open scoped BigOperators ComplexConjugate ENNReal Real

open Finset Function MeasureTheory Set

namespace Erdos1124.OneDimensionalDiscrepancy

noncomputable section

/-- The additive unit circle `ℝ / ℤ`. -/
abbrev Circle := UnitAddCircle

/-- Normalized Haar measure on the additive unit circle. -/
abbrev circleHaar : Measure Circle := AddCircle.haarAddCircle

theorem circleHaar_eq_volume : circleHaar = (volume : Measure Circle) := by
  symm
  simpa [circleHaar] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

/-- Distance to the nearest integer, expressed intrinsically on `ℝ / ℤ`. -/
def integerDistance (x : Circle) : ℝ := ‖x‖

theorem integerDistance_nonneg (x : Circle) : 0 ≤ integerDistance x := norm_nonneg x

theorem integerDistance_le_half (x : Circle) : integerDistance x ≤ 1 / 2 := by
  simpa [integerDistance] using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)

@[simp]
theorem integerDistance_zero : integerDistance (0 : Circle) = 0 := by
  simp [integerDistance]

@[simp]
theorem integerDistance_neg (x : Circle) : integerDistance (-x) = integerDistance x := by
  simp [integerDistance]

@[simp]
theorem integerDistance_coe (x : ℝ) :
    integerDistance (x : Circle) = |x - round x| := by
  simp [integerDistance, UnitAddCircle.norm_eq]

/-- The standard additive character `e(x) = exp(2πix)`. -/
def character (x : Circle) : ℂ := AddCircle.toCircle x

@[simp]
theorem character_zero : character 0 = 1 := by
  simp [character]

@[simp]
theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  unfold character
  rw [AddCircle.toCircle_add]
  rfl

@[simp]
theorem character_nsmul (n : ℕ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_nsmul]
  rfl

@[simp]
theorem character_zsmul (n : ℤ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_zsmul]
  rfl

@[simp]
theorem character_finset_sum {I : Type*} (s : Finset I) (f : I → Circle) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add]

@[simp]
theorem character_fintype_sum {I : Type*} [Fintype I] (f : I → Circle) :
    character (∑ i, f i) = ∏ i, character (f i) := by
  simpa using character_finset_sum Finset.univ f

@[simp]
theorem norm_character (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [character] using h
  · rintro rfl
    exact character_zero

/-- The exponential sum along a one-dimensional orbit segment. -/
def geometricCharacterSum (N : ℕ) (x : Circle) : ℂ :=
  ∑ n ∈ range N, character (n • x)

/-- Exact finite geometric-series identity for the standard circle character. -/
theorem geometricCharacterSum_mul (N : ℕ) (x : Circle) :
    geometricCharacterSum N x * (character x - 1) = character (N • x) - 1 := by
  simp only [geometricCharacterSum, character_nsmul]
  exact geom_sum_mul (character x) N

/-- The numerator in the geometric-series formula has norm at most two. -/
theorem norm_character_sub_one_le_two (x : Circle) : ‖character x - 1‖ ≤ 2 := by
  calc
    ‖character x - 1‖ ≤ ‖character x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

/-- Jordan's inequality, in the precise form used for a unit-circle character.

The norm on `UnitAddCircle` is distance to the nearest integer.  Hence the
chord joining `1` to `e(x)` has length at least four times that distance.
-/
theorem four_mul_integerDistance_le_norm_character_sub_one (x : Circle) :
    4 * integerDistance x ≤ ‖character x - 1‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hyabs : |y| ≤ 1 / 2 := by
    simpa [y] using abs_sub_round r
  have hypi_abs : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 * |y| ≤ |Real.sin (π * y)| := by
    have h := Real.mul_abs_le_abs_sin hypi_abs
    calc
      2 * |y| = (2 / π) * |π * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (π * y)| := h
  have hry : (r : Circle) = (y : Circle) := by
    simp [y, sub_eq_add_neg]
  have hcharacter :
      character (y : Circle) = Complex.exp (Complex.I * (2 * π * y : ℝ)) := by
    unfold character
    rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [integerDistance_coe]
  change 4 * |y| ≤ _
  rw [hry, hcharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  change 4 * |y| ≤ |2 * Real.sin ((2 * π * y) / 2)|
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    4 * |y| = 2 * (2 * |y|) := by ring
    _ ≤ 2 * |Real.sin (π * y)| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * |Real.sin ((2 * π * y) / 2)| := by ring_nf

/-- The geometric-character estimate in the form used by Marks--Unger.

It is stated multiplicatively, avoiding division by zero.  When `x ≠ 0`, it
immediately yields `‖∑ n < N, e(nx)‖ ≤ 1 / (2 * ‖x‖)`.
-/
theorem two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (N : ℕ) (x : Circle) :
    2 * integerDistance x * ‖geometricCharacterSum N x‖ ≤ 1 := by
  have hprod :
      ‖geometricCharacterSum N x‖ * ‖character x - 1‖ ≤ 2 := by
    rw [← norm_mul, geometricCharacterSum_mul]
    exact norm_character_sub_one_le_two _
  have hden := four_mul_integerDistance_le_norm_character_sub_one x
  have hnorm : 0 ≤ ‖geometricCharacterSum N x‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hden hnorm]

theorem norm_geometricCharacterSum_le (N : ℕ) {x : Circle} (hx : x ≠ 0) :
    ‖geometricCharacterSum N x‖ ≤ (2 * integerDistance x)⁻¹ := by
  have hdist : 0 < integerDistance x := by
    simpa [integerDistance, norm_pos_iff] using hx
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x

/-! ## Rectangular orbit boxes -/

/-- A `d`-dimensional rectangular orbit-box sum. -/
def orbitBoxCharacterSum {d : ℕ} (N : ℕ) (u : Fin d → Circle) (h : ℤ) : ℂ :=
  ∑ n : Fin d → Fin N, character (h • (∑ i, (n i : ℕ) • u i))

theorem geometricCharacterSum_eq_sum_fin (N : ℕ) (x : Circle) :
    geometricCharacterSum N x = ∑ n : Fin N, character ((n : ℕ) • x) := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [geometricCharacterSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mem_range.mp hn]

/-- The exponential sum on a rectangular orbit box factors into one-dimensional
geometric sums, one factor for every generator. -/
theorem orbitBoxCharacterSum_eq_prod {d : ℕ} (N : ℕ) (u : Fin d → Circle) (h : ℤ) :
    orbitBoxCharacterSum N u h =
      ∏ i : Fin d, geometricCharacterSum N (h • u i) := by
  rw [orbitBoxCharacterSum]
  simp_rw [geometricCharacterSum_eq_sum_fin]
  rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro n
  rw [← character_fintype_sum]
  congr 1
  simp only [smul_sum, nsmul_eq_mul, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  module

/-- Norm form of the orbit-box factorization. -/
theorem norm_orbitBoxCharacterSum_eq_prod {d : ℕ} (N : ℕ)
    (u : Fin d → Circle) (h : ℤ) :
    ‖orbitBoxCharacterSum N u h‖ =
      ∏ i : Fin d, ‖geometricCharacterSum N (h • u i)‖ := by
  rw [orbitBoxCharacterSum_eq_prod]
  exact norm_prod _ _

/-- Product geometric-sum estimate, still in denominator-free form. -/
theorem orbitBoxCharacterSum_product_bound {d : ℕ} (N : ℕ)
    (u : Fin d → Circle) (h : ℤ) :
    (∏ i : Fin d, 2 * integerDistance (h • u i)) *
        ‖orbitBoxCharacterSum N u h‖ ≤ 1 := by
  rw [norm_orbitBoxCharacterSum_eq_prod]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_one (fun i _ ↦ mul_nonneg
      (mul_nonneg (by norm_num) (integerDistance_nonneg _))
      (norm_nonneg (geometricCharacterSum N (h • u i))))
    (fun i _ ↦ two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N (h • u i))

/-! ## The fixed negative moment

The logarithmically weighted estimate in Marks--Unger can be replaced by the
standard fixed-negative-moment argument.  The exponent `-1/2` is integrable
on the circle.  Independence on a finite product then makes the product of
these moments integrable as well.
-/

/-- The `-1/2` moment of distance to the nearest integer.  Lean's real power
sets `0 ^ (-1/2)` to zero; this only changes the function at the Haar-null
point `0`.
-/
def negativeHalfMoment (x : Circle) : ℝ :=
  integerDistance x ^ (-(1 / 2 : ℝ))

theorem negativeHalfMoment_nonneg (x : Circle) : 0 ≤ negativeHalfMoment x := by
  exact Real.rpow_nonneg (integerDistance_nonneg x) _

private theorem integrableOn_abs_rpow_neg_half :
    IntegrableOn (fun x : ℝ ↦ |x| ^ (-(1 / 2 : ℝ)))
      (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  have hpow : -1 < -(1 / 2 : ℝ) := by norm_num
  have hp₀ : IntegrableOn (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) (Ioo 0 (1 / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1 / 2)).2 hpow
  have hp : IntegrableOn (fun x : ℝ ↦ |x| ^ (-(1 / 2 : ℝ)))
      (Ioc 0 (1 / 2)) := by
    have h := hp₀.congr_set_ae Ioo_ae_eq_Ioc.symm
    apply h.congr_fun
    · intro x hx
      simp only [abs_of_nonneg hx.1.le]
    · exact measurableSet_Ioc
  have hn : IntegrableOn (fun x : ℝ ↦ |x| ^ (-(1 / 2 : ℝ)))
      (Ioc (-(1 / 2 : ℝ)) 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Ioc, neg_zero, neg_neg]
    have hpi : IntegrableOn (fun x : ℝ ↦ |x| ^ (-(1 / 2 : ℝ)))
        (Ico 0 (1 / 2)) := hp.congr_set_ae Ico_ae_eq_Ioc
    simpa only [abs_neg] using hpi
  rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2), integrableOn_union]
  exact ⟨hn, hp⟩

theorem aestronglyMeasurable_negativeHalfMoment :
    AEStronglyMeasurable negativeHalfMoment circleHaar := by
  apply Measurable.aestronglyMeasurable
  apply measurable_of_measurable_on_compl_singleton (0 : Circle)
  have hc : ContinuousOn negativeHalfMoment {x : Circle | x ≠ 0} := by
    unfold negativeHalfMoment integerDistance
    exact
    continuous_norm.continuousOn.rpow_const fun x hx ↦ Or.inl <| norm_ne_zero_iff.mpr <| by
      simpa only [mem_setOf_eq] using hx
  exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable

theorem integrable_negativeHalfMoment :
    Integrable negativeHalfMoment circleHaar := by
  have hvol : (volume : Measure Circle) = circleHaar := by
    simpa [circleHaar] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hc : IntegrableOn (fun x : ℝ ↦ negativeHalfMoment (x : Circle))
      (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
    apply integrableOn_abs_rpow_neg_half.congr_fun
    · intro x hx
      change |x| ^ (-(1 / 2 : ℝ)) = ‖(x : Circle)‖ ^ (-(1 / 2 : ℝ))
      have hnorm : ‖(x : Circle)‖ = |x| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 <| by
          rw [abs_le]
          constructor <;> linarith [hx.1, hx.2]
      rw [hnorm]
    · exact measurableSet_Ioc
  have hc' : Integrable
      (negativeHalfMoment ∘ ((↑) : ℝ → Circle))
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) := by
    convert hc using 1 <;> norm_num [IntegrableOn, Function.comp_def]
  rw [← hvol]
  have hm : AEStronglyMeasurable negativeHalfMoment (volume : Measure Circle) := by
    rw [hvol]
    exact aestronglyMeasurable_negativeHalfMoment
  apply ((UnitAddCircle.measurePreserving_mk (-(1 / 2 : ℝ))).integrable_comp hm).mp
  simpa [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] using hc'

/-- Product Haar probability measure on `d` scalar generators. -/
def tupleHaar (d : ℕ) : Measure (Fin d → Circle) :=
  Measure.pi fun _ ↦ circleHaar

instance tupleHaar_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (tupleHaar d) := by
  unfold tupleHaar circleHaar
  infer_instance

theorem tupleHaar_eq_volume (d : ℕ) :
    tupleHaar d = (volume : Measure (Fin d → Circle)) := by
  rw [tupleHaar, circleHaar_eq_volume, ← MeasureTheory.volume_pi]

/-- Product of the `-1/2` moments over all scalar generators. -/
def tupleNegativeHalfMoment {d : ℕ} (u : Fin d → Circle) : ℝ :=
  ∏ i, negativeHalfMoment (u i)

theorem tupleNegativeHalfMoment_nonneg {d : ℕ} (u : Fin d → Circle) :
    0 ≤ tupleNegativeHalfMoment u := by
  exact Finset.prod_nonneg fun i _ ↦ negativeHalfMoment_nonneg (u i)

theorem integrable_tupleNegativeHalfMoment (d : ℕ) :
    Integrable (tupleNegativeHalfMoment (d := d)) (tupleHaar d) := by
  exact Integrable.fintype_prod fun _ ↦ integrable_negativeHalfMoment

/-- The product negative moment is exactly the negative half-power of the
product of the distances. -/
theorem tupleNegativeHalfMoment_eq_rpow_prod {d : ℕ} (u : Fin d → Circle) :
    tupleNegativeHalfMoment u =
      (∏ i, integerDistance (u i)) ^ (-(1 / 2 : ℝ)) := by
  change (∏ i, integerDistance (u i) ^ (-(1 / 2 : ℝ))) = _
  exact Real.finsetProd_rpow Finset.univ (fun i ↦ integerDistance (u i))
    (fun i _ ↦ integerDistance_nonneg _) _

/-- Multiplication by a nonzero integer preserves normalized Haar measure on
the circle.
-/
theorem measurePreserving_integerMultiple (h : ℤ) (hh : h ≠ 0) :
    MeasurePreserving (fun x : Circle ↦ h • x) circleHaar circleHaar := by
  exact Measure.measurePreserving_zsmul circleHaar hh

/-- Coordinatewise multiplication by a nonzero integer preserves product
Haar measure.
-/
theorem measurePreserving_tupleIntegerMultiple (d : ℕ) (h : ℤ) (hh : h ≠ 0) :
    MeasurePreserving (fun u : Fin d → Circle ↦ fun i ↦ h • u i)
      (tupleHaar d) (tupleHaar d) := by
  exact measurePreserving_pi _ _ fun _ ↦ measurePreserving_integerMultiple h hh

/-- The shifted product moment at Fourier frequency `h`. -/
def tupleNegativeHalfMomentAt {d : ℕ} (h : ℤ) (u : Fin d → Circle) : ℝ :=
  ∏ i, negativeHalfMoment (h • u i)

theorem integrable_tupleNegativeHalfMomentAt (d : ℕ) {h : ℤ} (hh : h ≠ 0) :
    Integrable (tupleNegativeHalfMomentAt (d := d) h) (tupleHaar d) := by
  have hm := (measurePreserving_tupleIntegerMultiple d h hh).integrable_comp_of_integrable
    (integrable_tupleNegativeHalfMoment d)
  change Integrable
    (fun u : Fin d → Circle ↦ ∏ i, negativeHalfMoment (h • u i)) (tupleHaar d)
  exact hm

theorem integral_tupleNegativeHalfMomentAt (d : ℕ) {h : ℤ} (hh : h ≠ 0) :
    (∫ u, tupleNegativeHalfMomentAt (d := d) h u ∂(tupleHaar d)) =
      ∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d) := by
  let f : (Fin d → Circle) → (Fin d → Circle) := fun u i ↦ h • u i
  have hp : MeasurePreserving f (tupleHaar d) (tupleHaar d) :=
    measurePreserving_tupleIntegerMultiple d h hh
  have hmeas : AEStronglyMeasurable (tupleNegativeHalfMoment (d := d))
      ((tupleHaar d).map f) := by
    rw [hp.map_eq]
    exact (integrable_tupleNegativeHalfMoment d).aestronglyMeasurable
  have hi := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at hi
  change (∫ u, tupleNegativeHalfMoment (f u) ∂(tupleHaar d)) =
    ∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)
  exact hi.symm

/-- Quantitative Markov inequality for the shifted product moment. -/
theorem mul_measureReal_tupleMoment_ge_le_integral (d : ℕ) {h : ℤ} (hh : h ≠ 0)
    (ε : ℝ) :
    ε * (tupleHaar d).real
        {u | ε ≤ tupleNegativeHalfMomentAt (d := d) h u} ≤
      ∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d) := by
  rw [← integral_tupleNegativeHalfMomentAt d hh]
  exact mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun u ↦ Finset.prod_nonneg fun i _ ↦ negativeHalfMoment_nonneg _)
    (integrable_tupleNegativeHalfMomentAt d hh) ε

/-! ## A Borel--Cantelli product-distance estimate -/

/-- The bad set at positive integer frequency `n + 1` for the fixed
negative-moment argument. -/
def momentBadSet (d n : ℕ) : Set (Fin d → Circle) :=
  {u | ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
    tupleNegativeHalfMomentAt (d := d) (n + 1 : ℕ) u}

theorem measure_momentBadSet_le (d n : ℕ) :
    (tupleHaar d) (momentBadSet d n) ≤ ENNReal.ofReal
      ((∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) *
        (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) := by
  have heps : 0 < (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by positivity
  have hm := mul_measureReal_tupleMoment_ge_le_integral d
    (h := (n + 1 : ℕ)) (by exact_mod_cast Nat.succ_ne_zero n)
    (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))
  have hreal : (tupleHaar d).real (momentBadSet d n) ≤
      (∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) /
        (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [le_div_iff₀ heps, mul_comm]
    simpa only [momentBadSet, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Int.ofNat_eq_natCast] using hm
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  calc
    (tupleHaar d).real (momentBadSet d n) ≤
        (∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) /
          (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := hreal
    _ = (∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) *
        (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [div_eq_mul_inv, Real.rpow_neg (by positivity)]

theorem tsum_measure_momentBadSet_ne_top (d : ℕ) :
    (∑' n, (tupleHaar d) (momentBadSet d n)) ≠ ∞ := by
  have hs0 : Summable (fun n : ℕ ↦
      (∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) *
        (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2 : ℝ)) < -1)).mul_left _
  have hs : Summable (fun n : ℕ ↦
      (∫ u, tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) *
        (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    exact (summable_nat_add_iff 1).2 hs0
  exact ne_top_of_le_ne_top hs.tsum_ofReal_ne_top <|
    ENNReal.tsum_le_tsum fun n ↦ measure_momentBadSet_le d n

theorem tupleNegativeHalfMomentAt_eq_rpow_prod {d : ℕ} (h : ℤ)
    (u : Fin d → Circle) :
    tupleNegativeHalfMomentAt h u =
      (∏ i, integerDistance (h • u i)) ^ (-(1 / 2 : ℝ)) := by
  change tupleNegativeHalfMoment (fun i ↦ h • u i) = _
  exact tupleNegativeHalfMoment_eq_rpow_prod _

/-- Normalized Haar measure of the origin in the unit circle is zero. -/
theorem circleHaar_singleton_zero : circleHaar ({0} : Set Circle) = 0 := by
  have hp := UnitAddCircle.measurePreserving_mk (-(1 / 2 : ℝ))
  have hcount : Set.Countable {x : ℝ | (x : Circle) = 0} := by
    apply (Set.countable_range (fun n : ℤ ↦ (n : ℝ))).mono
    intro x hx
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
    refine ⟨n, ?_⟩
    simpa using hn
  have hzero : (volume : Measure Circle) ({0} : Set Circle) = 0 := by
    rw [← hp.map_eq,
      Measure.map_apply hp.measurable (measurableSet_singleton (0 : Circle)),
      Measure.restrict_apply (hp.measurable (measurableSet_singleton (0 : Circle)))]
    have heq : ((fun x : ℝ ↦ (x : Circle)) ⁻¹' ({0} : Set Circle)) =
        {x : ℝ | (x : Circle) = 0} := by ext x; simp
    rw [heq]
    exact measure_mono_null inter_subset_left (hcount.measure_zero (volume : Measure ℝ))
  have hvol : (volume : Measure Circle) = circleHaar := by
    simpa [circleHaar] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol]
  exact hzero

theorem ae_all_positive_integerMultiple_coordinates_ne_zero (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), ∀ n : ℕ, ∀ i : Fin d,
      ((n + 1 : ℕ) : ℤ) • u i ≠ 0 := by
  rw [ae_all_iff]
  intro n
  have hz : ∀ᵐ v ∂(tupleHaar d), ∀ i : Fin d, v i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have he :=
      (measurePreserving_eval (fun _ : Fin d ↦ circleHaar) i).quasiMeasurePreserving.ae
        (compl_mem_ae_iff.2 circleHaar_singleton_zero :
          ∀ᵐ x ∂circleHaar, x ∉ ({0} : Set Circle))
    change ∀ᵐ v ∂Measure.pi (fun _ : Fin d ↦ circleHaar), v i ≠ 0
    filter_upwards [he] with v hv
    simpa only [Function.eval_apply, mem_singleton_iff] using hv
  exact (measurePreserving_tupleIntegerMultiple d ((n + 1 : ℕ) : ℤ)
    (by exact_mod_cast Nat.succ_ne_zero n)).quasiMeasurePreserving.ae hz

theorem productDistance_lower_of_moment_lt {d n : ℕ} {u : Fin d → Circle}
    (hz : ∀ i : Fin d, ((n + 1 : ℕ) : ℤ) • u i ≠ 0)
    (hm : tupleNegativeHalfMomentAt ((n + 1 : ℕ) : ℤ) u <
      (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) :
    (((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) <
      ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i) := by
  let p : ℝ := ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i)
  let t : ℝ := ((n + 1 : ℕ) : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hp : 0 < p := by
    apply Finset.prod_pos
    intro i hi
    simpa only [integerDistance, norm_pos_iff] using hz i
  rw [tupleNegativeHalfMomentAt_eq_rpow_prod] at hm
  change t ^ (-(3 : ℝ)) < p
  have hq : 0 < t ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos ht _
  apply (Real.rpow_lt_rpow_iff_of_neg hp hq (by norm_num : (-(1 / 2 : ℝ)) < 0)).mp
  rw [← Real.rpow_mul (le_of_lt ht)]
  norm_num
  exact hm

/-- Almost every tuple has the product Diophantine lower bound
`∏ᵢ ‖h uᵢ‖ > h⁻³` at all sufficiently large positive frequencies. -/
theorem ae_eventually_productDistance_lower (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), ∀ᶠ n : ℕ in Filter.atTop,
      (((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) <
        ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i) := by
  have hbc := ae_eventually_notMem (tsum_measure_momentBadSet_ne_top d)
  filter_upwards [hbc, ae_all_positive_integerMultiple_coordinates_ne_zero d]
    with u hmoment hz
  filter_upwards [hmoment] with n hn
  apply productDistance_lower_of_moment_lt (hz n)
  simpa only [momentBadSet, mem_ofPred_eq, not_le] using hn

theorem exists_eventually_productDistance_lower (d : ℕ) :
    ∃ u : Fin d → Circle, ∀ᶠ n : ℕ in Filter.atTop,
      (((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) <
        ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i) := by
  exact (ae_eventually_productDistance_lower d).exists

/-- A single tuple can be chosen both free and with the eventual
product-distance lower bound. -/
theorem exists_circleFree_eventually_productDistance_lower (d : ℕ) :
    ∃ u : Fin d → Circle, FreeTuple.CircleFree u ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) <
          ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i) := by
  have hp := ae_eventually_productDistance_lower d
  rw [tupleHaar_eq_volume] at hp
  have hboth : ∀ᵐ u : Fin d → Circle, FreeTuple.CircleFree u ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) <
          ∏ i, integerDistance (((n + 1 : ℕ) : ℤ) • u i) := by
    filter_upwards [FreeTuple.ae_free d, hp] with u hfree hprod
    exact ⟨hfree, hprod⟩
  exact hboth.exists

/-! ## Finite interval discrepancy -/

/-- A half-open interval (arc) on the additive unit circle.  Its starting
point is `a`, and its length is `ℓ ∈ [0,1]`.
-/
def arc (a : Circle) (ℓ : ℝ) : Set Circle :=
  {x | ((AddCircle.equivIco 1 0) (x - a) : ℝ) < ℓ}

/-- Normalized counting mass of a finite set on an arc. -/
def arcMass (F : Finset Circle) (a : Circle) (ℓ : ℝ) : ℝ :=
  by
    classical
    exact (F.filter (· ∈ arc a ℓ)).card / F.card

/-- Interval discrepancy of a nonempty finite subset of the unit circle.

The supremum is taken over all starting points and lengths in `[0,1]`; the
comparison mass is the arc length, which equals normalized Haar measure.
-/
def intervalDiscrepancy (F : Finset Circle) : ℝ :=
  sSup {r : ℝ | ∃ a : Circle, ∃ ℓ ∈ Set.Icc (0 : ℝ) 1,
    r = |arcMass F a ℓ - ℓ|}

theorem arcMass_nonneg (F : Finset Circle) (a : Circle) (ℓ : ℝ) :
    0 ≤ arcMass F a ℓ := by
  unfold arcMass
  positivity

theorem arcMass_le_one {F : Finset Circle} (hF : F.Nonempty) (a : Circle) (ℓ : ℝ) :
    arcMass F a ℓ ≤ 1 := by
  classical
  rw [arcMass, div_le_one (by exact_mod_cast hF.card_pos)]
  exact_mod_cast Finset.card_filter_le _ _

theorem intervalDiscrepancy_nonneg (F : Finset Circle) : 0 ≤ intervalDiscrepancy F := by
  apply Real.sSup_nonneg
  rintro r ⟨a, ℓ, hℓ, rfl⟩
  exact abs_nonneg _

theorem intervalDiscrepancy_le_one {F : Finset Circle} (hF : F.Nonempty) :
    intervalDiscrepancy F ≤ 1 := by
  apply csSup_le
  · exact ⟨|arcMass F 0 0 - 0|, 0, 0, by simp, rfl⟩
  rintro r ⟨a, ℓ, hℓ, rfl⟩
  rw [abs_le]
  constructor
  · linarith [arcMass_nonneg F a ℓ, hℓ.2]
  · linarith [arcMass_le_one hF a ℓ, hℓ.1]

/-! ## The finite Fourier-sandwich argument

This section isolates the purely algebraic part of the Erdős--Turán
inequality.  Once upper and lower trigonometric-polynomial approximations to
an arc indicator have been supplied, the following lemmas turn their Fourier
coefficient bounds into an interval-discrepancy estimate.
-/

/-- The empirical average of a real-valued function over a finite set. -/
def empiricalAverage (F : Finset Circle) (f : Circle → ℝ) : ℝ :=
  (∑ x ∈ F, f x) / F.card

/-- A real trigonometric tail with prescribed finite frequency support. -/
def realTrigTail (S : Finset ℤ) (c : ℤ → ℂ) (x : Circle) : ℝ :=
  (∑ h ∈ S, c h * character (h • x)).re

/-- The normalized exponential-sum contribution of one Fourier coefficient. -/
def frequencyCost (F : Finset Circle) (c : ℤ → ℂ) (h : ℤ) : ℝ :=
  ‖c h‖ * ‖∑ x ∈ F, character (h • x)‖ / F.card

/-- The normalized magnitude of the `h`-th exponential sum. -/
def normalizedCharacterSum (F : Finset Circle) (h : ℤ) : ℝ :=
  ‖∑ x ∈ F, character (h • x)‖ / F.card

theorem frequencyCost_nonneg (F : Finset Circle) (c : ℤ → ℂ) (h : ℤ) :
    0 ≤ frequencyCost F c h := by
  unfold frequencyCost
  positivity

theorem normalizedCharacterSum_nonneg (F : Finset Circle) (h : ℤ) :
    0 ≤ normalizedCharacterSum F h := by
  unfold normalizedCharacterSum
  positivity

/-! ### Concrete translated orbit finsets -/

/-- Point indexed by a negative rectangular orbit box, translated by `x`. -/
def negativeOrbitPoint {d N : ℕ} (u : Fin d → Circle) (x : Circle)
    (n : Fin d → Fin N) : Circle :=
  -(∑ i, (n i : ℕ) • u i) + x

/-- The finite set underlying a translated negative rectangular orbit box. -/
def negativeOrbitFinset {d : ℕ} (u : Fin d → Circle) (N : ℕ)
    (x : Circle) : Finset Circle := by
  classical
  exact Finset.univ.image (negativeOrbitPoint (N := N) u x)

theorem negativeOrbitPoint_injective {d N : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (x : Circle) :
    Function.Injective (negativeOrbitPoint (N := N) u x) := by
  intro n m hnm
  have hsum : (∑ i, (n i : ℕ) • u i) = ∑ i, (m i : ℕ) • u i := by
    apply neg_injective
    exact add_right_cancel hnm
  have hdisp : FreeTuple.circleDisplacement u (fun i ↦ ((n i : ℕ) : ℤ)) =
      FreeTuple.circleDisplacement u (fun i ↦ ((m i : ℕ) : ℤ)) := by
    simpa [FreeTuple.circleDisplacement] using hsum
  have hcoeff := hu hdisp
  funext i
  apply Fin.ext
  exact_mod_cast congrFun hcoeff i

theorem card_negativeOrbitFinset {d : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (N : ℕ) (x : Circle) :
    (negativeOrbitFinset u N x).card = N ^ d := by
  classical
  rw [negativeOrbitFinset,
    Finset.card_image_of_injective _ (negativeOrbitPoint_injective hu x),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem character_negativeOrbitPoint {d N : ℕ} (u : Fin d → Circle)
    (x : Circle) (n : Fin d → Fin N) (h : ℤ) :
    character (h • negativeOrbitPoint u x n) =
      star (character (h • (∑ i, (n i : ℕ) • u i))) * character (h • x) := by
  rw [negativeOrbitPoint, smul_add, smul_neg, character_add]
  congr 1
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

theorem norm_character_sum_negativeOrbitFinset {d : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (N : ℕ) (x : Circle) (h : ℤ) :
    ‖∑ y ∈ negativeOrbitFinset u N x, character (h • y)‖ =
      ‖orbitBoxCharacterSum N u h‖ := by
  classical
  rw [negativeOrbitFinset,
    Finset.sum_image (negativeOrbitPoint_injective hu x).injOn]
  simp_rw [character_negativeOrbitPoint]
  rw [← Finset.sum_mul, ← star_sum]
  rw [norm_mul, norm_star, norm_character, mul_one]
  rfl

/-- Exact bridge from the concrete free orbit finset to the indexed product
exponential sum. -/
theorem normalizedCharacterSum_negativeOrbitFinset {d : ℕ} {u : Fin d → Circle}
    (hu : FreeTuple.CircleFree u) (N : ℕ) (x : Circle) (h : ℤ) :
    normalizedCharacterSum (negativeOrbitFinset u N x) h =
      ‖orbitBoxCharacterSum N u h‖ / (N : ℝ) ^ d := by
  rw [normalizedCharacterSum, norm_character_sum_negativeOrbitFinset hu,
    card_negativeOrbitFinset hu]
  norm_cast

/-- Product of the circle distances occurring in the rectangular
geometric-sum estimate. -/
def distanceProduct {d : ℕ} (u : Fin d → Circle) (h : ℤ) : ℝ :=
  ∏ i, integerDistance (h • u i)

theorem prod_two_mul_integerDistance_eq {d : ℕ} (u : Fin d → Circle) (h : ℤ) :
    (∏ i : Fin d, 2 * integerDistance (h • u i)) =
      (2 : ℝ) ^ d * distanceProduct u h := by
  rw [distanceProduct, Finset.prod_mul_distrib]
  simp

/-- Concrete normalized Fourier bound for a free translated orbit finset. -/
theorem normalizedCharacterSum_negativeOrbitFinset_le {d : ℕ}
    {u : Fin d → Circle} (hu : FreeTuple.CircleFree u) {N : ℕ} (hN : 0 < N)
    (x : Circle) (h : ℤ) (hz : ∀ i : Fin d, h • u i ≠ 0) :
    normalizedCharacterSum (negativeOrbitFinset u N x) h ≤
      ((2 : ℝ) ^ d * distanceProduct u h)⁻¹ / (N : ℝ) ^ d := by
  rw [normalizedCharacterSum_negativeOrbitFinset hu]
  have hNp : 0 < (N : ℝ) ^ d := by positivity
  rw [div_le_div_iff_of_pos_right hNp]
  have hD : 0 < (2 : ℝ) ^ d * distanceProduct u h := by
    rw [← prod_two_mul_integerDistance_eq]
    apply Finset.prod_pos
    intro i hi
    have : 0 < integerDistance (h • u i) := by
      simpa only [integerDistance, norm_pos_iff] using hz i
    positivity
  rw [inv_eq_one_div, le_div_iff₀ hD]
  rw [← prod_two_mul_integerDistance_eq]
  simpa only [mul_comm] using orbitBoxCharacterSum_product_bound N u h

theorem character_neg (x : Circle) : character (-x) = star (character x) := by
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

theorem character_neg_zsmul (h : ℤ) (x : Circle) :
    character ((-h) • x) = star (character (h • x)) := by
  rw [neg_smul, character_neg]

theorem norm_character_sum_neg (F : Finset Circle) (h : ℤ) :
    ‖∑ x ∈ F, character ((-h) • x)‖ =
      ‖∑ x ∈ F, character (h • x)‖ := by
  simp_rw [character_neg_zsmul]
  rw [← star_sum]
  exact Complex.norm_conj _

@[simp]
theorem normalizedCharacterSum_neg (F : Finset Circle) (h : ℤ) :
    normalizedCharacterSum F (-h) = normalizedCharacterSum F h := by
  unfold normalizedCharacterSum
  rw [norm_character_sum_neg]

theorem frequencyCost_le_of_norm_le (F : Finset Circle) (c : ℤ → ℂ)
    (C : ℝ) (h : ℤ) (hc : ‖c h‖ ≤ C / |(h : ℝ)|) :
    frequencyCost F c h ≤ C / |(h : ℝ)| * normalizedCharacterSum F h := by
  unfold frequencyCost normalizedCharacterSum
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- The `{0,1}`-valued characteristic function of an arc. -/
noncomputable def arcIndicator (a : Circle) (ℓ : ℝ) : Circle → ℝ := by
  classical
  exact fun x ↦ if x ∈ arc a ℓ then 1 else 0

/-- The points of `F` which lie in a given arc. -/
noncomputable def pointsInArc (F : Finset Circle) (a : Circle) (ℓ : ℝ) : Finset Circle := by
  classical
  exact F.filter (· ∈ arc a ℓ)

theorem sum_arc_indicator (F : Finset Circle) (a : Circle) (ℓ : ℝ) :
    ∑ x ∈ F, arcIndicator a ℓ x = (pointsInArc F a ℓ).card := by
  classical
  simp [arcIndicator, pointsInArc]

theorem empiricalAverage_arc_indicator (F : Finset Circle) (a : Circle) (ℓ : ℝ) :
    empiricalAverage F (arcIndicator a ℓ) = arcMass F a ℓ := by
  classical
  rw [empiricalAverage, sum_arc_indicator]
  simp [arcMass, pointsInArc]

theorem empiricalAverage_const_add_of_nonempty {F : Finset Circle} (hF : F.Nonempty)
    (b : ℝ) (f : Circle → ℝ) :
    empiricalAverage F (fun x ↦ b + f x) = b + empiricalAverage F f := by
  classical
  simp only [empiricalAverage, sum_add_distrib, sum_const, nsmul_eq_mul]
  field_simp [hF.card_ne_zero]

theorem empiricalAverage_mono (F : Finset Circle) {f g : Circle → ℝ}
    (hfg : ∀ x ∈ F, f x ≤ g x) : empiricalAverage F f ≤ empiricalAverage F g := by
  unfold empiricalAverage
  gcongr with x hx
  exact hfg x hx

theorem norm_sum_re_le_frequencyCost_mul_card (F : Finset Circle)
    (c : ℤ → ℂ) (h : ℤ) :
    |∑ x ∈ F, (c h * character (h • x)).re| ≤ frequencyCost F c h * F.card := by
  classical
  have hre : (∑ x ∈ F, c h * character (h • x)).re =
      ∑ x ∈ F, (c h * character (h • x)).re := by simp
  rw [← hre]
  calc
    |(∑ x ∈ F, c h * character (h • x)).re| ≤
        ‖∑ x ∈ F, c h * character (h • x)‖ := Complex.abs_re_le_norm _
    _ = ‖c h * ∑ x ∈ F, character (h • x)‖ := by
      congr 1
      rw [mul_sum]
    _ = ‖c h‖ * ‖∑ x ∈ F, character (h • x)‖ := norm_mul _ _
    _ = frequencyCost F c h * F.card := by
      unfold frequencyCost
      by_cases hcard : F.card = 0
      · have hF : F = ∅ := card_eq_zero.mp hcard
        simp [hF]
      · field_simp

theorem abs_empiricalAverage_realTrigTail_le {F : Finset Circle} (hF : F.Nonempty)
    (S : Finset ℤ) (c : ℤ → ℂ) :
    |empiricalAverage F (realTrigTail S c)| ≤ ∑ h ∈ S, frequencyCost F c h := by
  classical
  unfold empiricalAverage
  have hcardAbs : |(F.card : ℝ)| = F.card := abs_of_nonneg (Nat.cast_nonneg _)
  rw [abs_div, hcardAbs]
  simp only [realTrigTail]
  change |∑ x ∈ F, (∑ h ∈ S, c h * character (h • x)).re| / F.card ≤ _
  have hswap : ∑ x ∈ F, (∑ h ∈ S, c h * character (h • x)).re =
      ∑ h ∈ S, ∑ x ∈ F, (c h * character (h • x)).re := by
    simp_rw [Complex.re_sum]
    exact sum_comm
  rw [hswap]
  calc
    |∑ h ∈ S, ∑ x ∈ F, (c h * character (h • x)).re| / F.card ≤
        (∑ h ∈ S, |∑ x ∈ F, (c h * character (h • x)).re|) / F.card := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ h ∈ S, frequencyCost F c h * F.card) / F.card := by
      gcongr with h hh
      exact norm_sum_re_le_frequencyCost_mul_card F c h
    _ = ∑ h ∈ S, frequencyCost F c h := by
      rw [← sum_mul]
      field_simp [hF.card_ne_zero]

/-- Fourier-sandwich form of the Erdős--Turán argument. -/
theorem abs_arcMass_sub_le_of_fourier_sandwich
    {F : Finset Circle} (hF : F.Nonempty) (a : Circle) (ℓ δ bPlus bMinus : ℝ)
    (SPlus SMinus : Finset ℤ) (cPlus cMinus : ℤ → ℂ)
    (_hδ : 0 ≤ δ)
    (hbPlus : bPlus - ℓ ≤ δ) (hbMinus : ℓ - bMinus ≤ δ)
    (hupper : ∀ x, arcIndicator a ℓ x ≤ bPlus + realTrigTail SPlus cPlus x)
    (hlower : ∀ x, bMinus + realTrigTail SMinus cMinus x ≤ arcIndicator a ℓ x) :
    |arcMass F a ℓ - ℓ| ≤ δ +
      (∑ h ∈ SPlus, frequencyCost F cPlus h) +
      (∑ h ∈ SMinus, frequencyCost F cMinus h) := by
  classical
  have havgUpper := empiricalAverage_mono F (fun x _ ↦ hupper x)
  have havgLower := empiricalAverage_mono F (fun x _ ↦ hlower x)
  rw [empiricalAverage_arc_indicator,
    empiricalAverage_const_add_of_nonempty hF] at havgUpper havgLower
  have htailPlus := abs_empiricalAverage_realTrigTail_le hF SPlus cPlus
  have htailMinus := abs_empiricalAverage_realTrigTail_le hF SMinus cMinus
  have hcostPlus : 0 ≤ ∑ h ∈ SPlus, frequencyCost F cPlus h :=
    sum_nonneg (fun h _ ↦ frequencyCost_nonneg F cPlus h)
  have hcostMinus : 0 ≤ ∑ h ∈ SMinus, frequencyCost F cMinus h :=
    sum_nonneg (fun h _ ↦ frequencyCost_nonneg F cMinus h)
  rw [abs_le] at htailPlus htailMinus
  rw [abs_le]
  constructor <;> linarith

/-- An Erdős--Turán-shaped consequence of the sandwich lemma. -/
theorem abs_arcMass_sub_le_of_harmonic_fourier_sandwich
    {F : Finset Circle} (hF : F.Nonempty) (a : Circle) (ℓ δ bPlus bMinus C : ℝ)
    (SPlus SMinus : Finset ℤ) (cPlus cMinus : ℤ → ℂ)
    (hδ : 0 ≤ δ)
    (hbPlus : bPlus - ℓ ≤ δ) (hbMinus : ℓ - bMinus ≤ δ)
    (hupper : ∀ x, arcIndicator a ℓ x ≤ bPlus + realTrigTail SPlus cPlus x)
    (hlower : ∀ x, bMinus + realTrigTail SMinus cMinus x ≤ arcIndicator a ℓ x)
    (hcPlus : ∀ h ∈ SPlus, ‖cPlus h‖ ≤ C / |(h : ℝ)|)
    (hcMinus : ∀ h ∈ SMinus, ‖cMinus h‖ ≤ C / |(h : ℝ)|) :
    |arcMass F a ℓ - ℓ| ≤ δ +
      (∑ h ∈ SPlus, C / |(h : ℝ)| * normalizedCharacterSum F h) +
      (∑ h ∈ SMinus, C / |(h : ℝ)| * normalizedCharacterSum F h) := by
  refine (abs_arcMass_sub_le_of_fourier_sandwich hF a ℓ δ bPlus bMinus
    SPlus SMinus cPlus cMinus hδ hbPlus hbMinus hupper hlower).trans ?_
  have hp : ∑ h ∈ SPlus, frequencyCost F cPlus h ≤
      ∑ h ∈ SPlus, C / |(h : ℝ)| * normalizedCharacterSum F h := by
    gcongr with h hh
    exact frequencyCost_le_of_norm_le F cPlus C h (hcPlus h hh)
  have hm : ∑ h ∈ SMinus, frequencyCost F cMinus h ≤
      ∑ h ∈ SMinus, C / |(h : ℝ)| * normalizedCharacterSum F h := by
    gcongr with h hh
    exact frequencyCost_le_of_norm_le F cMinus C h (hcMinus h hh)
  linarith

/-- Pointwise arc bounds immediately bound the supremum defining discrepancy. -/
theorem intervalDiscrepancy_le_of_arc_bound (F : Finset Circle) (B : ℝ)
    (hB : ∀ a ℓ, ℓ ∈ Set.Icc (0 : ℝ) 1 → |arcMass F a ℓ - ℓ| ≤ B) :
    intervalDiscrepancy F ≤ B := by
  apply csSup_le
  · exact ⟨|arcMass F 0 0 - 0|, 0, 0, by simp, rfl⟩
  · rintro r ⟨a, ℓ, hℓ, rfl⟩
    exact hB a ℓ hℓ

end

end Erdos1124.OneDimensionalDiscrepancy
