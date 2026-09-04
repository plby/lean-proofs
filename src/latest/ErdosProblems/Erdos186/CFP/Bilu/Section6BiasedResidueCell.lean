/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section7FreimanMap
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bilu Lemma 6.3: a large simultaneous half-cell

This file formalizes Ruzsa's weighted AM--GM proof of Bilu's Lemma 6.3.
If every binary coordinate has a lower-half bias larger than
`(1 + δ) / 2`, one simultaneous residue cell contains more than the
`r`-fold product of the corresponding entropy gain.
-/

namespace Erdos186.CFP.Bilu.Section6BiasedResidueCell

open scoped BigOperators RealInnerProductSpace
open Section7FreimanMap Proposition74Construction SubspaceLattice

noncomputable section

/-- The optimizing weight in Ruzsa's weighted AM--GM proof. -/
def biasRatio (δ : ℝ) : ℝ := (1 + δ) / (1 - δ)

/-- Bilu's explicit gain over the unbiased `2⁻¹` factor, in the
optimization form used directly by the proof.  Below we identify it with
the source's entropy-product formula. -/
def biasGamma (δ : ℝ) : ℝ :=
  2 * (biasRatio δ) ^ ((1 + δ) / 2) / (1 + biasRatio δ)

theorem biasGamma_div_two (δ : ℝ) :
    biasGamma δ / 2 =
      (biasRatio δ) ^ ((1 + δ) / 2) / (1 + biasRatio δ) := by
  rw [biasGamma]
  ring

/-- Entropy-product form of Bilu's constant, as printed after Lemma 6.3. -/
theorem biasGamma_eq_entropyProduct {δ : ℝ} (hδneg : -1 < δ)
    (hδone : δ < 1) :
    biasGamma δ =
      (1 + δ) ^ ((1 + δ) / 2) *
        (1 - δ) ^ ((1 - δ) / 2) := by
  have hplus : 0 < 1 + δ := by linarith
  have hminus : 0 < 1 - δ := by linarith
  let p : ℝ := (1 + δ) / 2
  calc
    biasGamma δ =
        2 * (((1 + δ) / (1 - δ)) ^ p) /
          (1 + (1 + δ) / (1 - δ)) := by
      rfl
    _ = (((1 + δ) / (1 - δ)) ^ p) * (1 - δ) := by
      field_simp
      <;> ring
    _ = ((1 + δ) ^ p / (1 - δ) ^ p) * (1 - δ) := by
      rw [Real.div_rpow hplus.le hminus.le]
    _ = (1 + δ) ^ p * ((1 - δ) / (1 - δ) ^ p) := by ring
    _ = (1 + δ) ^ p * (1 - δ) ^ (1 - p) := by
      rw [Real.rpow_one_sub' hminus.le (by dsimp only [p]; linarith)]
    _ = (1 + δ) ^ ((1 + δ) / 2) *
        (1 - δ) ^ ((1 - δ) / 2) := by
      dsimp only [p]
      congr 2
      ring

/-- The logarithmic gain whose exponential is `biasGamma`. -/
def entropyGain (δ : ℝ) : ℝ :=
  ((1 + δ) / 2) * Real.log (1 + δ) +
    ((1 - δ) / 2) * Real.log (1 - δ)

theorem log_biasGamma {δ : ℝ} (hδneg : -1 < δ) (hδone : δ < 1) :
    Real.log (biasGamma δ) = entropyGain δ := by
  have hplus : 0 < 1 + δ := by linarith
  have hminus : 0 < 1 - δ := by linarith
  rw [biasGamma_eq_entropyProduct hδneg hδone,
    Real.log_mul (Real.rpow_pos_of_pos hplus _).ne'
      (Real.rpow_pos_of_pos hminus _).ne',
    Real.log_rpow hplus, Real.log_rpow hminus]
  unfold entropyGain
  ring

/-- The excess of the logarithmic gain over the quadratic lower bound. -/
def entropyExcess (δ : ℝ) : ℝ := entropyGain δ - δ ^ 2 / 2

theorem hasDerivAt_entropyExcess {δ : ℝ} (hδneg : -1 < δ)
    (hδone : δ < 1) :
    HasDerivAt entropyExcess
      (1 / 2 * Real.log ((1 + δ) / (1 - δ)) - δ) δ := by
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 δ := by
    simpa [add_comm] using (hasDerivAt_id δ).const_add 1
  have hminus : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) δ := by
    simpa only [id_eq] using (hasDerivAt_id δ).const_sub 1
  have hplusNe : 1 + δ ≠ 0 := by linarith
  have hminusNe : 1 - δ ≠ 0 := by linarith
  have hlogPlus :
      HasDerivAt (fun x : ℝ ↦ Real.log (1 + x)) (1 / (1 + δ)) δ := by
    simpa only [one_div, mul_one] using hplus.log hplusNe
  have hlogMinus :
      HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-1 / (1 - δ)) δ := by
    simpa only [one_div, mul_neg, neg_div] using hminus.log hminusNe
  have htermPlus := (hplus.div_const 2).mul hlogPlus
  have htermMinus := (hminus.div_const 2).mul hlogMinus
  have hsquare := ((hasDerivAt_id δ).pow 2).div_const 2
  have htotal := (htermPlus.add htermMinus).sub hsquare
  change HasDerivAt
    (fun x : ℝ ↦ (1 + x) / 2 * Real.log (1 + x) +
      (1 - x) / 2 * Real.log (1 - x) - x ^ 2 / 2)
    (1 / 2 * Real.log (1 + δ) + (1 + δ) / 2 * (1 / (1 + δ)) +
      (-1 / 2 * Real.log (1 - δ) +
        (1 - δ) / 2 * (-1 / (1 - δ))) -
      (2 : ℝ) * δ ^ (2 - 1) * 1 / 2) δ at htotal
  change HasDerivAt
    (fun x : ℝ ↦ (1 + x) / 2 * Real.log (1 + x) +
      (1 - x) / 2 * Real.log (1 - x) - x ^ 2 / 2)
    (1 / 2 * Real.log ((1 + δ) / (1 - δ)) - δ) δ
  convert htotal using 1
  rw [Real.log_div (by linarith) (by linarith)]
  field_simp
  ring

/-- Bilu's numerical entropy estimate in logarithmic form. -/
theorem half_sq_lt_entropyGain {δ : ℝ} (hδpos : 0 < δ)
    (hδone : δ < 1) :
    δ ^ 2 / 2 < entropyGain δ := by
  let F : ℝ → ℝ := entropyExcess
  have hcontinuous : ContinuousOn F (Set.Icc 0 δ) := by
    intro x hx
    have hplus : 1 + x ≠ 0 := by linarith [hx.1]
    have hminus : 1 - x ≠ 0 := by linarith [hx.2]
    have hcPlus : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x :=
      (Real.continuousAt_log hplus).comp
        (continuousAt_const.add continuousAt_id)
    have hcMinus : ContinuousAt (fun y : ℝ ↦ Real.log (1 - y)) x :=
      (Real.continuousAt_log hminus).comp
        (continuousAt_const.sub continuousAt_id)
    change ContinuousWithinAt
      (fun y : ℝ ↦ (1 + y) / 2 * Real.log (1 + y) +
        (1 - y) / 2 * Real.log (1 - y) - y ^ 2 / 2)
      (Set.Icc 0 δ) x
    exact (((continuousAt_const.add continuousAt_id).div_const 2).mul hcPlus |>.add
      (((continuousAt_const.sub continuousAt_id).div_const 2).mul hcMinus) |>.sub
      ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc 0 δ),
      0 < deriv F x := by
    intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := hx.1
    have hxone : x < 1 := hx.2.trans hδone
    have hseries := Real.sum_range_le_log_div hxpos.le hxone 2
    have hstrict : x < 1 / 2 * Real.log ((1 + x) / (1 - x)) := by
      have hcube : 0 < x ^ 3 / 3 := by positivity
      norm_num [Finset.sum_range_succ] at hseries
      nlinarith
    rw [(hasDerivAt_entropyExcess (by linarith) hxone).deriv]
    exact sub_pos.mpr hstrict
  have hmono : StrictMonoOn F (Set.Icc 0 δ) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 δ) hcontinuous hderiv
  have hzero : F 0 = 0 := by
    simp [F, entropyExcess, entropyGain]
  have hpositive : 0 < F δ := by
    rw [← hzero]
    exact hmono ⟨le_rfl, hδpos.le⟩ ⟨hδpos.le, le_rfl⟩ hδpos
  dsimp only [F, entropyExcess] at hpositive
  linarith

/-- Remark 6.4: Bilu's gain strictly dominates `exp (δ²/2)`. -/
theorem exp_half_sq_lt_biasGamma {δ : ℝ} (hδpos : 0 < δ)
    (hδone : δ < 1) :
    Real.exp (δ ^ 2 / 2) < biasGamma δ := by
  have hlog := half_sq_lt_entropyGain hδpos hδone
  have hgammaPos : 0 < biasGamma δ := by
    rw [biasGamma_eq_entropyProduct (by linarith) hδone]
    positivity
  rw [← Real.exp_log hgammaPos]
  exact Real.exp_lt_exp.mpr (by
    rw [log_biasGamma (by linarith) hδone]
    exact hlog)

/-- The number of zero coordinates in a binary residue vector. -/
def zeroCoordinateCount {r : ℕ} (alpha : Fin r → Fin 2) : ℕ :=
  ∑ i, if alpha i = 0 then 1 else 0

/-- A generic fiber of a finite set under a binary coordinate coloring. -/
def binaryFiber {X : Type*} [DecidableEq X] {r : ℕ}
    (color : X → Fin r → Fin 2) (alpha : Fin r → Fin 2)
    (K : Finset X) : Finset X :=
  K.filter fun x ↦ color x = alpha

@[simp]
theorem mem_binaryFiber {X : Type*} [DecidableEq X] {r : ℕ}
    (color : X → Fin r → Fin 2) (alpha : Fin r → Fin 2)
    (K : Finset X) (x : X) :
    x ∈ binaryFiber color alpha K ↔ x ∈ K ∧ color x = alpha := by
  simp [binaryFiber]

/-- The binary fibers partition the finite source set. -/
theorem card_eq_sum_card_binaryFiber {X : Type*} [DecidableEq X] {r : ℕ}
    (color : X → Fin r → Fin 2) (K : Finset X) :
    K.card = ∑ alpha : Fin r → Fin 2, (binaryFiber color alpha K).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := color) (s := K) (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  rfl

/-- Double-counting incidences between a point and its zero-colored
coordinates. -/
theorem sum_zeroCoordinateCount_mul_card_binaryFiber
    {X : Type*} [DecidableEq X] {r : ℕ}
    (color : X → Fin r → Fin 2) (K : Finset X) :
    (∑ alpha : Fin r → Fin 2,
        zeroCoordinateCount alpha * (binaryFiber color alpha K).card) =
      ∑ i : Fin r, (K.filter fun x ↦ color x i = 0).card := by
  classical
  simp only [zeroCoordinateCount, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  let T : Finset (Fin r → Fin 2) := Finset.univ.filter fun alpha ↦ alpha i = 0
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter K T color
  calc
    (∑ alpha : Fin r → Fin 2,
        (if alpha i = 0 then 1 else 0) *
          (binaryFiber color alpha K).card) =
        ∑ alpha ∈ T, (binaryFiber color alpha K).card := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro alpha _halpha
          by_cases hzero : alpha i = 0 <;> simp [hzero]
    _ = (K.filter fun x ↦ color x i = 0).card := by
      simpa only [T, binaryFiber, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply] using hfiber

/-- The partition function of the number of zero coordinates. -/
theorem sum_rpow_zeroCoordinateCount {r : ℕ} {z : ℝ} (hz : 0 < z) :
    (∑ alpha : Fin r → Fin 2,
        z ^ (zeroCoordinateCount alpha : ℝ)) = (1 + z) ^ r := by
  classical
  rw [show (1 + z) ^ r = ∏ _i : Fin r, (1 + z) by simp]
  rw [show (∏ _i : Fin r, (1 + z)) =
      ∏ i : Fin r, ∑ bit : Fin 2,
        (if bit = 0 then z else 1) by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [Fin.sum_univ_two]
    simp [add_comm]]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  rw [zeroCoordinateCount, Nat.cast_sum, Real.rpow_sum_of_pos hz]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hzero : alpha i = 0
  · simp [hzero]
  · have hone : alpha i = 1 := Fin.eq_one_of_ne_zero _ hzero
    simp [hone]

/-- Abstract binary form of Bilu's Lemma 6.3.  It is separated from the
geometric definition of the cells so the weighted AM--GM bookkeeping can
be reused verbatim. -/
theorem exists_large_biased_binaryFiber
    {X : Type*} [DecidableEq X] {r : ℕ}
    (color : X → Fin r → Fin 2) (K : Finset X) {δ : ℝ}
    (hr : 0 < r) (hδpos : 0 < δ) (hδone : δ < 1)
    (hbias : ∀ i : Fin r,
      ((K.filter fun x ↦ color x i = 0).card : ℝ) >
        ((1 + δ) / 2) * K.card) :
    ∃ alpha : Fin r → Fin 2,
      (biasGamma δ / 2) ^ r * K.card <
        (binaryFiber color alpha K).card := by
  classical
  let p : ℝ := (1 + δ) / 2
  let z : ℝ := biasRatio δ
  have hKpos : 0 < (K.card : ℝ) := by
    let i : Fin r := ⟨0, hr⟩
    have hi := hbias i
    have hKnat : 0 < K.card := by
      by_contra hK
      have hKzero : K.card = 0 := Nat.eq_zero_of_not_pos hK
      have hfilterZero : (K.filter fun x ↦ color x i = 0).card = 0 := by
        exact Nat.eq_zero_of_le_zero
          ((Finset.card_filter_le _ _).trans_eq hKzero)
      have hfilterCast :
          ((K.filter fun x ↦ color x i = 0).card : ℝ) = 0 := by
        exact_mod_cast hfilterZero
      have hKCast : (K.card : ℝ) = 0 := by exact_mod_cast hKzero
      rw [hfilterCast, hKCast, mul_zero] at hi
      exact (lt_irrefl 0) hi
    exact_mod_cast hKnat
  have hzpos : 0 < z := by
    dsimp [z, biasRatio]
    positivity
  have hzone : 1 < z := by
    dsimp [z, biasRatio]
    rw [lt_div_iff₀ (by linarith : 0 < 1 - δ)]
    linarith
  have hweightCast :
      (∑ alpha : Fin r → Fin 2,
          ((zeroCoordinateCount alpha : ℕ) : ℝ) *
            ((binaryFiber color alpha K).card : ℝ)) =
        ∑ i : Fin r, ((K.filter fun x ↦ color x i = 0).card : ℝ) := by
    exact_mod_cast sum_zeroCoordinateCount_mul_card_binaryFiber color K
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hweightedCount :
      p * (r : ℝ) * K.card <
        ∑ alpha : Fin r → Fin 2,
          (zeroCoordinateCount alpha : ℝ) *
            (binaryFiber color alpha K).card := by
    have hsum := Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin r)).Nonempty)
      (fun i _hi ↦ hbias i)
    rw [hweightCast]
    dsimp only [p]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    calc
      (1 + δ) / 2 * (r : ℝ) * K.card =
          (r : ℝ) * ((1 + δ) / 2 * K.card) := by ring
      _ < ∑ i : Fin r, ((K.filter fun x ↦ color x i = 0).card : ℝ) := hsum
  let w : (Fin r → Fin 2) → ℝ := fun alpha ↦
    (binaryFiber color alpha K).card / K.card
  let value : (Fin r → Fin 2) → ℝ := fun alpha ↦
    z ^ (zeroCoordinateCount alpha : ℝ)
  have hw_nonneg : ∀ alpha ∈ (Finset.univ : Finset (Fin r → Fin 2)),
      0 ≤ w alpha := by
    intro alpha _halpha
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hw_sum : ∑ alpha : Fin r → Fin 2, w alpha = 1 := by
    dsimp only [w]
    rw [← Finset.sum_div]
    have hpartition := card_eq_sum_card_binaryFiber color K
    rw [← Nat.cast_sum, ← hpartition]
    exact div_self hKpos.ne'
  have hvalue_nonneg : ∀ alpha ∈ (Finset.univ : Finset (Fin r → Fin 2)),
      0 ≤ value alpha := by
    intro alpha _halpha
    exact (Real.rpow_pos_of_pos hzpos _).le
  have hamgm := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin r → Fin 2)) w value
    hw_nonneg hw_sum hvalue_nonneg
  have hprod :
      (∏ alpha : Fin r → Fin 2, (value alpha) ^ (w alpha)) =
        z ^ ((∑ alpha : Fin r → Fin 2,
          (zeroCoordinateCount alpha : ℝ) *
            (binaryFiber color alpha K).card) / K.card) := by
    rw [show (∏ alpha : Fin r → Fin 2, (value alpha) ^ (w alpha)) =
        ∏ alpha : Fin r → Fin 2,
          z ^ ((zeroCoordinateCount alpha : ℝ) * w alpha) by
      apply Finset.prod_congr rfl
      intro alpha _halpha
      dsimp only [value]
      rw [Real.rpow_mul hzpos.le]]
    rw [← Real.rpow_sum_of_pos hzpos]
    congr 1
    dsimp only [w]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro alpha _halpha
    ring
  have hexponent :
      p * (r : ℝ) <
        (∑ alpha : Fin r → Fin 2,
          (zeroCoordinateCount alpha : ℝ) *
            (binaryFiber color alpha K).card) / K.card := by
    rw [lt_div_iff₀ hKpos]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using hweightedCount
  have hlowerAverage :
      z ^ (p * (r : ℝ)) <
        ∑ alpha : Fin r → Fin 2, w alpha * value alpha := by
    calc
      z ^ (p * (r : ℝ)) <
          z ^ ((∑ alpha : Fin r → Fin 2,
            (zeroCoordinateCount alpha : ℝ) *
              (binaryFiber color alpha K).card) / K.card) :=
        Real.rpow_lt_rpow_of_exponent_lt hzone hexponent
      _ = ∏ alpha : Fin r → Fin 2, (value alpha) ^ (w alpha) := hprod.symm
      _ ≤ ∑ alpha : Fin r → Fin 2, w alpha * value alpha := by
        simpa using hamgm
  have hlowerWeighted :
      (K.card : ℝ) * z ^ (p * (r : ℝ)) <
        ∑ alpha : Fin r → Fin 2,
          (binaryFiber color alpha K).card *
            z ^ (zeroCoordinateCount alpha : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hlowerAverage hKpos
    rw [Finset.mul_sum] at hmul
    have hsumEq :
        (∑ alpha : Fin r → Fin 2,
          (K.card : ℝ) * (w alpha * value alpha)) =
        ∑ alpha : Fin r → Fin 2,
          (binaryFiber color alpha K).card *
            z ^ (zeroCoordinateCount alpha : ℝ) := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      dsimp only [w, value]
      field_simp
    rw [hsumEq] at hmul
    exact hmul
  by_contra hnone
  push Not at hnone
  have hupperWeighted :
      (∑ alpha : Fin r → Fin 2,
          (binaryFiber color alpha K).card *
            z ^ (zeroCoordinateCount alpha : ℝ)) ≤
        ((biasGamma δ / 2) ^ r * K.card) * (1 + z) ^ r := by
    calc
      _ ≤ ∑ alpha : Fin r → Fin 2,
          ((biasGamma δ / 2) ^ r * K.card) *
            z ^ (zeroCoordinateCount alpha : ℝ) := by
        apply Finset.sum_le_sum
        intro alpha _halpha
        exact mul_le_mul_of_nonneg_right (hnone alpha)
          (Real.rpow_nonneg hzpos.le _)
      _ = ((biasGamma δ / 2) ^ r * K.card) *
          (∑ alpha : Fin r → Fin 2,
            z ^ (zeroCoordinateCount alpha : ℝ)) := by
        rw [Finset.mul_sum]
      _ = ((biasGamma δ / 2) ^ r * K.card) * (1 + z) ^ r := by
        rw [sum_rpow_zeroCoordinateCount hzpos]
  have hopt :
      ((biasGamma δ / 2) ^ r * K.card) * (1 + z) ^ r =
        (K.card : ℝ) * z ^ (p * (r : ℝ)) := by
    rw [biasGamma_div_two]
    change (((z ^ p / (1 + z)) ^ r * (K.card : ℝ)) * (1 + z) ^ r) = _
    have hden : 1 + z ≠ 0 := by positivity
    have hpowers : (z ^ p) ^ r = z ^ (p * (r : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hzpos.le p (r : ℝ)).symm
    rw [div_pow, hpowers]
    field_simp
  rw [hopt] at hupperWeighted
  exact (not_lt_of_ge hupperWeighted) hlowerWeighted

/-- Bilu's Lemma 6.3 in the residue-cell language used by Section 7.
The apparently redundant nonnegativity test in `hbias` records the
source's half-open interval `[0, 1/2)` literally. -/
theorem exists_large_biased_residueCell
    {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (K : Finset (Mahler.IntegralPoint m)) {δ : ℝ}
    (hr : 0 < r) (hδpos : 0 < δ) (hδone : δ < 1)
    (hbias : ∀ i : Fin r,
      ((K.filter fun x ↦
          0 ≤ Int.fract (phase a b x i) ∧
            Int.fract (phase a b x i) < 1 / 2).card : ℝ) >
        ((1 + δ) / 2) * K.card) :
    ∃ alpha : Fin r → Fin 2,
      (biasGamma δ / 2) ^ r * K.card <
        (residueCell a b alpha K).card := by
  classical
  have hbias' : ∀ i : Fin r,
      ((K.filter fun x ↦ residueColor a b x i = 0).card : ℝ) >
        ((1 + δ) / 2) * K.card := by
    intro i
    have hfilter :
        K.filter (fun x ↦ residueColor a b x i = 0) =
          K.filter (fun x ↦
            0 ≤ Int.fract (phase a b x i) ∧
              Int.fract (phase a b x i) < 1 / 2) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hxK, hcolor⟩
        refine ⟨hxK, Int.fract_nonneg _, ?_⟩
        simpa [residueColor] using hcolor
      · rintro ⟨hxK, _hnonneg, hhalf⟩
        refine ⟨hxK, ?_⟩
        simp only [residueColor, if_pos]
        norm_num at hhalf ⊢
        exact hhalf
    rw [hfilter]
    exact hbias i
  obtain ⟨alpha, halpha⟩ :=
    exists_large_biased_binaryFiber (residueColor a b) K
      hr hδpos hδone hbias'
  refine ⟨alpha, ?_⟩
  simpa only [binaryFiber, residueCell_eq_filter_color] using halpha

end

end Erdos186.CFP.Bilu.Section6BiasedResidueCell

#print axioms Erdos186.CFP.Bilu.Section6BiasedResidueCell.exp_half_sq_lt_biasGamma
#print axioms Erdos186.CFP.Bilu.Section6BiasedResidueCell.exists_large_biased_binaryFiber
#print axioms Erdos186.CFP.Bilu.Section6BiasedResidueCell.exists_large_biased_residueCell
