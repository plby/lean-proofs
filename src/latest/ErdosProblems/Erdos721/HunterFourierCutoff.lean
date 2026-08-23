/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterDiophantine
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite Fourier cutoffs and the quantitative torus-orbit lemma

This file isolates the elementary Fourier calculation in Hunter's argument.
A cutoff is represented by its nonnegative, finitely supported Fourier
coefficients.  Averaging it over all differences of two initial orbit
segments produces a Fejér square, so resonant frequencies contribute
nonnegatively and all remaining frequencies are controlled by a geometric
sum.
-/

namespace Erdos721.HunterFourierCutoff

open Function Set
open scoped BigOperators ComplexConjugate

open HunterTorus HunterPhase HunterLattice HunterDistributedCenters
  HunterDiophantine

/-- The unit-complex character attached to an integral torus frequency. -/
noncomputable def torusCharacter {D : ℕ} (ξ : Fin D → ℤ)
    (x : Torus D) : ℂ :=
  fourier 1 (integerDot ξ x)

@[simp] lemma torusCharacter_zero_frequency {D : ℕ} (x : Torus D) :
    torusCharacter (0 : Fin D → ℤ) x = 1 := by
  simp [torusCharacter, integerDot]

@[simp] lemma torusCharacter_zero_point {D : ℕ} (ξ : Fin D → ℤ) :
    torusCharacter ξ (0 : Torus D) = 1 := by
  simp [torusCharacter]

lemma torusCharacter_add {D : ℕ} (ξ : Fin D → ℤ) (x y : Torus D) :
    torusCharacter ξ (x + y) = torusCharacter ξ x * torusCharacter ξ y := by
  simp [torusCharacter, fourier_one, map_add, AddCircle.toCircle_add]

lemma torusCharacter_neg {D : ℕ} (ξ : Fin D → ℤ) (x : Torus D) :
    torusCharacter ξ (-x) = conj (torusCharacter ξ x) := by
  rw [torusCharacter, map_neg, fourier_one, AddCircle.toCircle_neg]
  simpa [torusCharacter, fourier_one] using
    Circle.coe_inv_eq_conj (AddCircle.toCircle (integerDot ξ x))

lemma torusCharacter_sub {D : ℕ} (ξ : Fin D → ℤ) (x y : Torus D) :
    torusCharacter ξ (x - y) =
      torusCharacter ξ x * conj (torusCharacter ξ y) := by
  rw [sub_eq_add_neg, torusCharacter_add, torusCharacter_neg]

lemma norm_torusCharacter {D : ℕ} (ξ : Fin D → ℤ) (x : Torus D) :
    ‖torusCharacter ξ x‖ = 1 := by
  simp [torusCharacter, fourier_apply, Circle.norm_coe]

@[simp] lemma torusCharacter_nsmul {D : ℕ} (ξ : Fin D → ℤ)
    (n : ℕ) (x : Torus D) :
    torusCharacter ξ (n • x) = torusCharacter ξ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, torusCharacter_add, ih, pow_succ]

/-- The ordinary geometric sum of a circle character. -/
noncomputable def circleGeomSum (L : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i : Fin L, fourier 1 (i.val • x)

@[simp] lemma fourier_one_nsmul (n : ℕ) (x : AddCircle (1 : ℝ)) :
    fourier 1 (n • x) = fourier 1 x ^ n := by
  simp [fourier_one, AddCircle.toCircle_nsmul]

lemma circleGeomSum_eq_geom (L : ℕ) (x : AddCircle (1 : ℝ)) :
    circleGeomSum L x =
      Finset.sum (Finset.range L) fun i ↦ (fourier 1 x) ^ i := by
  simp only [circleGeomSum, fourier_one_nsmul]
  simpa using (Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (fourier 1 x) ^ i) L)

/-- Chord distance on the unit circle dominates four times the quotient
metric distance to zero. -/
lemma four_norm_le_norm_one_sub_fourier (x : AddCircle (1 : ℝ)) :
    4 * ‖x‖ ≤ ‖1 - fourier 1 x‖ := by
  let r := centeredCoord x
  have hr : |r| ≤ 1 / 2 := abs_centeredCoord_le_half x
  have hpi : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hpi
  have hfourier : fourier 1 x =
      Complex.exp (Complex.I * (2 * Real.pi * r)) := by
    rw [← AddCircle.coe_equivIco (p := (1 : ℝ))
      (a := -(1 / 2 : ℝ)) (y := x), fourier_coe_apply]
    dsimp [r, centeredCoord]
    congr 1
    push_cast
    ring
  have hexponent : Complex.I * (2 * Real.pi * r) =
      Complex.I * ((2 * Real.pi * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfourier, norm_sub_rev,
    hexponent,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    show (2 * Real.pi * r) / 2 = Real.pi * r by ring]
  have hrnorm : |r| = ‖x‖ := HunterPhase.abs_centeredCoord_eq_norm x
  have hsin' : 2 * |r| ≤ |Real.sin (Real.pi * r)| := by
    calc
      2 * |r| = 2 / Real.pi * |Real.pi * r| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp
      _ ≤ |Real.sin (Real.pi * r)| := hsin
  rw [← hrnorm]
  nlinarith

/-- Away from zero, a circle geometric sum has the standard reciprocal
bound.  The deliberately loose constant is convenient downstream. -/
lemma norm_circleGeomSum_le {L : ℕ} {x : AddCircle (1 : ℝ)} {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hx : epsilon < ‖x‖) :
    ‖circleGeomSum L x‖ ≤ (2 * epsilon)⁻¹ := by
  let z : ℂ := fourier 1 x
  have hzNorm : ‖z‖ = 1 := by
    simp [z, fourier_apply, Circle.norm_coe]
  have hchord : 4 * epsilon < ‖1 - z‖ :=
    (mul_lt_mul_of_pos_left hx (by norm_num)).trans_le
      (four_norm_le_norm_one_sub_fourier x)
  have hgeom : circleGeomSum L x * (z - 1) = z ^ L - 1 := by
    rw [circleGeomSum_eq_geom]
    exact geom_sum_mul z L
  have hmul : ‖circleGeomSum L x‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, hzNorm]; norm_num)
  have hden : 2 * epsilon < ‖z - 1‖ := by
    rw [norm_sub_rev]
    linarith
  have heps0 : 0 < 2 * epsilon := by positivity
  rw [inv_eq_one_div, le_div_iff₀ heps0]
  have hnorm0 : 0 ≤ ‖circleGeomSum L x‖ := norm_nonneg _
  have hchord' : 4 * epsilon < ‖z - 1‖ := by
    rwa [norm_sub_rev]
  have hfourmul : ‖circleGeomSum L x‖ * (4 * epsilon) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hchord'.le hnorm0).trans hmul
  nlinarith

/-- A finite Fourier polynomial with nonnegative coefficients, normalized
constant coefficient, and a spatial sign condition. -/
structure FourierCutoff (D H : ℕ) (radius massBound : ℝ) where
  coeff : FrequencyCode D H → ℝ
  value : Torus D → ℝ
  coeff_nonneg : ∀ a, 0 ≤ coeff a
  coeff_zero : coeff (zeroFrequencyCode D H) = 1
  expansion : ∀ x,
    (value x : ℂ) = ∑ a, (coeff a : ℂ) *
      torusCharacter (decodeFrequency a) x
  nonpos_outside : ∀ x, x ∉ centeredBox D radius → value x ≤ 0
  coeff_sum_le : ∑ a, coeff a ≤ massBound

/-- Fejér energy of one character on an initial orbit segment. -/
noncomputable def geomEnergy {D : ℕ} (L : ℕ) (ξ : Fin D → ℤ)
    (alpha : Torus D) : ℝ :=
  Complex.normSq (circleGeomSum L (integerDot ξ alpha))

lemma geomEnergy_nonneg {D : ℕ} (L : ℕ) (ξ : Fin D → ℤ)
    (alpha : Torus D) : 0 ≤ geomEnergy L ξ alpha :=
  Complex.normSq_nonneg _

lemma geomEnergy_zero_frequency {D L : ℕ} (alpha : Torus D) :
    geomEnergy L (0 : Fin D → ℤ) alpha = (L : ℝ) ^ 2 := by
  simp [geomEnergy, circleGeomSum, integerDot, Complex.normSq]
  ring

lemma geomEnergy_le_of_nonresonant {D L : ℕ} {ξ : Fin D → ℤ}
    {alpha : Torus D} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hξ : epsilon < ‖integerDot ξ alpha‖) :
    geomEnergy L ξ alpha ≤ (2 * epsilon)⁻¹ ^ 2 := by
  rw [geomEnergy, ← Complex.sq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_circleGeomSum_le hepsilon hξ) 2

lemma torusCharacter_orbit_sub_orbit_sub {D : ℕ} (ξ : Fin D → ℤ)
    (i j : ℕ) (alpha y : Torus D) :
    torusCharacter ξ (i • alpha - j • alpha - y) =
      torusCharacter ξ (i • alpha) *
        conj (torusCharacter ξ (j • alpha)) *
          conj (torusCharacter ξ y) := by
  rw [torusCharacter_sub, torusCharacter_sub]

/-- The double orbit average of one character is its Fejér square times the
target phase. -/
lemma sum_sum_torusCharacter_orbit {D L : ℕ} (ξ : Fin D → ℤ)
    (alpha y : Torus D) :
    (∑ i : Fin L, ∑ j : Fin L,
        torusCharacter ξ (i.val • alpha - j.val • alpha - y)) =
      (geomEnergy L ξ alpha : ℂ) * conj (torusCharacter ξ y) := by
  simp_rw [torusCharacter_orbit_sub_orbit_sub]
  have hsum : (∑ i : Fin L, torusCharacter ξ (i.val • alpha)) =
      circleGeomSum L (integerDot ξ alpha) := by
    apply Finset.sum_congr rfl
    intro i _hi
    simp [torusCharacter, circleGeomSum, map_nsmul]
  calc
    (∑ i : Fin L, ∑ j : Fin L,
        torusCharacter ξ (i.val • alpha) *
          conj (torusCharacter ξ (j.val • alpha)) *
            conj (torusCharacter ξ y)) =
        ((∑ i : Fin L, torusCharacter ξ (i.val • alpha)) *
          (∑ j : Fin L, conj (torusCharacter ξ (j.val • alpha)))) *
            conj (torusCharacter ξ y) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ((∑ i : Fin L, torusCharacter ξ (i.val • alpha)) *
          conj (∑ j : Fin L, torusCharacter ξ (j.val • alpha))) *
            conj (torusCharacter ξ y) := by rw [map_sum]
    _ = (geomEnergy L ξ alpha : ℂ) *
          conj (torusCharacter ξ y) := by
      rw [hsum, Complex.mul_conj]
      rfl

/-- Sum of a cutoff over all differences of two initial orbit segments. -/
noncomputable def orbitCutoffSum {D H : ℕ} {radius massBound : ℝ}
    (F : FourierCutoff D H radius massBound) (L : ℕ)
    (alpha y : Torus D) : ℝ :=
  ∑ i : Fin L, ∑ j : Fin L,
    F.value (i.val • alpha - j.val • alpha - y)

lemma orbitCutoffSum_complex {D H L : ℕ} {radius massBound : ℝ}
    (F : FourierCutoff D H radius massBound) (alpha y : Torus D) :
    (orbitCutoffSum F L alpha y : ℂ) =
      ∑ a : FrequencyCode D H,
        (F.coeff a : ℂ) * (geomEnergy L (decodeFrequency a) alpha : ℂ) *
          conj (torusCharacter (decodeFrequency a) y) := by
  classical
  let f := fun (i j : Fin L) (a : FrequencyCode D H) ↦
    (F.coeff a : ℂ) * torusCharacter (decodeFrequency a)
      (i.val • alpha - j.val • alpha - y)
  calc
    (orbitCutoffSum F L alpha y : ℂ) =
        ∑ i : Fin L, ∑ j : Fin L, ∑ a : FrequencyCode D H, f i j a := by
      rw [orbitCutoffSum]
      push_cast
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      exact F.expansion _
    _ = ∑ i : Fin L, ∑ a : FrequencyCode D H, ∑ j : Fin L, f i j a := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Finset.sum_comm
    _ = ∑ a : FrequencyCode D H, ∑ i : Fin L, ∑ j : Fin L, f i j a :=
      Finset.sum_comm
    _ = ∑ a : FrequencyCode D H,
        (F.coeff a : ℂ) *
          (∑ i : Fin L, ∑ j : Fin L,
            torusCharacter (decodeFrequency a)
              (i.val • alpha - j.val • alpha - y)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [f, Finset.mul_sum]
    _ = ∑ a : FrequencyCode D H,
        (F.coeff a : ℂ) * (geomEnergy L (decodeFrequency a) alpha : ℂ) *
          conj (torusCharacter (decodeFrequency a) y) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [sum_sum_torusCharacter_orbit]
      ring

lemma orbitCutoffSum_eq_real_sum {D H L : ℕ} {radius massBound : ℝ}
    (F : FourierCutoff D H radius massBound) (alpha y : Torus D) :
    orbitCutoffSum F L alpha y =
      ∑ a : FrequencyCode D H,
        F.coeff a * geomEnergy L (decodeFrequency a) alpha *
          (torusCharacter (decodeFrequency a) y).re := by
  have h := congrArg Complex.re
    (orbitCutoffSum_complex (L := L) F alpha y)
  simpa using h

/-- Fourier lower bound for the double orbit sum.  Frequencies whose phase
is at most `epsilon` must annihilate the target; all other frequencies are
bounded by the geometric-sum estimate. -/
lemma orbitCutoffSum_lower {D H L : ℕ} {radius massBound epsilon : ℝ}
    (F : FourierCutoff D H radius massBound)
    (hepsilon : 0 < epsilon) (alpha y : Torus D)
    (hphase : ∀ a : FrequencyCode D H,
      ‖integerDot (decodeFrequency a) alpha‖ ≤ epsilon →
        integerDot (decodeFrequency a) y = 0) :
    (L : ℝ) ^ 2 - massBound * (2 * epsilon)⁻¹ ^ 2 ≤
      orbitCutoffSum F L alpha y := by
  classical
  let C : ℝ := (2 * epsilon)⁻¹ ^ 2
  let term : FrequencyCode D H → ℝ := fun a ↦
    F.coeff a * geomEnergy L (decodeFrequency a) alpha *
      (torusCharacter (decodeFrequency a) y).re
  have hC : 0 ≤ C := sq_nonneg _
  have hterm : ∀ a : FrequencyCode D H,
      -F.coeff a * C ≤ term a := by
    intro a
    have hc := F.coeff_nonneg a
    have hE := geomEnergy_nonneg L (decodeFrequency a) alpha
    by_cases ha : ‖integerDot (decodeFrequency a) alpha‖ ≤ epsilon
    · have hy := hphase a ha
      have hchar : torusCharacter (decodeFrequency a) y = 1 := by
        simp [torusCharacter, hy]
      simp only [term, hchar, Complex.one_re, mul_one]
      have hprod : 0 ≤ F.coeff a * geomEnergy L (decodeFrequency a) alpha :=
        mul_nonneg hc hE
      have hneg : -F.coeff a * C ≤ 0 := by
        nlinarith [mul_nonneg hc hC]
      exact hneg.trans hprod
    · have hnon : epsilon < ‖integerDot (decodeFrequency a) alpha‖ :=
        lt_of_not_ge ha
      have hEle : geomEnergy L (decodeFrequency a) alpha ≤ C := by
        exact geomEnergy_le_of_nonresonant hepsilon hnon
      have hre : -1 ≤ (torusCharacter (decodeFrequency a) y).re := by
        have habs := Complex.abs_re_le_norm
          (torusCharacter (decodeFrequency a) y)
        rw [norm_torusCharacter] at habs
        linarith [neg_abs_le
          (torusCharacter (decodeFrequency a) y).re]
      have hcoefEnergy :
          F.coeff a * geomEnergy L (decodeFrequency a) alpha ≤
            F.coeff a * C := mul_le_mul_of_nonneg_left hEle hc
      have hleft : -F.coeff a * C ≤
          -(F.coeff a * geomEnergy L (decodeFrequency a) alpha) := by
        linarith
      have hright : -(F.coeff a * geomEnergy L
          (decodeFrequency a) alpha) ≤ term a := by
        dsimp [term]
        nlinarith [mul_le_mul_of_nonneg_left hre
          (mul_nonneg hc hE)]
      exact hleft.trans hright
  have hzero : term (zeroFrequencyCode D H) = (L : ℝ) ^ 2 := by
    simp [term, F.coeff_zero, geomEnergy_zero_frequency]
  have hsumErase :
      ∑ a ∈ (Finset.univ : Finset (FrequencyCode D H)).erase
          (zeroFrequencyCode D H), -F.coeff a * C ≤
        ∑ a ∈ (Finset.univ : Finset (FrequencyCode D H)).erase
          (zeroFrequencyCode D H), term a := by
    apply Finset.sum_le_sum
    intro a _ha
    exact hterm a
  have hcoeffErase :
      ∑ a ∈ (Finset.univ : Finset (FrequencyCode D H)).erase
          (zeroFrequencyCode D H), F.coeff a ≤ massBound := by
    calc
      _ ≤ ∑ a : FrequencyCode D H, F.coeff a := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun _ _ _ ↦ F.coeff_nonneg _)
      _ ≤ massBound := F.coeff_sum_le
  rw [orbitCutoffSum_eq_real_sum]
  change (L : ℝ) ^ 2 - massBound * C ≤ ∑ a, term a
  rw [← Finset.sum_erase_add (Finset.univ) term
      (Finset.mem_univ (zeroFrequencyCode D H)),
    hzero]
  have hpenalty : -massBound * C ≤
      ∑ a ∈ (Finset.univ : Finset (FrequencyCode D H)).erase
        (zeroFrequencyCode D H), -F.coeff a * C := by
    let s := (Finset.univ : Finset (FrequencyCode D H)).erase
      (zeroFrequencyCode D H)
    have hmul := mul_le_mul_of_nonneg_right hcoeffErase hC
    calc
      -massBound * C ≤ -(∑ a ∈ s, F.coeff a) * C := by
        dsimp [s] at hmul ⊢
        nlinarith
      _ = ∑ a ∈ s, -F.coeff a * C := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.sum_neg_distrib]
  linarith [hpenalty.trans hsumErase]

/-- Quantitative orbit hitting: some difference of two indices below `L`
lands in the cutoff box around the prescribed target. -/
theorem exists_orbit_difference_mem_box {D H L : ℕ}
    {radius massBound epsilon : ℝ}
    (F : FourierCutoff D H radius massBound)
    (hepsilon : 0 < epsilon) (alpha y : Torus D)
    (hphase : ∀ a : FrequencyCode D H,
      ‖integerDot (decodeFrequency a) alpha‖ ≤ epsilon →
        integerDot (decodeFrequency a) y = 0)
    (hlarge : massBound * (2 * epsilon)⁻¹ ^ 2 < (L : ℝ) ^ 2) :
    ∃ i j : Fin L,
      i.val • alpha - j.val • alpha - y ∈ centeredBox D radius := by
  have hlower := orbitCutoffSum_lower (L := L) F hepsilon alpha y hphase
  have hpos : 0 < orbitCutoffSum F L alpha y := by linarith
  by_contra hex
  push_neg at hex
  have hnonpos : orbitCutoffSum F L alpha y ≤ 0 := by
    rw [orbitCutoffSum]
    apply Finset.sum_nonpos
    intro i _hi
    apply Finset.sum_nonpos
    intro j _hj
    exact F.nonpos_outside _ (hex i j)
  exact (not_lt_of_ge hnonpos) hpos

end Erdos721.HunterFourierCutoff
