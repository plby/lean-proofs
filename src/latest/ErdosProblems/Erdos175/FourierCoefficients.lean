/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos175.Sawtooth

/-!
# The degree-ten Vaaler coefficients used in Erdős problem 175

This file contains the finite numerical part of Granville--Ramaré's
degree-`10` sawtooth estimate.  In particular, it proves the sharp finite
coefficient bound which is responsible for the constants `43 / 6` and
`11 / 8` in their equation (7.2).
-/

noncomputable section

namespace Erdos175
namespace FourierCoefficients

open Set

/-- The rational lower endpoint used for `π`. -/
def piLower : ℝ := 3.141592

/-- The rational upper endpoint used for `π`. -/
def piUpper : ℝ := 3.141593

lemma piLower_lt_pi : piLower < Real.pi := by
  exact Real.pi_gt_d6

lemma pi_lt_piUpper : Real.pi < piUpper := by
  exact Real.pi_lt_d6

/-- Taylor polynomial for sine through degree eleven. -/
def sinPoly11 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 -
    x ^ 11 / 39916800

/-- Taylor polynomial for cosine through degree ten. -/
def cosPoly10 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800

def sinLower (x : ℝ) : ℝ := sinPoly11 x - x ^ 12 / 479001600
def sinUpper (x : ℝ) : ℝ := sinPoly11 x + x ^ 12 / 479001600
def cosLower (x : ℝ) : ℝ := cosPoly10 x - x ^ 11 / 39916800
def cosUpper (x : ℝ) : ℝ := cosPoly10 x + x ^ 11 / 39916800

private lemma sin_taylor_polynomial {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.sin 11 (Set.Icc 0 x) 0 x = sinPoly11 x := by
  rw [taylor_within_apply]
  have hderiv (n : ℕ) :
      iteratedDerivWithin n Real.sin (Set.Icc 0 x) 0 =
        iteratedDeriv n Real.sin 0 :=
    Real.iteratedDerivWithin_sin_Icc n hx (by simp [hx.le])
  simp_rw [hderiv]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_sin,
    Real.iteratedDeriv_odd_sin, sinPoly11]
  ring

private lemma cos_taylor_polynomial {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.cos 10 (Set.Icc 0 x) 0 x = cosPoly10 x := by
  rw [taylor_within_apply]
  have hderiv (n : ℕ) :
      iteratedDerivWithin n Real.cos (Set.Icc 0 x) 0 =
        iteratedDeriv n Real.cos 0 :=
    Real.iteratedDerivWithin_cos_Icc n hx (by simp [hx.le])
  simp_rw [hderiv]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_even_cos,
    Real.iteratedDeriv_odd_cos, cosPoly10]
  ring

lemma abs_sin_sub_sinPoly11 {x : ℝ} (hx : 0 < x) :
    |Real.sin x - sinPoly11 x| ≤ x ^ 12 / 479001600 := by
  obtain ⟨y, _hy, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (x := x) (x₀ := 0) (n := 11) hx.ne
    Real.contDiff_sin.contDiffOn
  have hpoly :
      taylorWithinEval Real.sin 11 (Set.uIcc 0 x) 0 x = sinPoly11 x := by
    rw [Set.uIcc_of_le hx.le]
    exact sin_taylor_polynomial hx
  rw [← hpoly, hrem]
  simp only [sub_zero, Nat.factorial]
  rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hx.le]
  have hd := Real.abs_iteratedDeriv_sin_le_one 12 y
  norm_num at hd ⊢
  have hxpow : 0 ≤ x ^ 12 := by positivity
  nlinarith

lemma abs_cos_sub_cosPoly10 {x : ℝ} (hx : 0 < x) :
    |Real.cos x - cosPoly10 x| ≤ x ^ 11 / 39916800 := by
  obtain ⟨y, _hy, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.cos) (x := x) (x₀ := 0) (n := 10) hx.ne
    Real.contDiff_cos.contDiffOn
  have hpoly :
      taylorWithinEval Real.cos 10 (Set.uIcc 0 x) 0 x = cosPoly10 x := by
    rw [Set.uIcc_of_le hx.le]
    exact cos_taylor_polynomial hx
  rw [← hpoly, hrem]
  simp only [sub_zero, Nat.factorial]
  rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hx.le]
  have hd := Real.abs_iteratedDeriv_cos_le_one 11 y
  norm_num at hd ⊢
  have hxpow : 0 ≤ x ^ 11 := by positivity
  nlinarith

lemma sinLower_le_sin {x : ℝ} (hx : 0 < x) :
    sinLower x ≤ Real.sin x := by
  have h := abs_sin_sub_sinPoly11 hx
  rw [abs_le] at h
  dsimp [sinLower]
  linarith

lemma sin_le_sinUpper {x : ℝ} (hx : 0 < x) :
    Real.sin x ≤ sinUpper x := by
  have h := abs_sin_sub_sinPoly11 hx
  rw [abs_le] at h
  dsimp [sinUpper]
  linarith

lemma cosLower_le_cos {x : ℝ} (hx : 0 < x) :
    cosLower x ≤ Real.cos x := by
  have h := abs_cos_sub_cosPoly10 hx
  rw [abs_le] at h
  dsimp [cosLower]
  linarith

lemma cos_le_cosUpper {x : ℝ} (hx : 0 < x) :
    Real.cos x ≤ cosUpper x := by
  have h := abs_cos_sub_cosPoly10 hx
  rw [abs_le] at h
  dsimp [cosUpper]
  linarith

/-- Rational Taylor enclosures transported to any angle between `l` and `u`
inside the first quadrant. -/
lemma trig_enclosure {l x u : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hxu : x ≤ u)
    (hu : u ≤ Real.pi / 2) :
    sinLower l ≤ Real.sin x ∧ Real.sin x ≤ sinUpper u ∧
      cosLower u ≤ Real.cos x ∧ Real.cos x ≤ cosUpper l := by
  have huxpi : u ≤ Real.pi := hu.trans (by linarith [Real.pi_pos])
  have hxpi2 : x ≤ Real.pi / 2 := hxu.trans hu
  have hxnonneg : 0 ≤ x := hl.le.trans hlx
  have hsin_lx : Real.sin l ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxpi2 hlx
  have hsin_xu : Real.sin x ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hu hxu
  have hcos_xl : Real.cos x ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi hl.le (hxpi2.trans (by linarith [Real.pi_pos])) hlx
  have hcos_ux : Real.cos u ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hxnonneg huxpi hxu
  exact ⟨(sinLower_le_sin hl).trans hsin_lx,
    hsin_xu.trans (sin_le_sinUpper (hl.trans_le (hlx.trans hxu))),
    (cosLower_le_cos (hl.trans_le (hlx.trans hxu))).trans hcos_ux,
    hcos_xl.trans (cos_le_cosUpper hl)⟩

/-- The imaginary coordinate of either degree-ten majorant/minorant
coefficient at positive frequency `k`. -/
def imagAmplitude (k : ℕ) : ℝ :=
  (Real.pi * (1 - (k : ℝ) / 11) *
      Real.cot (Real.pi * (k : ℝ) / 11) + 1) / (22 * Real.pi)

/-- The absolute value of the real coordinate at positive frequency `k`. -/
def realAmplitude (k : ℕ) : ℝ := (1 - (k : ℝ) / 11) / 22

/-- Rational upper certificates for the ten imaginary coordinates. -/
def imagBound : ℕ → ℝ
  | 1 => 0.155200
  | 2 => 0.072338
  | 3 => 0.043114
  | 4 => 0.027679
  | 5 => 0.018034
  | 6 => 0.011499
  | 7 => 0.006921
  | 8 => 0.003727
  | 9 => 0.001609
  | 10 => 0.000396
  | _ => 0

/-- Rational upper certificates for the ten complex coefficient norms. -/
def normBound : ℕ → ℝ
  | 1 => 0.160607
  | 2 => 0.081339
  | 3 => 0.054329
  | 4 => 0.040036
  | 5 => 0.030659
  | 6 => 0.023646
  | 7 => 0.017920
  | 8 => 0.012945
  | 9 => 0.008420
  | 10 => 0.004152
  | _ => 0

private def lowerAngle (m : ℕ) : ℝ := piLower * (m : ℝ) / 11
private def upperAngle (m : ℕ) : ℝ := piUpper * (m : ℝ) / 11
private def exactAngle (m : ℕ) : ℝ := Real.pi * (m : ℝ) / 11

private lemma rational_angle_enclosure {m : ℕ} (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    sinLower (lowerAngle m) ≤ Real.sin (exactAngle m) ∧
      Real.sin (exactAngle m) ≤ sinUpper (upperAngle m) ∧
      cosLower (upperAngle m) ≤ Real.cos (exactAngle m) ∧
      Real.cos (exactAngle m) ≤ cosUpper (lowerAngle m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl : 0 < lowerAngle m := by
    dsimp [lowerAngle, piLower]
    positivity
  have hlx : lowerAngle m ≤ exactAngle m := by
    dsimp [lowerAngle, exactAngle]
    gcongr
    exact piLower_lt_pi.le
  have hxu : exactAngle m ≤ upperAngle m := by
    dsimp [exactAngle, upperAngle]
    gcongr
    exact pi_lt_piUpper.le
  have hu' : upperAngle m ≤ piLower / 2 := by
    calc
      upperAngle m ≤ upperAngle 5 := by
        dsimp [upperAngle]
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm5)
            (by norm_num [piUpper])
        · norm_num
      _ ≤ piLower / 2 := by norm_num [upperAngle, piUpper, piLower]
  have hu : upperAngle m ≤ Real.pi / 2 :=
    hu'.trans (div_le_div_of_nonneg_right piLower_lt_pi.le (by norm_num))
  exact trig_enclosure hl hlx hxu hu

private lemma exactAngle_pos {m : ℕ} (hm : 1 ≤ m) : 0 < exactAngle m := by
  dsimp [exactAngle]
  have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  positivity

private lemma exactAngle_lt_pi {m : ℕ} (hm : m ≤ 10) : exactAngle m < Real.pi := by
  dsimp [exactAngle]
  have hpi := Real.pi_pos
  have hm' : (m : ℝ) < 11 := by exact_mod_cast (show m < 11 by omega)
  nlinarith

/-- On the first five frequencies, a rational Taylor certificate bounds the
imaginary coordinate.  This packages the ordered-field bookkeeping; the ten
instances below are discharged by exact rational normalization. -/
private lemma imagAmplitude_le_of_low_certificate {k : ℕ} {B : ℝ}
    (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (hB : 0 ≤ B)
    (hcert :
      piUpper * (1 - (k : ℝ) / 11) * cosUpper (lowerAngle k) +
          sinUpper (upperAngle k) ≤
        22 * piLower * B * sinLower (lowerAngle k)) :
    imagAmplitude k ≤ B := by
  obtain ⟨hslo, hshi, _hclo, hchi⟩ := rational_angle_enclosure hk1 hk5
  have hxpos : 0 < exactAngle k := exactAngle_pos hk1
  have hxpi : exactAngle k < Real.pi := exactAngle_lt_pi (by omega)
  have hspos : 0 < Real.sin (exactAngle k) :=
    Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
  have hcpos : 0 < Real.cos (exactAngle k) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, hxpos]
    · dsimp [exactAngle]
      have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
      nlinarith [Real.pi_pos]
  have hq : 0 ≤ 1 - (k : ℝ) / 11 := by
    have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
    norm_num
    linarith
  have hcu : 0 ≤ cosUpper (lowerAngle k) :=
    hcpos.le.trans hchi
  have hpiq : Real.pi * (1 - (k : ℝ) / 11) ≤
      piUpper * (1 - (k : ℝ) / 11) :=
    mul_le_mul_of_nonneg_right pi_lt_piUpper.le hq
  have hcosprod :
      Real.pi * (1 - (k : ℝ) / 11) * Real.cos (exactAngle k) ≤
        piUpper * (1 - (k : ℝ) / 11) * cosUpper (lowerAngle k) :=
    (mul_le_mul_of_nonneg_right hpiq hcpos.le).trans
      (mul_le_mul_of_nonneg_left hchi (mul_nonneg (by
        exact pi_lt_piUpper.le.trans' Real.pi_pos.le) hq))
  have hslopos : 0 < sinLower (lowerAngle k) := by
    interval_cases k <;>
      norm_num [sinLower, sinPoly11, lowerAngle, piLower] at hk1 hk5 ⊢
  have hdenlower :
      22 * piLower * B * sinLower (lowerAngle k) ≤
        22 * Real.pi * B * Real.sin (exactAngle k) := by
    have hp : 0 ≤ (22 : ℝ) := by norm_num
    have h1 : 22 * piLower ≤ 22 * Real.pi :=
      mul_le_mul_of_nonneg_left piLower_lt_pi.le hp
    have h2 : 22 * piLower * B ≤ 22 * Real.pi * B :=
      mul_le_mul_of_nonneg_right h1 hB
    exact (mul_le_mul_of_nonneg_right h2 hslopos.le).trans
      (mul_le_mul_of_nonneg_left hslo (mul_nonneg
        (mul_nonneg hp Real.pi_pos.le) hB))
  have hnum :
      Real.pi * (1 - (k : ℝ) / 11) * Real.cos (exactAngle k) +
          Real.sin (exactAngle k) ≤
        22 * Real.pi * B * Real.sin (exactAngle k) := by
    exact (add_le_add hcosprod hshi).trans (hcert.trans hdenlower)
  rw [imagAmplitude, Real.cot_eq_cos_div_sin]
  change (Real.pi * (1 - (k : ℝ) / 11) *
      (Real.cos (exactAngle k) / Real.sin (exactAngle k)) + 1) /
        (22 * Real.pi) ≤ B
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 22 * Real.pi)]
  calc
    Real.pi * (1 - (k : ℝ) / 11) *
          (Real.cos (exactAngle k) / Real.sin (exactAngle k)) + 1 =
        (Real.pi * (1 - (k : ℝ) / 11) * Real.cos (exactAngle k) +
          Real.sin (exactAngle k)) / Real.sin (exactAngle k) := by
            field_simp
    _ ≤ 22 * Real.pi * B := (div_le_iff₀ hspos).2 (by
      simpa [mul_assoc] using hnum)
    _ = B * (22 * Real.pi) := by ring

private lemma imagAmplitude_reflect (m : ℕ) (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    imagAmplitude (11 - m) =
      (Real.sin (exactAngle m) - exactAngle m * Real.cos (exactAngle m)) /
        (22 * Real.pi * Real.sin (exactAngle m)) := by
  have hmle : m ≤ 11 := by omega
  have hxpos := exactAngle_pos hm1
  have hxpi := exactAngle_lt_pi (by omega : m ≤ 10)
  have hsne : Real.sin (exactAngle m) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hxpos hxpi).ne'
  have hangle : Real.pi * ((11 - m : ℕ) : ℝ) / 11 =
      Real.pi - exactAngle m := by
    rw [Nat.cast_sub hmle]
    dsimp [exactAngle]
    ring
  rw [imagAmplitude, hangle, Real.cot_eq_cos_div_sin,
    Real.sin_pi_sub, Real.cos_pi_sub]
  rw [Nat.cast_sub hmle]
  push_cast
  field_simp [hsne]
  dsimp [exactAngle]
  ring

private lemma imagAmplitude_le_of_high_certificate {m : ℕ} {B : ℝ}
    (hm1 : 1 ≤ m) (hm5 : m ≤ 5) (hB : 0 ≤ B)
    (hcert :
      sinUpper (upperAngle m) - lowerAngle m * cosLower (upperAngle m) ≤
        22 * piLower * B * sinLower (lowerAngle m)) :
    imagAmplitude (11 - m) ≤ B := by
  obtain ⟨hslo, hshi, hclo, _hchi⟩ := rational_angle_enclosure hm1 hm5
  have hxpos : 0 < exactAngle m := exactAngle_pos hm1
  have hxpi : exactAngle m < Real.pi := exactAngle_lt_pi (by omega)
  have hspos : 0 < Real.sin (exactAngle m) :=
    Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
  have hcpos : 0 < Real.cos (exactAngle m) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, hxpos]
    · dsimp [exactAngle]
      have hmR : (m : ℝ) ≤ 5 := by exact_mod_cast hm5
      nlinarith [Real.pi_pos]
  have hclopos : 0 < cosLower (upperAngle m) := by
    interval_cases m <;>
      norm_num [cosLower, cosPoly10, upperAngle, piUpper] at hm1 hm5 ⊢
  have hylower : lowerAngle m ≤ exactAngle m := by
    dsimp [lowerAngle, exactAngle]
    gcongr
    exact piLower_lt_pi.le
  have hproduct :
      lowerAngle m * cosLower (upperAngle m) ≤
        exactAngle m * Real.cos (exactAngle m) :=
    (mul_le_mul_of_nonneg_right hylower hclopos.le).trans
      (mul_le_mul_of_nonneg_left hclo hxpos.le)
  have hslopos : 0 < sinLower (lowerAngle m) := by
    interval_cases m <;>
      norm_num [sinLower, sinPoly11, lowerAngle, piLower] at hm1 hm5 ⊢
  have hdenlower :
      22 * piLower * B * sinLower (lowerAngle m) ≤
        22 * Real.pi * B * Real.sin (exactAngle m) := by
    have hp : 0 ≤ (22 : ℝ) := by norm_num
    have h1 : 22 * piLower ≤ 22 * Real.pi :=
      mul_le_mul_of_nonneg_left piLower_lt_pi.le hp
    have h2 : 22 * piLower * B ≤ 22 * Real.pi * B :=
      mul_le_mul_of_nonneg_right h1 hB
    exact (mul_le_mul_of_nonneg_right h2 hslopos.le).trans
      (mul_le_mul_of_nonneg_left hslo (mul_nonneg
        (mul_nonneg hp Real.pi_pos.le) hB))
  have hnum :
      Real.sin (exactAngle m) - exactAngle m * Real.cos (exactAngle m) ≤
        22 * Real.pi * B * Real.sin (exactAngle m) := by
    calc
      Real.sin (exactAngle m) - exactAngle m * Real.cos (exactAngle m) ≤
          sinUpper (upperAngle m) - lowerAngle m * cosLower (upperAngle m) :=
        sub_le_sub hshi hproduct
      _ ≤ 22 * piLower * B * sinLower (lowerAngle m) := hcert
      _ ≤ 22 * Real.pi * B * Real.sin (exactAngle m) := hdenlower
  rw [imagAmplitude_reflect m hm1 hm5]
  rw [div_le_iff₀ (mul_pos (by positivity) hspos)]
  have heq : B * (22 * Real.pi * Real.sin (exactAngle m)) =
      22 * Real.pi * B * Real.sin (exactAngle m) := by ring
  rw [heq]
  exact hnum

/-- Each of the ten imaginary coordinates is bounded by the displayed
six-decimal rational certificate. -/
lemma imagAmplitude_le_imagBound {k : ℕ} (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    imagAmplitude k ≤ imagBound k := by
  interval_cases k
  · exact imagAmplitude_le_of_low_certificate (k := 1) (B := imagBound 1)
      (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
        norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
          sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10])
  · exact imagAmplitude_le_of_low_certificate (k := 2) (B := imagBound 2)
      (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
        norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
          sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10])
  · exact imagAmplitude_le_of_low_certificate (k := 3) (B := imagBound 3)
      (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
        norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
          sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10])
  · exact imagAmplitude_le_of_low_certificate (k := 4) (B := imagBound 4)
      (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
        norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
          sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10])
  · exact imagAmplitude_le_of_low_certificate (k := 5) (B := imagBound 5)
      (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
        norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
          sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10])
  · simpa [imagBound] using
      (imagAmplitude_le_of_high_certificate (m := 5) (B := imagBound 6)
        (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
          norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
            sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10]))
  · simpa [imagBound] using
      (imagAmplitude_le_of_high_certificate (m := 4) (B := imagBound 7)
        (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
          norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
            sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10]))
  · simpa [imagBound] using
      (imagAmplitude_le_of_high_certificate (m := 3) (B := imagBound 8)
        (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
          norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
            sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10]))
  · simpa [imagBound] using
      (imagAmplitude_le_of_high_certificate (m := 2) (B := imagBound 9)
        (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
          norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
            sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10]))
  · simpa [imagBound] using
      (imagAmplitude_le_of_high_certificate (m := 1) (B := imagBound 10)
        (by norm_num) (by norm_num) (by norm_num [imagBound]) (by
          norm_num [imagBound, piUpper, piLower, lowerAngle, upperAngle,
            sinLower, sinUpper, cosLower, cosUpper, sinPoly11, cosPoly10]))

private lemma reflected_numerator_nonneg {m : ℕ} (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    0 ≤ Real.sin (exactAngle m) - exactAngle m * Real.cos (exactAngle m) := by
  have hxpos : 0 < exactAngle m := exactAngle_pos hm1
  have hxhalf : exactAngle m < Real.pi / 2 := by
    dsimp [exactAngle]
    have hmR : (m : ℝ) ≤ 5 := by exact_mod_cast hm5
    nlinarith [Real.pi_pos]
  have hcpos : 0 < Real.cos (exactAngle m) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos, hxpos, hxhalf]
  have ht := Real.le_tan hxpos.le hxhalf
  rw [Real.tan_eq_sin_div_cos] at ht
  have := (le_div_iff₀ hcpos).mp ht
  linarith

/-- The imaginary coordinates have the sign shown in the paper. -/
lemma imagAmplitude_nonneg {k : ℕ} (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    0 ≤ imagAmplitude k := by
  by_cases hk5 : k ≤ 5
  · have hxpos : 0 < exactAngle k := exactAngle_pos hk1
    have hxhalf : exactAngle k < Real.pi / 2 := by
      dsimp [exactAngle]
      have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
      nlinarith [Real.pi_pos]
    have hspos : 0 < Real.sin (exactAngle k) :=
      Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hxhalf, Real.pi_pos])
    have hcpos : 0 < Real.cos (exactAngle k) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos, hxpos, hxhalf]
    have hcot : 0 ≤ Real.cot (exactAngle k) := by
      rw [Real.cot_eq_cos_div_sin]
      positivity
    have hq : 0 ≤ 1 - (k : ℝ) / 11 := by
      have hkR : (k : ℝ) ≤ 5 := by exact_mod_cast hk5
      norm_num
      linarith
    rw [imagAmplitude]
    change 0 ≤ (Real.pi * (1 - (k : ℝ) / 11) * Real.cot (exactAngle k) + 1) /
      (22 * Real.pi)
    positivity
  · let m := 11 - k
    have hm1 : 1 ≤ m := by dsimp [m]; omega
    have hm5 : m ≤ 5 := by dsimp [m]; omega
    have hkm : 11 - m = k := by dsimp [m]; omega
    rw [← hkm, imagAmplitude_reflect m hm1 hm5]
    have hspos : 0 < Real.sin (exactAngle m) :=
      Real.sin_pos_of_pos_of_lt_pi (exactAngle_pos hm1) (exactAngle_lt_pi (by omega))
    exact div_nonneg (reflected_numerator_nonneg hm1 hm5)
      (mul_nonneg (by positivity) hspos.le)

/-- A positive-frequency Vaaler coefficient.  `ε = 1` is the majorant and
`ε = -1` is the minorant. -/
def signedPositiveCoeff (ε : ℝ) (k : ℕ) : ℂ :=
  (ε * realAmplitude k : ℝ) + (imagAmplitude k : ℂ) * Complex.I

@[simp] lemma signedPositiveCoeff_re (ε : ℝ) (k : ℕ) :
    (signedPositiveCoeff ε k).re = ε * realAmplitude k := by
  simp [signedPositiveCoeff]

@[simp] lemma signedPositiveCoeff_im (ε : ℝ) (k : ℕ) :
    (signedPositiveCoeff ε k).im = imagAmplitude k := by
  simp [signedPositiveCoeff]

private lemma realAmplitude_nonneg {k : ℕ} (hk10 : k ≤ 10) :
    0 ≤ realAmplitude k := by
  dsimp [realAmplitude]
  have hkR : (k : ℝ) ≤ 10 := by exact_mod_cast hk10
  linarith

private lemma imagBound_nonneg {k : ℕ} (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    0 ≤ imagBound k := by
  interval_cases k <;> norm_num [imagBound] at hk1 hk10 ⊢

private lemma normBound_nonneg {k : ℕ} (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    0 ≤ normBound k := by
  interval_cases k <;> norm_num [normBound] at hk1 hk10 ⊢

/-- Certified norm bound for each positive-frequency coefficient. -/
lemma norm_signedPositiveCoeff_le_normBound {ε : ℝ} (hε : |ε| ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    ‖signedPositiveCoeff ε k‖ ≤ normBound k := by
  have hb0 : 0 ≤ imagAmplitude k := imagAmplitude_nonneg hk1 hk10
  have hb1 : imagAmplitude k ≤ imagBound k := imagAmplitude_le_imagBound hk1 hk10
  have hB0 : 0 ≤ imagBound k := imagBound_nonneg hk1 hk10
  have hc0 : 0 ≤ realAmplitude k := realAmplitude_nonneg hk10
  have heps : ε ^ 2 ≤ 1 := by
    rw [abs_le] at hε
    nlinarith [sq_nonneg (ε - 1), sq_nonneg (ε + 1)]
  have hrealSq : (ε * realAmplitude k) ^ 2 ≤ (realAmplitude k) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right heps (sq_nonneg (realAmplitude k))
    nlinarith
  have himagSq : (imagAmplitude k) ^ 2 ≤ (imagBound k) ^ 2 := by
    nlinarith [sq_nonneg (imagAmplitude k - imagBound k)]
  have hcert :
      (imagBound k) ^ 2 + (realAmplitude k) ^ 2 ≤ (normBound k) ^ 2 := by
    interval_cases k <;>
      norm_num [imagBound, realAmplitude, normBound] at hk1 hk10 ⊢
  have hnormSq :
      ‖signedPositiveCoeff ε k‖ ^ 2 =
        (ε * realAmplitude k) ^ 2 + (imagAmplitude k) ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    simp [signedPositiveCoeff]
    ring
  have hsquare : ‖signedPositiveCoeff ε k‖ ^ 2 ≤ (normBound k) ^ 2 := by
    rw [hnormSq]
    nlinarith
  have hnorm0 : 0 ≤ ‖signedPositiveCoeff ε k‖ := norm_nonneg _
  have hnb0 : 0 ≤ normBound k := normBound_nonneg hk1 hk10
  nlinarith [sq_nonneg (‖signedPositiveCoeff ε k‖ + normBound k)]

/-- The sum of the positive-frequency norm certificates. -/
lemma sum_normBound_le :
    (∑ k ∈ Finset.Icc 1 10, normBound k) ≤ (43 : ℝ) / 99 := by
  norm_num [normBound, Finset.sum_Icc_succ_top]

/-- The positive half of the degree-ten coefficient sum. -/
lemma sum_norm_signedPositiveCoeff_le {ε : ℝ} (hε : |ε| ≤ 1) :
    (∑ k ∈ Finset.Icc 1 10, ‖signedPositiveCoeff ε k‖) ≤ (43 : ℝ) / 99 := by
  calc
    (∑ k ∈ Finset.Icc 1 10, ‖signedPositiveCoeff ε k‖) ≤
        ∑ k ∈ Finset.Icc 1 10, normBound k := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.mem_Icc] at hk
      exact norm_signedPositiveCoeff_le_normBound hε hk.1 hk.2
    _ ≤ (43 : ℝ) / 99 := sum_normBound_le

/-- Both nonzero halves together have `L¹` norm at most `86/99`. -/
lemma two_mul_sum_norm_signedPositiveCoeff_le {ε : ℝ} (hε : |ε| ≤ 1) :
    2 * (∑ k ∈ Finset.Icc 1 10, ‖signedPositiveCoeff ε k‖) ≤
      (86 : ℝ) / 99 := by
  nlinarith [sum_norm_signedPositiveCoeff_le hε]

/-- Granville--Ramaré's coefficient `a_r^ε` for `R = 10`.  The value at
frequency zero is set to zero because the Fourier sum omits that frequency. -/
def degreeTenCoeff (ε : ℝ) (r : ℤ) : ℂ :=
  if r = 0 then 0 else
    ((ε * (1 - (r.natAbs : ℝ) / 11) / 22 : ℝ) : ℂ) +
      (((Real.pi * (1 - (r.natAbs : ℝ) / 11) *
          Real.cot (Real.pi * (r : ℝ) / 11) +
          (r.natAbs : ℝ) / (r : ℝ)) / (22 * Real.pi) : ℝ) : ℂ) * Complex.I

@[simp] lemma degreeTenCoeff_zero (ε : ℝ) : degreeTenCoeff ε 0 = 0 := by
  simp [degreeTenCoeff]

/-- The exact integer-frequency formula reduces to the positive-frequency
coordinate form. -/
lemma degreeTenCoeff_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    degreeTenCoeff ε (k : ℤ) = signedPositiveCoeff ε k := by
  rw [degreeTenCoeff, if_neg (by exact_mod_cast hk)]
  simp only [Int.natAbs_natCast, Int.cast_natCast]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  dsimp [signedPositiveCoeff, imagAmplitude, realAmplitude]
  field_simp [hkR, Real.pi_ne_zero]

/-- Negative-frequency coefficients are conjugates of the corresponding
positive-frequency coefficients. -/
lemma degreeTenCoeff_neg_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    degreeTenCoeff ε (-(k : ℤ)) =
      ((ε * realAmplitude k : ℝ) : ℂ) - (imagAmplitude k : ℂ) * Complex.I := by
  have hkz : -(k : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hk)
  rw [degreeTenCoeff, if_neg hkz]
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
  have hcot : Real.cot (-(Real.pi * (k : ℝ) / 11)) =
      -Real.cot (Real.pi * (k : ℝ) / 11) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      Real.sin_neg, Real.cos_neg]
    ring
  rw [show Real.pi * (-(k : ℝ)) / 11 =
    -(Real.pi * (k : ℝ) / 11) by ring, hcot]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hscalar :
      (Real.pi * (1 - (k : ℝ) / 11) *
          (-Real.cot (Real.pi * (k : ℝ) / 11)) +
          (k : ℝ) / (-(k : ℝ))) / (22 * Real.pi) =
        -imagAmplitude k := by
    dsimp [imagAmplitude]
    field_simp [hkR, Real.pi_ne_zero]
    ring
  rw [hscalar]
  dsimp [realAmplitude]
  push_cast
  ring

@[simp] lemma norm_degreeTenCoeff_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖degreeTenCoeff ε (k : ℤ)‖ = ‖signedPositiveCoeff ε k‖ := by
  rw [degreeTenCoeff_ofNat ε hk]

@[simp] lemma norm_degreeTenCoeff_neg_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖degreeTenCoeff ε (-(k : ℤ))‖ = ‖signedPositiveCoeff ε k‖ := by
  rw [degreeTenCoeff_neg_ofNat ε hk]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def]
  simp [signedPositiveCoeff]

/-- The twenty nonzero frequencies used at degree ten. -/
def degreeTenFrequencies : Finset ℤ :=
  (Finset.Icc (-10 : ℤ) 10).erase 0

/-- Exact pairing of the twenty signed-frequency norms. -/
lemma sum_norm_degreeTenCoeff_eq (ε : ℝ) :
    (∑ r ∈ degreeTenFrequencies, ‖degreeTenCoeff ε r‖) =
      2 * ∑ k ∈ Finset.Icc 1 10, ‖signedPositiveCoeff ε k‖ := by
  have hfreq : degreeTenFrequencies =
      {(-10 : ℤ), -9, -8, -7, -6, -5, -4, -3, -2, -1,
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  rw [hfreq]
  norm_num [Finset.sum_Icc_succ_top]
  have hp1 : ‖degreeTenCoeff ε 1‖ = ‖signedPositiveCoeff ε 1‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp2 : ‖degreeTenCoeff ε 2‖ = ‖signedPositiveCoeff ε 2‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp3 : ‖degreeTenCoeff ε 3‖ = ‖signedPositiveCoeff ε 3‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp4 : ‖degreeTenCoeff ε 4‖ = ‖signedPositiveCoeff ε 4‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp5 : ‖degreeTenCoeff ε 5‖ = ‖signedPositiveCoeff ε 5‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp6 : ‖degreeTenCoeff ε 6‖ = ‖signedPositiveCoeff ε 6‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp7 : ‖degreeTenCoeff ε 7‖ = ‖signedPositiveCoeff ε 7‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp8 : ‖degreeTenCoeff ε 8‖ = ‖signedPositiveCoeff ε 8‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp9 : ‖degreeTenCoeff ε 9‖ = ‖signedPositiveCoeff ε 9‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  have hp10 : ‖degreeTenCoeff ε 10‖ = ‖signedPositiveCoeff ε 10‖ :=
    norm_degreeTenCoeff_ofNat ε (by norm_num)
  rw [show (-10 : ℤ) = -((10 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (10 : ℕ) ≠ 0),
    show (-9 : ℤ) = -((9 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (9 : ℕ) ≠ 0),
    show (-8 : ℤ) = -((8 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (8 : ℕ) ≠ 0),
    show (-7 : ℤ) = -((7 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (7 : ℕ) ≠ 0),
    show (-6 : ℤ) = -((6 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (6 : ℕ) ≠ 0),
    show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (5 : ℕ) ≠ 0),
    show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (4 : ℕ) ≠ 0),
    show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (3 : ℕ) ≠ 0),
    show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (2 : ℕ) ≠ 0),
    show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    norm_degreeTenCoeff_neg_ofNat ε (by norm_num : (1 : ℕ) ≠ 0),
    hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10]
  ring

/-- The sharp finite coefficient estimate used in equation (7.2). -/
theorem sum_norm_degreeTenCoeff_le {ε : ℝ} (hε : |ε| ≤ 1) :
    (∑ r ∈ degreeTenFrequencies, ‖degreeTenCoeff ε r‖) ≤ (86 : ℝ) / 99 := by
  rw [sum_norm_degreeTenCoeff_eq]
  exact two_mul_sum_norm_signedPositiveCoeff_le hε

/-! ### Identification with the sawtooth module -/

lemma degreeTenFrequencies_eq :
    degreeTenFrequencies = Sawtooth.frequencies 10 := by
  rfl

/-- The coordinate formula certified above is exactly the coefficient formula
used by the finite sawtooth module. -/
lemma degreeTenCoeff_eq_grCoefficient (ε : ℝ) {r : ℤ} (hr : r ≠ 0) :
    degreeTenCoeff ε r = Sawtooth.grCoefficient 10 ε r := by
  rw [degreeTenCoeff, if_neg hr]
  simp only [Sawtooth.grCoefficient, Nat.reduceAdd, Nat.cast_ofNat,
    OfNat.ofNat, Real.cot_eq_cos_div_sin]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

lemma degreeTenPlusCoefficient_eq {r : ℤ} (hr : r ≠ 0) :
    Sawtooth.degreeTenPlusCoefficient r = degreeTenCoeff 1 r := by
  rw [Sawtooth.degreeTenPlusCoefficient,
    degreeTenCoeff_eq_grCoefficient 1 hr]

lemma degreeTenMinusCoefficient_eq {r : ℤ} (hr : r ≠ 0) :
    Sawtooth.degreeTenMinusCoefficient r = -degreeTenCoeff (-1) r := by
  rw [Sawtooth.degreeTenMinusCoefficient,
    degreeTenCoeff_eq_grCoefficient (-1) hr]

theorem sum_norm_degreeTenPlusCoefficient_le :
    (∑ r ∈ Sawtooth.frequencies 10,
      ‖Sawtooth.degreeTenPlusCoefficient r‖) ≤ (86 : ℝ) / 99 := by
  rw [← degreeTenFrequencies_eq]
  calc
    (∑ r ∈ degreeTenFrequencies,
        ‖Sawtooth.degreeTenPlusCoefficient r‖) =
        ∑ r ∈ degreeTenFrequencies, ‖degreeTenCoeff 1 r‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr0 : r ≠ 0 := by
        change r ∈ (Finset.Icc (-10 : ℤ) 10).erase 0 at hr
        exact (Finset.mem_erase.mp hr).1
      rw [degreeTenPlusCoefficient_eq hr0]
    _ ≤ (86 : ℝ) / 99 := sum_norm_degreeTenCoeff_le (by norm_num)

theorem sum_norm_degreeTenMinusCoefficient_le :
    (∑ r ∈ Sawtooth.frequencies 10,
      ‖Sawtooth.degreeTenMinusCoefficient r‖) ≤ (86 : ℝ) / 99 := by
  rw [← degreeTenFrequencies_eq]
  calc
    (∑ r ∈ degreeTenFrequencies,
        ‖Sawtooth.degreeTenMinusCoefficient r‖) =
        ∑ r ∈ degreeTenFrequencies, ‖degreeTenCoeff (-1) r‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr0 : r ≠ 0 := by
        change r ∈ (Finset.Icc (-10 : ℤ) 10).erase 0 at hr
        exact (Finset.mem_erase.mp hr).1
      rw [degreeTenMinusCoefficient_eq hr0, norm_neg]
    _ ≤ (86 : ℝ) / 99 := sum_norm_degreeTenCoeff_le (by norm_num)

/-! ### The degree-eleven Fejér square -/

lemma e_add (x y : ℝ) :
    Sawtooth.e (x + y) = Sawtooth.e x * Sawtooth.e y := by
  unfold Sawtooth.e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e_conj (x : ℝ) :
    (starRingEnd ℂ) (Sawtooth.e x) = Sawtooth.e (-x) := by
  unfold Sawtooth.e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma e_nat_mul (m : ℕ) (x : ℝ) :
    Sawtooth.e ((m : ℝ) * x) = Sawtooth.e x ^ m := by
  induction m with
  | zero => simp [Sawtooth.e]
  | succ m ih =>
      rw [Nat.cast_succ, add_mul, e_add, ih, pow_succ]
      simp

/-- The one-sided degree-ten Dirichlet sum. -/
noncomputable def dirichlet11 (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.range 11, Sawtooth.e ((m : ℝ) * x)

/-- The normalized square form of the Fejér kernel of order eleven. -/
noncomputable def fejer11 (x : ℝ) : ℝ :=
  Complex.normSq (dirichlet11 x) / 11

theorem fejer11_nonneg (x : ℝ) : 0 ≤ fejer11 x := by
  exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

/-- The usual symmetric Fourier expansion of the same kernel. -/
noncomputable def fejer11Fourier (x : ℝ) : ℂ :=
  1 + ∑ k ∈ Finset.Icc (1 : ℕ) 10,
    (((1 - (k : ℝ) / 11 : ℝ) : ℂ) *
      (Sawtooth.e ((k : ℝ) * x) + Sawtooth.e (-(k : ℝ) * x)))

theorem fejer11Fourier_eq (x : ℝ) :
    fejer11Fourier x = (fejer11 x : ℂ) := by
  have hneg (m : ℕ) :
      Sawtooth.e (-(m : ℝ) * x) =
        (starRingEnd ℂ) (Sawtooth.e x) ^ m := by
    rw [show -(m : ℝ) * x = -((m : ℝ) * x) by ring,
      ← e_conj, e_nat_mul, map_pow]
  have hneg' (m : ℕ) :
      Sawtooth.e (-(x * (m : ℝ))) =
        (starRingEnd ℂ) (Sawtooth.e x) ^ m := by
    rw [show -(x * (m : ℝ)) = -(m : ℝ) * x by ring, hneg]
  have hneg'' (m : ℕ) :
      Sawtooth.e (-((m : ℝ) * x)) =
        (starRingEnd ℂ) (Sawtooth.e x) ^ m := by
    rw [← e_conj, e_nat_mul, map_pow]
  have hunit :
      (starRingEnd ℂ) (Sawtooth.e x) * Sawtooth.e x = 1 := by
    rw [e_conj, ← e_add]
    simp [Sawtooth.e]
  have hstar :
      (starRingEnd ℂ) (Sawtooth.e x) = (Sawtooth.e x)⁻¹ :=
    eq_inv_of_mul_eq_one_left hunit
  have he_ne : Sawtooth.e x ≠ 0 := by
    intro he
    have hn := Sawtooth.norm_e x
    rw [he, norm_zero] at hn
    norm_num at hn
  have hn2 : Sawtooth.e (-(2 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 2 := by
    (convert hneg'' 2 using 1; norm_num)
  have hn3 : Sawtooth.e (-(3 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 3 := by
    (convert hneg'' 3 using 1; norm_num)
  have hn4 : Sawtooth.e (-(4 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 4 := by
    (convert hneg'' 4 using 1; norm_num)
  have hn5 : Sawtooth.e (-(5 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 5 := by
    (convert hneg'' 5 using 1; norm_num)
  have hn6 : Sawtooth.e (-(6 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 6 := by
    (convert hneg'' 6 using 1; norm_num)
  have hn7 : Sawtooth.e (-(7 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 7 := by
    (convert hneg'' 7 using 1; norm_num)
  have hn8 : Sawtooth.e (-(8 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 8 := by
    (convert hneg'' 8 using 1; norm_num)
  have hn9 : Sawtooth.e (-(9 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 9 := by
    (convert hneg'' 9 using 1; norm_num)
  have hn10 : Sawtooth.e (-(10 * x)) =
      (starRingEnd ℂ) (Sawtooth.e x) ^ 10 := by
    (convert hneg'' 10 using 1; norm_num)
  rw [fejer11Fourier, fejer11, dirichlet11]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, map_sum]
  norm_num [Finset.sum_range_succ, Finset.sum_Icc_succ_top,
    e_nat_mul, hneg]
  rw [← e_conj x, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  rw [hstar]
  field_simp [he_ne]
  ring

/-- Integer-frequency coefficients of the Fejér kernel. -/
def fejer11Coefficient (r : ℤ) : ℝ :=
  1 - (r.natAbs : ℝ) / 11

theorem fejer11Fourier_eq_symmetric (x : ℝ) :
    fejer11Fourier x =
      ∑ r ∈ Finset.Icc (-10 : ℤ) 10,
        (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x) := by
  unfold fejer11Fourier fejer11Coefficient
  have hIcc : Finset.Icc (-10 : ℤ) 10 =
      {-10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  rw [hIcc]
  norm_num [Finset.sum_Icc_succ_top]
  rw [show Sawtooth.e 0 = 1 by simp [Sawtooth.e]]
  ring_nf

/-- The odd central Vaaler polynomial, before adding or subtracting the
Fejér error kernel. -/
noncomputable def centralCoefficient (r : ℤ) : ℂ :=
  Sawtooth.grCoefficient 10 0 r

lemma plusCoefficient_eq_central_add (r : ℤ) :
    Sawtooth.degreeTenPlusCoefficient r = centralCoefficient r +
      ((fejer11Coefficient r / 22 : ℝ) : ℂ) := by
  simp only [Sawtooth.degreeTenPlusCoefficient, centralCoefficient,
    Sawtooth.grCoefficient, fejer11Coefficient]
  push_cast
  ring

lemma minusCoefficient_eq_neg_central_add (r : ℤ) :
    Sawtooth.degreeTenMinusCoefficient r = -centralCoefficient r +
      ((fejer11Coefficient r / 22 : ℝ) : ℂ) := by
  simp only [Sawtooth.degreeTenMinusCoefficient, centralCoefficient,
    Sawtooth.grCoefficient, fejer11Coefficient]
  push_cast
  ring

theorem fejer11Fourier_eq_one_add_nonzero (x : ℝ) :
    fejer11Fourier x = 1 +
      ∑ r ∈ Sawtooth.frequencies 10,
        (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x) := by
  rw [fejer11Fourier_eq_symmetric]
  unfold Sawtooth.frequencies
  have hzero : (0 : ℤ) ∈ Finset.Icc (-10 : ℤ) 10 := by simp
  have herase :
      (∑ r ∈ (Finset.Icc (-10 : ℤ) 10).erase 0,
          (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x)) +
        (fejer11Coefficient 0 : ℂ) * Sawtooth.e (((0 : ℤ) : ℝ) * x) =
      ∑ r ∈ Finset.Icc (-10 : ℤ) 10,
        (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x) :=
    Finset.sum_erase_add (Finset.Icc (-10 : ℤ) 10)
      (fun r => (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x)) hzero
  rw [← herase]
  simp [fejer11Coefficient, Sawtooth.e]

noncomputable def centralPolynomial (x : ℝ) : ℂ :=
  Sawtooth.fourierPolynomial (Sawtooth.frequencies 10) centralCoefficient x

theorem plusPolynomial_eq_central_add_fejer (x : ℝ) :
    (((1 / 22 : ℝ) : ℂ) +
        Sawtooth.fourierPolynomial (Sawtooth.frequencies 10)
          Sawtooth.degreeTenPlusCoefficient x) =
      centralPolynomial x + (fejer11Fourier x) / 22 := by
  unfold Sawtooth.fourierPolynomial centralPolynomial
  have hsum :
      (∑ r ∈ Sawtooth.frequencies 10,
        Sawtooth.degreeTenPlusCoefficient r * Sawtooth.e ((r : ℝ) * x)) =
      ∑ r ∈ Sawtooth.frequencies 10,
        (centralCoefficient r + ((fejer11Coefficient r / 22 : ℝ) : ℂ)) *
          Sawtooth.e ((r : ℝ) * x) := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [plusCoefficient_eq_central_add]
  rw [hsum]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, fejer11Fourier_eq_one_add_nonzero]
  push_cast
  have hdiv :
      (∑ r ∈ Sawtooth.frequencies 10,
          (fejer11Coefficient r : ℂ) / 22 * Sawtooth.e ((r : ℝ) * x)) =
        (∑ r ∈ Sawtooth.frequencies 10,
          (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x)) / 22 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  rw [hdiv]
  change _ =
    (∑ r ∈ Sawtooth.frequencies 10,
      centralCoefficient r * Sawtooth.e ((r : ℝ) * x)) + _
  ring

theorem minusPolynomial_eq_neg_central_add_fejer (x : ℝ) :
    (((1 / 22 : ℝ) : ℂ) +
        Sawtooth.fourierPolynomial (Sawtooth.frequencies 10)
          Sawtooth.degreeTenMinusCoefficient x) =
      -centralPolynomial x + (fejer11Fourier x) / 22 := by
  unfold Sawtooth.fourierPolynomial centralPolynomial
  have hsum :
      (∑ r ∈ Sawtooth.frequencies 10,
        Sawtooth.degreeTenMinusCoefficient r * Sawtooth.e ((r : ℝ) * x)) =
      ∑ r ∈ Sawtooth.frequencies 10,
        (-centralCoefficient r + ((fejer11Coefficient r / 22 : ℝ) : ℂ)) *
          Sawtooth.e ((r : ℝ) * x) := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [minusCoefficient_eq_neg_central_add]
  rw [hsum]
  simp_rw [add_mul, neg_mul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    fejer11Fourier_eq_one_add_nonzero]
  push_cast
  have hdiv :
      (∑ r ∈ Sawtooth.frequencies 10,
          (fejer11Coefficient r : ℂ) / 22 * Sawtooth.e ((r : ℝ) * x)) =
        (∑ r ∈ Sawtooth.frequencies 10,
          (fejer11Coefficient r : ℂ) * Sawtooth.e ((r : ℝ) * x)) / 22 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  rw [hdiv]
  change _ =
    -(∑ r ∈ Sawtooth.frequencies 10,
      centralCoefficient r * Sawtooth.e ((r : ℝ) * x)) + _
  ring

theorem plusPolynomial_re_eq_central_add_fejer (x : ℝ) :
    (1 / 22 : ℝ) +
        (Sawtooth.fourierPolynomial (Sawtooth.frequencies 10)
          Sawtooth.degreeTenPlusCoefficient x).re =
      (centralPolynomial x).re + fejer11 x / 22 := by
  have h := congrArg Complex.re (plusPolynomial_eq_central_add_fejer x)
  rw [fejer11Fourier_eq] at h
  simpa using h

theorem minusPolynomial_re_eq_neg_central_add_fejer (x : ℝ) :
    (1 / 22 : ℝ) +
        (Sawtooth.fourierPolynomial (Sawtooth.frequencies 10)
          Sawtooth.degreeTenMinusCoefficient x).re =
      -(centralPolynomial x).re + fejer11 x / 22 := by
  have h := congrArg Complex.re (minusPolynomial_eq_neg_central_add_fejer x)
  rw [fejer11Fourier_eq] at h
  simpa using h

/-- The standard Vaaler error inequality for the odd central polynomial
immediately yields the two one-sided majorants used downstream. -/
theorem majorants_of_central_error
    (herror : ∀ x : ℝ,
      |(centralPolynomial x).re - Sawtooth.psi x| ≤ fejer11 x / 22) :
    Sawtooth.IsUpperMajorant (Sawtooth.frequencies 10) Sawtooth.psi
        (1 / 22) Sawtooth.degreeTenPlusCoefficient ∧
      Sawtooth.IsUpperMajorant (Sawtooth.frequencies 10)
        (fun x ↦ -Sawtooth.psi x) (1 / 22)
        Sawtooth.degreeTenMinusCoefficient := by
  constructor
  · intro x
    rw [plusPolynomial_re_eq_central_add_fejer]
    have h := (abs_le.mp (herror x)).1
    linarith
  · intro x
    rw [minusPolynomial_re_eq_neg_central_add_fejer]
    have h := (abs_le.mp (herror x)).2
    linarith

end FourierCoefficients
end Erdos175
