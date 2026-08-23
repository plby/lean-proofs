/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 511.
https://www.erdosproblems.com/forum/thread/511

Informal authors:
- Christian Pommerenke
- L. Huang

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos511.md
-/
/-
This is a Lean formalization of the negative solution to Erdős Problem 511.
https://www.erdosproblems.com/511

Pommerenke proved, and Huang independently rediscovered, the stronger result
that arbitrarily many components can have any prescribed diameter below 4.
Here the exact negative answer is formalized by an elementary explicit
construction at the fixed threshold 6/5, which is sufficient to refute the
proposed bound for every c > 1.
-/

import ErdosProblems.Erdos229

open Polynomial Set Topology Metric Filter

noncomputable section

namespace Erdos511

/-- The open unit lemniscate of a complex polynomial. -/
def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

lemma isOpen_lemniscate (p : Polynomial ℂ) : IsOpen (lemniscate p) := by
  exact isOpen_lt p.continuous.norm continuous_const

private def innerHalfLength : ℝ := 5 / 8

private def outerHalfLength : ℝ := 2 / 3

private def constructionRadius : ℝ := 3 / 4

private def frequency (k : ℕ) : ℕ := 100 * (k + 1)

private def centerHeight (k : ℕ) (j : Fin k) : ℝ :=
  2 * Real.pi * (j : ℝ) / frequency k

private def halfHeight (k : ℕ) : ℝ :=
  Real.pi / frequency k

private def targetEps (k : ℕ) : ℝ :=
  (Real.cosh (frequency k * innerHalfLength))⁻¹

private def target (k : ℕ) (z : ℂ) : ℂ :=
  1 - targetEps k * Complex.cosh (frequency k * z)

private def mkPoint (x y : ℝ) : ℂ :=
  (x : ℂ) + (y : ℂ) * Complex.I

private lemma frequency_pos (k : ℕ) : 0 < frequency k := by
  simp [frequency]

private lemma frequency_gt_eight_pi_mul (k : ℕ) :
    8 * Real.pi * (k : ℝ) < frequency k := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have hpi := Real.pi_lt_four
  norm_num [frequency] at *
  nlinarith

private lemma halfHeight_pos (k : ℕ) : 0 < halfHeight k := by
  exact div_pos Real.pi_pos (by exact_mod_cast frequency_pos k)

private lemma targetEps_pos (k : ℕ) : 0 < targetEps k := by
  exact inv_pos.mpr (Real.cosh_pos _)

private lemma outer_cosh_gt_two_mul_inner (k : ℕ) :
    2 * Real.cosh (frequency k * innerHalfLength) <
      Real.cosh (frequency k * outerHalfLength) := by
  let n : ℝ := frequency k
  let u : ℝ := n * innerHalfLength
  let δ : ℝ := n / 24
  have hn : 100 ≤ n := by
    dsimp [n, frequency]
    norm_num
  have hδ : 4 < δ := by
    dsimp [δ]
    linarith
  have hcoshδ : 2 < Real.cosh δ := by
    rw [Real.cosh_eq]
    have hexp := Real.add_one_le_exp δ
    have hneg := Real.exp_pos (-δ)
    nlinarith
  have hu : 0 ≤ u := by
    dsimp [u, innerHalfLength]
    positivity
  have hsum : n * outerHalfLength = u + δ := by
    dsimp [u, δ, innerHalfLength, outerHalfLength]
    ring
  rw [hsum, Real.cosh_add]
  have hcu := Real.cosh_pos u
  have hsu : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu
  have hsδ : 0 ≤ Real.sinh δ := Real.sinh_nonneg_iff.mpr (le_of_lt (lt_trans (by norm_num) hδ))
  have hmul : 2 * Real.cosh u < Real.cosh u * Real.cosh δ := by
    nlinarith [mul_pos hcu (sub_pos.mpr hcoshδ)]
  dsimp [u, n] at *
  nlinarith [mul_nonneg hsu hsδ]

private lemma targetEps_mul_outer_cosh_gt_two (k : ℕ) :
    2 < targetEps k * Real.cosh (frequency k * outerHalfLength) := by
  have hcb := Real.cosh_pos (frequency k * innerHalfLength)
  have h := outer_cosh_gt_two_mul_inner k
  rw [targetEps]
  rw [inv_mul_eq_div]
  exact (lt_div_iff₀ hcb).2 (by simpa [mul_comm] using h)

private lemma targetEps_lt_outer_cosh (k : ℕ) :
    targetEps k < Real.cosh (frequency k * outerHalfLength) := by
  have heps : targetEps k ≤ 1 := by
    rw [targetEps]
    exact (inv_le_one₀ (Real.cosh_pos _)).2 (Real.one_le_cosh _)
  have houter : 1 < Real.cosh (frequency k * outerHalfLength) := by
    rw [Real.one_lt_cosh]
    have hn : frequency k ≠ 0 := (frequency_pos k).ne'
    have hA : outerHalfLength ≠ 0 := by norm_num [outerHalfLength]
    exact mul_ne_zero (by exact_mod_cast hn) hA
  linarith

private lemma cosh_mul_mk_re (n x y : ℝ) :
    (Complex.cosh ((n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))).re =
      Real.cosh (n * x) * Real.cos (n * y) := by
  rw [mul_add, Complex.cosh_add]
  rw [show (n : ℂ) * (x : ℂ) = ((n * x : ℝ) : ℂ) by push_cast; ring]
  rw [show (n : ℂ) * ((y : ℂ) * Complex.I) =
      ((n * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I]
  rw [← Complex.ofReal_cosh (n * x), ← Complex.ofReal_sinh (n * x),
    ← Complex.ofReal_cos (n * y), ← Complex.ofReal_sin (n * y)]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

private lemma cosh_mul_mk_im (n x y : ℝ) :
    (Complex.cosh ((n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))).im =
      Real.sinh (n * x) * Real.sin (n * y) := by
  rw [mul_add, Complex.cosh_add]
  rw [show (n : ℂ) * (x : ℂ) = ((n * x : ℝ) : ℂ) by push_cast; ring]
  rw [show (n : ℂ) * ((y : ℂ) * Complex.I) =
      ((n * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I]
  rw [← Complex.ofReal_cosh (n * x), ← Complex.ofReal_sinh (n * x),
    ← Complex.ofReal_cos (n * y), ← Complex.ofReal_sin (n * y)]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

private lemma target_re (k : ℕ) (x y : ℝ) :
    (target k (mkPoint x y)).re =
      1 - targetEps k * Real.cosh (frequency k * x) *
        Real.cos (frequency k * y) := by
  simp only [target, mkPoint, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := cosh_mul_mk_re (frequency k : ℝ) x y
  norm_num at h
  rw [h]
  ring

private lemma target_im (k : ℕ) (x y : ℝ) :
    (target k (mkPoint x y)).im =
      -(targetEps k * Real.sinh (frequency k * x) *
        Real.sin (frequency k * y)) := by
  simp only [target, mkPoint, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
    Complex.mul_im, Complex.ofReal_im, zero_mul, zero_sub]
  have h := cosh_mul_mk_im (frequency k : ℝ) x y
  norm_num at h
  rw [h]
  ring

private lemma frequency_mul_centerHeight (k : ℕ) (j : Fin k) :
    (frequency k : ℝ) * centerHeight k j = (j : ℝ) * (2 * Real.pi) := by
  dsimp [centerHeight]
  field_simp [show (frequency k : ℝ) ≠ 0 by exact_mod_cast (frequency_pos k).ne']

private lemma cos_frequency_centerHeight (k : ℕ) (j : Fin k) :
    Real.cos (frequency k * centerHeight k j) = 1 := by
  rw [frequency_mul_centerHeight]
  simpa using Real.cos_nat_mul_two_pi j.val

private lemma sin_frequency_centerHeight (k : ℕ) (j : Fin k) :
    Real.sin (frequency k * centerHeight k j) = 0 := by
  rw [frequency_mul_centerHeight]
  simpa using Real.sin_add_nat_mul_two_pi 0 j.val

private lemma target_center (k : ℕ) (j : Fin k) (x : ℝ) :
    target k (mkPoint x (centerHeight k j)) =
      (1 - targetEps k * Real.cosh (frequency k * x) : ℝ) := by
  apply Complex.ext
  · change (target k (mkPoint x (centerHeight k j))).re =
      1 - targetEps k * Real.cosh (frequency k * x)
    rw [target_re, cos_frequency_centerHeight]
    ring
  · change (target k (mkPoint x (centerHeight k j))).im = 0
    rw [target_im, sin_frequency_centerHeight]
    ring

private lemma cosh_frequency_mul_le_inner {k : ℕ} {x : ℝ}
    (hx : |x| ≤ innerHalfLength) :
    Real.cosh (frequency k * x) ≤
      Real.cosh (frequency k * innerHalfLength) := by
  rw [Real.cosh_le_cosh]
  have hn : (0 : ℝ) ≤ frequency k := by positivity
  have hB : (0 : ℝ) ≤ innerHalfLength := by norm_num [innerHalfLength]
  rw [abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg hB]
  exact mul_le_mul_of_nonneg_left hx hn

private lemma target_norm_lt_one_on_core
    (k : ℕ) (j : Fin k) {x : ℝ} (hx : |x| ≤ innerHalfLength) :
    ‖target k (mkPoint x (centerHeight k j))‖ < 1 := by
  have heps := targetEps_pos k
  have hcosh := Real.cosh_pos (frequency k * x)
  have hle := cosh_frequency_mul_le_inner (k := k) hx
  have hcancel :
      targetEps k * Real.cosh (frequency k * innerHalfLength) = 1 := by
    rw [targetEps, inv_mul_cancel₀ (Real.cosh_pos _).ne']
  have htpos :
      0 < targetEps k * Real.cosh (frequency k * x) := mul_pos heps hcosh
  have htle :
      targetEps k * Real.cosh (frequency k * x) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hle heps.le]
  rw [target_center, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr htle)]
  linarith

private lemma frequency_mul_halfHeight (k : ℕ) :
    (frequency k : ℝ) * halfHeight k = Real.pi := by
  dsimp [halfHeight]
  field_simp [show (frequency k : ℝ) ≠ 0 by exact_mod_cast (frequency_pos k).ne']

private lemma cos_frequency_center_add_halfHeight (k : ℕ) (j : Fin k) :
    Real.cos (frequency k * (centerHeight k j + halfHeight k)) = -1 := by
  rw [mul_add, frequency_mul_centerHeight, frequency_mul_halfHeight]
  simpa using Real.cos_nat_mul_two_pi_add_pi j.val

private lemma cos_frequency_center_sub_halfHeight (k : ℕ) (j : Fin k) :
    Real.cos (frequency k * (centerHeight k j - halfHeight k)) = -1 := by
  rw [mul_sub, frequency_mul_centerHeight, frequency_mul_halfHeight]
  simpa using Real.cos_nat_mul_two_pi_sub_pi j.val

private lemma target_norm_gt_one_on_horizontal_add
    (k : ℕ) (j : Fin k) (x : ℝ) :
    1 < ‖target k (mkPoint x (centerHeight k j + halfHeight k))‖ := by
  have heps := targetEps_pos k
  have hcosh := Real.cosh_pos (frequency k * x)
  have hre :
      1 < (target k (mkPoint x (centerHeight k j + halfHeight k))).re := by
    rw [target_re, cos_frequency_center_add_halfHeight]
    nlinarith [mul_pos heps hcosh]
  exact hre.trans_le (Complex.re_le_norm _)

private lemma target_norm_gt_one_on_horizontal_sub
    (k : ℕ) (j : Fin k) (x : ℝ) :
    1 < ‖target k (mkPoint x (centerHeight k j - halfHeight k))‖ := by
  have heps := targetEps_pos k
  have hcosh := Real.cosh_pos (frequency k * x)
  have hre :
      1 < (target k (mkPoint x (centerHeight k j - halfHeight k))).re := by
    rw [target_re, cos_frequency_center_sub_halfHeight]
    nlinarith [mul_pos heps hcosh]
  exact hre.trans_le (Complex.re_le_norm _)

private lemma target_sq_norm_sub_one (k : ℕ) (x y : ℝ) :
    ‖target k (mkPoint x y)‖ ^ 2 - 1 =
      -2 * targetEps k * Real.cosh (frequency k * x) *
          Real.cos (frequency k * y) +
        targetEps k ^ 2 *
          (Real.sinh (frequency k * x) ^ 2 +
            Real.cos (frequency k * y) ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply, target_re, target_im]
  have htrig := Real.sin_sq_add_cos_sq (frequency k * y)
  have hhyp := Real.cosh_sq_sub_sinh_sq (frequency k * x)
  linear_combination
    targetEps k ^ 2 *
      (Real.cos (frequency k * y) ^ 2 * hhyp +
        Real.sinh (frequency k * x) ^ 2 * htrig)

private def verticalExcess (k : ℕ) : ℝ :=
  (targetEps k * Real.cosh (frequency k * outerHalfLength)) *
    (targetEps k * Real.cosh (frequency k * outerHalfLength) - 2)

private lemma verticalExcess_pos (k : ℕ) : 0 < verticalExcess k := by
  have h := targetEps_mul_outer_cosh_gt_two k
  dsimp [verticalExcess]
  positivity

private lemma target_norm_sq_sub_one_ge_verticalExcess
    (k : ℕ) {x y : ℝ} (hx : x = outerHalfLength ∨ x = -outerHalfLength) :
    verticalExcess k ≤ ‖target k (mkPoint x y)‖ ^ 2 - 1 := by
  let e := targetEps k
  let C := Real.cosh (frequency k * outerHalfLength)
  let c := Real.cos (frequency k * y)
  have he : 0 < e := targetEps_pos k
  have heC : e < C := targetEps_lt_outer_cosh k
  have hc : c ≤ 1 := Real.cos_le_one _
  have hcoshx : Real.cosh (frequency k * x) = C := by
    rcases hx with rfl | rfl
    · rfl
    · dsimp [C]
      rw [mul_neg, Real.cosh_neg]
  have hsinhx :
      Real.sinh (frequency k * x) ^ 2 =
        Real.sinh (frequency k * outerHalfLength) ^ 2 := by
    rcases hx with rfl | rfl
    · rfl
    · rw [mul_neg, Real.sinh_neg]
      ring
  have hfactor : 0 ≤ 2 * C - e * (c + 1) := by
    nlinarith
  have hdiff :
      0 ≤ e * (1 - c) * (2 * C - e * (c + 1)) := by
    positivity
  have hsq := target_sq_norm_sub_one k x y
  rw [hcoshx, hsinhx] at hsq
  have hhyp := Real.cosh_sq_sub_sinh_sq (frequency k * outerHalfLength)
  dsimp [verticalExcess, e, C, c] at *
  nlinarith

private lemma target_norm_gt_one_on_vertical
    (k : ℕ) {x y : ℝ} (hx : x = outerHalfLength ∨ x = -outerHalfLength) :
    1 < ‖target k (mkPoint x y)‖ := by
  have hge := target_norm_sq_sub_one_ge_verticalExcess k (y := y) hx
  have hpos := verticalExcess_pos k
  have hnorm := norm_nonneg (target k (mkPoint x y))
  nlinarith

private def boxGauge (k : ℕ) (j : Fin k) (z : ℂ) : ℝ :=
  max (|z.re| / outerHalfLength)
    (|z.im - centerHeight k j| / halfHeight k)

private lemma continuous_boxGauge (k : ℕ) (j : Fin k) :
    Continuous (boxGauge k j) := by
  unfold boxGauge
  fun_prop

private lemma target_norm_gt_one_on_boxGauge_eq_one
    (k : ℕ) (j : Fin k) {z : ℂ} (hz : boxGauge k j z = 1) :
    1 < ‖target k z‖ := by
  let a := |z.re| / outerHalfLength
  let b := |z.im - centerHeight k j| / halfHeight k
  have hor : a = 1 ∨ b = 1 := by
    by_cases hab : a ≤ b
    · right
      calc
        b = max a b := (max_eq_right hab).symm
        _ = 1 := hz
    · left
      have hba : b ≤ a := le_of_not_ge hab
      calc
        a = max a b := (max_eq_left hba).symm
        _ = 1 := hz
  rcases hor with ha | hb
  · have hA : (0 : ℝ) < outerHalfLength := by norm_num [outerHalfLength]
    have habs : |z.re| = outerHalfLength := by
      dsimp [a] at ha
      calc
        |z.re| = (|z.re| / outerHalfLength) * outerHalfLength := by
          field_simp
        _ = outerHalfLength := by rw [ha, one_mul]
    have hx : z.re = outerHalfLength ∨ z.re = -outerHalfLength := by
      by_cases hre : 0 ≤ z.re
      · left
        simpa [abs_of_nonneg hre] using habs
      · right
        have hre' : z.re ≤ 0 := le_of_not_ge hre
        rw [abs_of_nonpos hre'] at habs
        linarith
    rw [← Complex.re_add_im z]
    exact target_norm_gt_one_on_vertical k hx
  · have hh : (0 : ℝ) < halfHeight k := halfHeight_pos k
    have habs : |z.im - centerHeight k j| = halfHeight k := by
      dsimp [b] at hb
      calc
        |z.im - centerHeight k j| =
            (|z.im - centerHeight k j| / halfHeight k) * halfHeight k := by
          field_simp
        _ = halfHeight k := by rw [hb, one_mul]
    by_cases him : 0 ≤ z.im - centerHeight k j
    · have hy : z.im = centerHeight k j + halfHeight k := by
        rw [abs_of_nonneg him] at habs
        linarith
      rw [← Complex.re_add_im z, hy]
      exact target_norm_gt_one_on_horizontal_add k j z.re
    · have him' : z.im - centerHeight k j ≤ 0 := le_of_not_ge him
      have hy : z.im = centerHeight k j - halfHeight k := by
        rw [abs_of_nonpos him'] at habs
        linarith
      rw [← Complex.re_add_im z, hy]
      exact target_norm_gt_one_on_horizontal_sub k j z.re

private lemma abs_centerHeight_add_halfHeight_lt_quarter
    (k : ℕ) (j : Fin k) :
    |centerHeight k j| + halfHeight k < 1 / 4 := by
  have hn : (0 : ℝ) < frequency k := by exact_mod_cast frequency_pos k
  have hc : 0 ≤ centerHeight k j := by
    dsimp [centerHeight]
    positivity
  rw [abs_of_nonneg hc]
  have hjNat : 2 * j.val + 1 ≤ 2 * k := by omega
  have hj : (2 : ℝ) * (j : ℝ) + 1 ≤ 2 * (k : ℝ) := by exact_mod_cast hjNat
  have hnum :
      2 * Real.pi * (j : ℝ) + Real.pi ≤ 2 * Real.pi * (k : ℝ) := by
    nlinarith [Real.pi_pos]
  have hratio : 2 * Real.pi * (k : ℝ) / frequency k < 1 / 4 := by
    rw [div_lt_iff₀ hn]
    have hfreq := frequency_gt_eight_pi_mul k
    nlinarith
  calc
    centerHeight k j + halfHeight k =
        (2 * Real.pi * (j : ℝ) + Real.pi) / frequency k := by
          simp only [centerHeight, halfHeight]
          ring
    _ ≤ 2 * Real.pi * (k : ℝ) / frequency k :=
      (div_le_div_iff_of_pos_right hn).2 hnum
    _ < 1 / 4 := hratio

private lemma boxGauge_le_one_mem_closedBall
    (k : ℕ) (j : Fin k) {z : ℂ} (hz : boxGauge k j z ≤ 1) :
    z ∈ Metric.closedBall (0 : ℂ) constructionRadius := by
  have hA : (0 : ℝ) < outerHalfLength := by norm_num [outerHalfLength]
  have hh : (0 : ℝ) < halfHeight k := halfHeight_pos k
  have hreDiv : |z.re| / outerHalfLength ≤ 1 := by
    exact (le_max_left _ _).trans hz
  have himDiv : |z.im - centerHeight k j| / halfHeight k ≤ 1 := by
    exact (le_max_right _ _).trans hz
  have hre : |z.re| ≤ outerHalfLength := by
    have := (div_le_iff₀ hA).1 hreDiv
    simpa using this
  have himCenter : |z.im - centerHeight k j| ≤ halfHeight k := by
    have := (div_le_iff₀ hh).1 himDiv
    simpa using this
  have himTriangle :
      |z.im| ≤ |z.im - centerHeight k j| + |centerHeight k j| := by
    have := abs_add_le (z.im - centerHeight k j) (centerHeight k j)
    simpa only [sub_add_cancel] using this
  have him : |z.im| < 1 / 4 := by
    have hc := abs_centerHeight_add_halfHeight_lt_quarter k j
    linarith
  have hreSq : z.re ^ 2 ≤ outerHalfLength ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hA.le] using hre
  have himSq : z.im ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    simpa using him
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖z‖ ^ 2 < constructionRadius ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [outerHalfLength, constructionRadius] at hreSq ⊢
    nlinarith
  exact le_of_lt ((sq_lt_sq₀ (norm_nonneg z) (by norm_num [constructionRadius])).1 hsq)

private lemma target_norm_le_one_sub_eps_on_core
    (k : ℕ) (j : Fin k) {x : ℝ} (hx : |x| ≤ innerHalfLength) :
    ‖target k (mkPoint x (centerHeight k j))‖ ≤ 1 - targetEps k := by
  have heps := targetEps_pos k
  have hcosh_one := Real.one_le_cosh (frequency k * x)
  have hle := cosh_frequency_mul_le_inner (k := k) hx
  have hcancel :
      targetEps k * Real.cosh (frequency k * innerHalfLength) = 1 := by
    rw [targetEps, inv_mul_cancel₀ (Real.cosh_pos _).ne']
  have ht_lower :
      targetEps k ≤ targetEps k * Real.cosh (frequency k * x) := by
    nlinarith [mul_nonneg heps.le (sub_nonneg.mpr hcosh_one)]
  have ht_upper :
      targetEps k * Real.cosh (frequency k * x) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hle heps.le]
  rw [target_center, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht_upper)]
  linarith

private lemma target_norm_ge_one_add_eps_on_horizontal_add
    (k : ℕ) (j : Fin k) (x : ℝ) :
    1 + targetEps k ≤
      ‖target k (mkPoint x (centerHeight k j + halfHeight k))‖ := by
  have heps := targetEps_pos k
  have hcosh := Real.one_le_cosh (frequency k * x)
  have hre :
      1 + targetEps k ≤
        (target k (mkPoint x (centerHeight k j + halfHeight k))).re := by
    rw [target_re, cos_frequency_center_add_halfHeight]
    nlinarith [mul_nonneg heps.le (sub_nonneg.mpr hcosh)]
  exact hre.trans (Complex.re_le_norm _)

private lemma target_norm_ge_one_add_eps_on_horizontal_sub
    (k : ℕ) (j : Fin k) (x : ℝ) :
    1 + targetEps k ≤
      ‖target k (mkPoint x (centerHeight k j - halfHeight k))‖ := by
  have heps := targetEps_pos k
  have hcosh := Real.one_le_cosh (frequency k * x)
  have hre :
      1 + targetEps k ≤
        (target k (mkPoint x (centerHeight k j - halfHeight k))).re := by
    rw [target_re, cos_frequency_center_sub_halfHeight]
    nlinarith [mul_nonneg heps.le (sub_nonneg.mpr hcosh)]
  exact hre.trans (Complex.re_le_norm _)

private def verticalMargin (k : ℕ) : ℝ :=
  Real.sqrt (1 + verticalExcess k) - 1

private lemma verticalMargin_pos (k : ℕ) : 0 < verticalMargin k := by
  have hv := verticalExcess_pos k
  have hsqrt : 1 < Real.sqrt (1 + verticalExcess k) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (by linarith : 1 < 1 + verticalExcess k)
  exact sub_pos.mpr hsqrt

private lemma target_norm_ge_one_add_verticalMargin
    (k : ℕ) {x y : ℝ} (hx : x = outerHalfLength ∨ x = -outerHalfLength) :
    1 + verticalMargin k ≤ ‖target k (mkPoint x y)‖ := by
  have hge := target_norm_sq_sub_one_ge_verticalExcess k (y := y) hx
  have hsq :
      1 + verticalExcess k ≤ ‖target k (mkPoint x y)‖ ^ 2 := by
    linarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg (target k (mkPoint x y)))] at hsqrt
  dsimp [verticalMargin]
  convert hsqrt using 1 <;> ring

private def barrierMargin (k : ℕ) : ℝ :=
  min (targetEps k) (verticalMargin k)

private lemma barrierMargin_pos (k : ℕ) : 0 < barrierMargin k := by
  exact lt_min (targetEps_pos k) (verticalMargin_pos k)

private lemma barrierMargin_le_eps (k : ℕ) : barrierMargin k ≤ targetEps k :=
  min_le_left _ _

private lemma target_norm_ge_one_add_barrierMargin_on_boxGauge_eq_one
    (k : ℕ) (j : Fin k) {z : ℂ} (hz : boxGauge k j z = 1) :
    1 + barrierMargin k ≤ ‖target k z‖ := by
  let a := |z.re| / outerHalfLength
  let b := |z.im - centerHeight k j| / halfHeight k
  have hor : a = 1 ∨ b = 1 := by
    by_cases hab : a ≤ b
    · right
      calc
        b = max a b := (max_eq_right hab).symm
        _ = 1 := hz
    · left
      have hba : b ≤ a := le_of_not_ge hab
      calc
        a = max a b := (max_eq_left hba).symm
        _ = 1 := hz
  rcases hor with ha | hb
  · have hA : (0 : ℝ) < outerHalfLength := by norm_num [outerHalfLength]
    have habs : |z.re| = outerHalfLength := by
      dsimp [a] at ha
      calc
        |z.re| = (|z.re| / outerHalfLength) * outerHalfLength := by field_simp
        _ = outerHalfLength := by rw [ha, one_mul]
    have hx : z.re = outerHalfLength ∨ z.re = -outerHalfLength := by
      by_cases hre : 0 ≤ z.re
      · left
        simpa [abs_of_nonneg hre] using habs
      · right
        have hre' : z.re ≤ 0 := le_of_not_ge hre
        rw [abs_of_nonpos hre'] at habs
        linarith
    rw [← Complex.re_add_im z]
    have hmargin : 1 + barrierMargin k ≤ 1 + verticalMargin k := by
      simpa only [barrierMargin, add_comm] using
        add_le_add_left (min_le_right (targetEps k) (verticalMargin k)) 1
    exact hmargin.trans (target_norm_ge_one_add_verticalMargin k hx)
  · have hh : (0 : ℝ) < halfHeight k := halfHeight_pos k
    have habs : |z.im - centerHeight k j| = halfHeight k := by
      dsimp [b] at hb
      calc
        |z.im - centerHeight k j| =
            (|z.im - centerHeight k j| / halfHeight k) * halfHeight k := by
          field_simp
        _ = halfHeight k := by rw [hb, one_mul]
    by_cases him : 0 ≤ z.im - centerHeight k j
    · have hy : z.im = centerHeight k j + halfHeight k := by
        rw [abs_of_nonneg him] at habs
        linarith
      rw [← Complex.re_add_im z, hy]
      have hmargin : 1 + barrierMargin k ≤ 1 + targetEps k := by
        linarith [barrierMargin_le_eps k]
      exact hmargin.trans (target_norm_ge_one_add_eps_on_horizontal_add k j z.re)
    · have him' : z.im - centerHeight k j ≤ 0 := le_of_not_ge him
      have hy : z.im = centerHeight k j - halfHeight k := by
        rw [abs_of_nonpos him'] at habs
        linarith
      rw [← Complex.re_add_im z, hy]
      have hmargin : 1 + barrierMargin k ≤ 1 + targetEps k := by
        linarith [barrierMargin_le_eps k]
      exact hmargin.trans (target_norm_ge_one_add_eps_on_horizontal_sub k j z.re)

private lemma analyticOnNhd_target (k : ℕ) :
    AnalyticOnNhd ℂ (target k) (Metric.closedBall 0 constructionRadius) := by
  intro z hz
  unfold target
  fun_prop

private lemma exists_monic_approx_target (k : ℕ) :
    ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ z : ℂ, ‖z‖ ≤ constructionRadius →
        ‖p.eval z - target k z‖ < barrierMargin k / 2 := by
  have hm : 0 < barrierMargin k / 4 := div_pos (barrierMargin_pos k) (by norm_num)
  obtain ⟨q, hq⟩ := Erdos229.polynomial_approx_on_disk
    constructionRadius (by norm_num [constructionRadius]) (target k)
    (analyticOnNhd_target k) (barrierMargin k / 4) hm
  have hpow_tendsto : Tendsto (fun n : ℕ ↦ constructionRadius ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num [constructionRadius]) (by norm_num [constructionRadius])
  have hpow_event : ∀ᶠ n : ℕ in atTop, constructionRadius ^ n < barrierMargin k / 4 :=
    (tendsto_order.1 hpow_tendsto).2 _ hm
  obtain ⟨D, hDpow, hDdeg⟩ :=
    (hpow_event.and (eventually_gt_atTop q.natDegree)).exists
  let p : Polynomial ℂ := X ^ D + q
  have hpMonic : p.Monic := by
    dsimp [p]
    by_cases hq0 : q = 0
    · simp [hq0]
    · exact monic_X_pow_add ((natDegree_lt_iff_degree_lt hq0).mp hDdeg)
  refine ⟨p, hpMonic, ?_⟩
  intro z hz
  have hzpow : ‖z ^ D‖ ≤ constructionRadius ^ D := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg z) hz D
  have hqz := hq z hz
  dsimp [p]
  rw [eval_add, eval_pow, eval_X]
  calc
    ‖z ^ D + q.eval z - target k z‖ =
        ‖z ^ D + (q.eval z - target k z)‖ := by ring_nf
    _ ≤ ‖z ^ D‖ + ‖q.eval z - target k z‖ := norm_add_le _ _
    _ < barrierMargin k / 4 + barrierMargin k / 4 := by
      have hqz' : ‖q.eval z - target k z‖ < barrierMargin k / 4 := by
        simpa only [norm_sub_rev] using hqz
      exact add_lt_add_of_le_of_lt (le_of_lt hDpow |>.trans' hzpow) hqz'
    _ = barrierMargin k / 2 := by ring

private def coreSegment (k : ℕ) (j : Fin k) : Set ℂ :=
  (fun x : ℝ ↦ mkPoint x (centerHeight k j)) ''
    Set.Icc (-innerHalfLength) innerHalfLength

private lemma isPreconnected_coreSegment (k : ℕ) (j : Fin k) :
    IsPreconnected (coreSegment k j) := by
  exact isPreconnected_Icc.image _ (by
    unfold mkPoint
    fun_prop)

private lemma center_mem_coreSegment (k : ℕ) (j : Fin k) :
    mkPoint 0 (centerHeight k j) ∈ coreSegment k j := by
  refine ⟨0, ?_, rfl⟩
  constructor <;> norm_num [innerHalfLength]

private lemma coreSegment_gauge_le_one
    (k : ℕ) (j : Fin k) {z : ℂ} (hz : z ∈ coreSegment k j) :
    boxGauge k j z ≤ 1 := by
  rcases hz with ⟨x, hx, rfl⟩
  have hxabs : |x| ≤ innerHalfLength := by
    exact abs_le.2 ⟨by simpa using hx.1, hx.2⟩
  have hxouter : |x| / outerHalfLength ≤ 1 := by
    have hinnerOuter : innerHalfLength < outerHalfLength := by
      norm_num [innerHalfLength, outerHalfLength]
    have hA : 0 < outerHalfLength := by norm_num [outerHalfLength]
    rw [div_le_one hA]
    exact hxabs.trans (le_of_lt hinnerOuter)
  simpa [boxGauge, mkPoint] using max_le hxouter (by norm_num : (0 : ℝ) ≤ 1)

private lemma coreSegment_subset_lemniscate
    (k : ℕ) (p : Polynomial ℂ)
    (happrox : ∀ z : ℂ, ‖z‖ ≤ constructionRadius →
      ‖p.eval z - target k z‖ < barrierMargin k / 2) :
    ∀ j : Fin k, coreSegment k j ⊆ lemniscate p := by
  intro j z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hxabs : |x| ≤ innerHalfLength :=
    abs_le.2 ⟨by simpa using hx.1, hx.2⟩
  have hgauge : boxGauge k j (mkPoint x (centerHeight k j)) ≤ 1 :=
    coreSegment_gauge_le_one k j ⟨x, hx, rfl⟩
  have hball := boxGauge_le_one_mem_closedBall k j hgauge
  have happ := happrox _ (by simpa [Metric.mem_closedBall, dist_zero_right] using hball)
  have htarget := target_norm_le_one_sub_eps_on_core k j hxabs
  have hp_le :
      ‖p.eval (mkPoint x (centerHeight k j))‖ ≤
        ‖target k (mkPoint x (centerHeight k j))‖ +
          ‖p.eval (mkPoint x (centerHeight k j)) -
            target k (mkPoint x (centerHeight k j))‖ := by
    convert norm_add_le
      (target k (mkPoint x (centerHeight k j)))
      (p.eval (mkPoint x (centerHeight k j)) -
        target k (mkPoint x (centerHeight k j))) using 1 <;> ring
  change ‖p.eval (mkPoint x (centerHeight k j))‖ < 1
  calc
    ‖p.eval (mkPoint x (centerHeight k j))‖ ≤
        ‖target k (mkPoint x (centerHeight k j))‖ +
          ‖p.eval (mkPoint x (centerHeight k j)) -
            target k (mkPoint x (centerHeight k j))‖ := hp_le
    _ < (1 - targetEps k) + barrierMargin k / 2 :=
      add_lt_add_of_le_of_lt htarget happ
    _ < 1 := by
      have hm := barrierMargin_le_eps k
      have he := targetEps_pos k
      linarith

private lemma boxBoundary_disjoint_lemniscate
    (k : ℕ) (p : Polynomial ℂ)
    (happrox : ∀ z : ℂ, ‖z‖ ≤ constructionRadius →
      ‖p.eval z - target k z‖ < barrierMargin k / 2)
    (j : Fin k) {z : ℂ} (hz : boxGauge k j z = 1) :
    z ∉ lemniscate p := by
  have hball := boxGauge_le_one_mem_closedBall k j (le_of_eq hz)
  have happ := happrox z (by simpa [Metric.mem_closedBall, dist_zero_right] using hball)
  have htarget := target_norm_ge_one_add_barrierMargin_on_boxGauge_eq_one k j hz
  have htri : ‖target k z‖ ≤ ‖target k z - p.eval z‖ + ‖p.eval z‖ := by
    convert norm_add_le (target k z - p.eval z) (p.eval z) using 1 <;> ring
  have happ' : ‖target k z - p.eval z‖ < barrierMargin k / 2 := by
    simpa only [norm_sub_rev] using happ
  change ¬ ‖p.eval z‖ < 1
  linarith [barrierMargin_pos k]

private lemma connectedComponent_subset_openBox
    (k : ℕ) (p : Polynomial ℂ)
    (happrox : ∀ z : ℂ, ‖z‖ ≤ constructionRadius →
      ‖p.eval z - target k z‖ < barrierMargin k / 2)
    (j : Fin k)
    (hcenter : mkPoint 0 (centerHeight k j) ∈ lemniscate p) :
    connectedComponentIn (lemniscate p) (mkPoint 0 (centerHeight k j)) ⊆
      {z | boxGauge k j z < 1} := by
  intro z hz
  by_contra hnot
  have hzge : 1 ≤ boxGauge k j z := le_of_not_gt hnot
  have hbaseGauge : boxGauge k j (mkPoint 0 (centerHeight k j)) = 0 := by
    simp [boxGauge, mkPoint, outerHalfLength]
  have hone :
      1 ∈ Set.Icc
        (boxGauge k j (mkPoint 0 (centerHeight k j))) (boxGauge k j z) := by
    rw [hbaseGauge]
    exact ⟨by norm_num, hzge⟩
  have hiv := isPreconnected_connectedComponentIn.intermediate_value
    (mem_connectedComponentIn hcenter) hz
    (continuous_boxGauge k j).continuousOn hone
  rcases hiv with ⟨w, hwcomp, hwgauge⟩
  have hwlem := connectedComponentIn_subset (lemniscate p)
    (mkPoint 0 (centerHeight k j)) hwcomp
  exact boxBoundary_disjoint_lemniscate k p happrox j hwgauge hwlem

private lemma center_not_mem_other_openBox
    (k : ℕ) {i j : Fin k} (hij : i ≠ j) :
    ¬ boxGauge k i (mkPoint 0 (centerHeight k j)) < 1 := by
  intro hbox
  have hratio :
      |centerHeight k j - centerHeight k i| / halfHeight k < 1 := by
    have hle := le_max_right
      (|((mkPoint 0 (centerHeight k j)).re)| / outerHalfLength)
      (|((mkPoint 0 (centerHeight k j)).im - centerHeight k i)| / halfHeight k)
    have := hle.trans_lt hbox
    simpa [mkPoint] using this
  have hdist : |centerHeight k j - centerHeight k i| < halfHeight k := by
    exact (div_lt_one (halfHeight_pos k)).mp hratio
  have hn : (0 : ℝ) < frequency k := by exact_mod_cast frequency_pos k
  have hji : j.val < i.val ∨ i.val < j.val := Nat.lt_or_gt_of_ne (by
    intro h
    apply hij
    exact Fin.ext h.symm)
  rcases hji with hji | hij'
  · have hsucc : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hji
    have hsucc' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hsucc
    have hcast : (1 : ℝ) ≤ (i : ℝ) - (j : ℝ) := by
      norm_num at hsucc' ⊢
      linarith
    have hsep : 2 * halfHeight k ≤ centerHeight k i - centerHeight k j := by
      calc
        2 * halfHeight k = (2 * Real.pi) / frequency k := by
          dsimp [halfHeight]
          ring
        _ ≤ (2 * Real.pi * ((i : ℝ) - (j : ℝ))) / frequency k := by
          rw [div_le_div_iff_of_pos_right hn]
          nlinarith [Real.pi_pos]
        _ = centerHeight k i - centerHeight k j := by
          dsimp [centerHeight]
          ring
    have hsepPos : 0 < centerHeight k i - centerHeight k j :=
      lt_of_lt_of_le (mul_pos (by norm_num) (halfHeight_pos k)) hsep
    have hnonpos : centerHeight k j - centerHeight k i ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos] at hdist
    linarith [halfHeight_pos k]
  · have hsucc : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij'
    have hsucc' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hsucc
    have hcast : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
      norm_num at hsucc' ⊢
      linarith
    have hsep : 2 * halfHeight k ≤ centerHeight k j - centerHeight k i := by
      calc
        2 * halfHeight k = (2 * Real.pi) / frequency k := by
          dsimp [halfHeight]
          ring
        _ ≤ (2 * Real.pi * ((j : ℝ) - (i : ℝ))) / frequency k := by
          rw [div_le_div_iff_of_pos_right hn]
          nlinarith [Real.pi_pos]
        _ = centerHeight k j - centerHeight k i := by
          dsimp [centerHeight]
          ring
    have hsepPos : 0 < centerHeight k j - centerHeight k i :=
      lt_of_lt_of_le (mul_pos (by norm_num) (halfHeight_pos k)) hsep
    have hnonneg : 0 ≤ centerHeight k j - centerHeight k i := hsepPos.le
    rw [abs_of_nonneg hnonneg] at hdist
    linarith [halfHeight_pos k]

/-- Connected components of s, regarded as subsets of the ambient complex plane. -/
def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {C | ∃ x : s, C = Subtype.val '' (connectedComponent x : Set s)}

/-- Components of the open lemniscate whose diameter is strictly larger than d. -/
def largeComponents (p : Polynomial ℂ) (d : ℝ) : Set (Set ℂ) :=
  {C | C ∈ componentsIn (lemniscate p) ∧ d < Metric.diam C}

/-- A finite witness that the lemniscate has at least N distinct large components. -/
def HasAtLeastLargeComponents
    (p : Polynomial ℂ) (d : ℝ) (N : ℕ) : Prop :=
  ∃ C : Fin N → Set ℂ,
    Function.Injective C ∧ ∀ i, C i ∈ largeComponents p d

/--
The boundedness assertion in Erdős Problem 511.  The natural number B
depends on d, but not on the polynomial or its degree.
-/
def Erdos511Bounded : Prop :=
  ∀ d : ℝ, 1 < d →
    ∃ B : ℕ, ∀ p : Polynomial ℂ, p.Monic →
      ¬ HasAtLeastLargeComponents p d (B + 1)

/-- The strong form of the Pommerenke--Huang counterexample theorem. -/
def PommerenkeCounterexamples : Prop :=
  ∀ d : ℝ, 0 < d → d < 4 →
    ∀ N : ℕ, ∃ p : Polynomial ℂ,
      p.Monic ∧ HasAtLeastLargeComponents p d N

theorem not_erdos511Bounded_of_pommerenke
    (h : PommerenkeCounterexamples) : ¬ Erdos511Bounded := by
  intro hbounded
  obtain ⟨B, hB⟩ := hbounded 2 (by norm_num)
  obtain ⟨p, hp, hmany⟩ :=
    h 2 (by norm_num) (by norm_num) (B + 1)
  exact hB p hp hmany

/--
An explicit fixed-threshold form of the negative solution.  For every `N` we
construct a monic polynomial with at least `N` different components of its
open unit lemniscate having diameter greater than `6/5`.
-/
theorem explicit_counterexamples (N : ℕ) :
    ∃ p : Polynomial ℂ,
      p.Monic ∧ HasAtLeastLargeComponents p (6 / 5 : ℝ) N := by
  obtain ⟨p, hpMonic, happrox⟩ := exists_monic_approx_target N
  have hcore : ∀ j : Fin N, coreSegment N j ⊆ lemniscate p :=
    coreSegment_subset_lemniscate N p happrox
  let base : Fin N → ℂ := fun j ↦ mkPoint 0 (centerHeight N j)
  let C : Fin N → Set ℂ := fun j ↦ connectedComponentIn (lemniscate p) (base j)
  have hbase (j : Fin N) : base j ∈ lemniscate p := by
    exact hcore j (center_mem_coreSegment N j)
  have hcoreC (j : Fin N) : coreSegment N j ⊆ C j := by
    exact (isPreconnected_coreSegment N j).subset_connectedComponentIn
      (center_mem_coreSegment N j) (hcore j)
  have htrap (j : Fin N) : C j ⊆ {z | boxGauge N j z < 1} := by
    exact connectedComponent_subset_openBox N p happrox j (hbase j)
  have hcomponent (j : Fin N) : C j ∈ componentsIn (lemniscate p) := by
    refine ⟨⟨base j, hbase j⟩, ?_⟩
    dsimp [C]
    exact connectedComponentIn_eq_image (hbase j)
  have hCinjective : Function.Injective C := by
    intro i j hij
    by_contra hne
    have hjCj : base j ∈ C j := mem_connectedComponentIn (hbase j)
    have hjCi : base j ∈ C i := by rwa [hij]
    have hjBox := htrap i hjCi
    exact center_not_mem_other_openBox N hne hjBox
  have hlarge (j : Fin N) : C j ∈ largeComponents p (6 / 5 : ℝ) := by
    refine ⟨hcomponent j, ?_⟩
    let left : ℂ := mkPoint (-innerHalfLength) (centerHeight N j)
    let right : ℂ := mkPoint innerHalfLength (centerHeight N j)
    have hleftCore : left ∈ coreSegment N j := by
      refine ⟨-innerHalfLength, ?_, rfl⟩
      constructor
      · exact le_rfl
      · norm_num [innerHalfLength]
    have hrightCore : right ∈ coreSegment N j := by
      refine ⟨innerHalfLength, ?_, rfl⟩
      constructor
      · norm_num [innerHalfLength]
      · exact le_rfl
    have hleft : left ∈ C j := hcoreC j hleftCore
    have hright : right ∈ C j := hcoreC j hrightCore
    have hCball : C j ⊆ Metric.closedBall (0 : ℂ) constructionRadius := by
      intro z hz
      exact boxGauge_le_one_mem_closedBall N j (le_of_lt (htrap j hz))
    have hbounded : Bornology.IsBounded (C j) :=
      Metric.isBounded_closedBall.subset hCball
    have hdist : dist left right = (5 / 4 : ℝ) := by
      dsimp [left, right]
      norm_num [mkPoint, innerHalfLength, Complex.dist_eq,
        Complex.norm_def, Complex.normSq]
    have hdiam := Metric.dist_le_diam_of_mem hbounded hleft hright
    rw [hdist] at hdiam
    norm_num at hdiam ⊢
    linarith
  exact ⟨p, hpMonic, ⟨C, hCinjective, hlarge⟩⟩

/-- The exact boundedness assertion in Erdős Problem 511 is false. -/
theorem erdos_511 : ¬ Erdos511Bounded := by
  intro hbounded
  obtain ⟨B, hB⟩ := hbounded (6 / 5 : ℝ) (by norm_num)
  obtain ⟨p, hp, hmany⟩ := explicit_counterexamples (B + 1)
  exact hB p hp hmany

end Erdos511

#print axioms Erdos511.erdos_511
