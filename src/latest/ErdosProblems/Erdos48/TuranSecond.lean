/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
# Turan's second main theorem: the radial separation step

The second main theorem for power sums chooses a circle which is uniformly
separated, in product, from all root moduli.  The key real-variable input is
the extremal property of the Chebyshev polynomial.  This file proves that
input first on `[-1,1]` and then on an arbitrary nondegenerate interval.

The normalization is intentionally exact.  For `K` points the product gap on
an interval of half-length `h` is at least
`h^K / 2^(K-1)`.  On the interval `[16/17,1]` used by the detector this is
`2 / 68^K`.
-/

namespace Erdos48

open Polynomial Set
open scoped BigOperators Polynomial

noncomputable section

/-- A monic real polynomial of positive degree has magnitude at least
`2^(1-K)` somewhere on `[-1,1]`.  This is the product form of Chebyshev's
extremal theorem. -/
theorem exists_unitInterval_prod_abs_ge_chebyshev
    {K : ℕ} (hK : 0 < K) (u : Fin K → ℝ) :
    ∃ y ∈ Set.Icc (-1 : ℝ) 1,
      ((2 : ℝ) ^ (K - 1))⁻¹ ≤ ∏ i, |y - u i| := by
  let P : ℝ[X] := ∏ i : Fin K, (X - C (u i))
  let A : ℝ := (2 : ℝ) ^ (K - 1)
  let Q : ℝ[X] := C A * P
  have hPmonic : P.Monic := by
    simpa only [P] using
      Polynomial.monic_prod_X_sub_C u (Finset.univ : Finset (Fin K))
  have hPnat : P.natDegree = K := by
    dsimp [P]
    simpa using Polynomial.natDegree_finsetProd_X_sub_C_eq_card
      (s := Finset.univ) u
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAnz : A ≠ 0 := hApos.ne'
  have hQnat : Q.natDegree = K := by
    dsimp [Q]
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hAnz)
      hPmonic.ne_zero, Polynomial.natDegree_C, zero_add, hPnat]
  have hQdeg : Q.degree ≤ (K : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree]
    · simp [hQnat]
    · dsimp [Q]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hAnz) hPmonic.ne_zero
  have hQcoeff : Q.coeff K = (2 : ℝ) ^ (K - 1) := by
    have hPcoeff : P.coeff K = 1 := by
      rw [← hPnat]
      exact hPmonic.coeff_natDegree
    dsimp [Q]
    rw [Polynomial.coeff_C_mul, hPcoeff]
    simp [A]
  by_contra hnot
  push_neg at hnot
  have hbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |Q.eval y| ≤ 1 := by
    intro y hy
    have hlt := hnot y hy
    have hPeval : |P.eval y| = ∏ i, |y - u i| := by
      dsimp [P]
      rw [Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Finset.abs_prod]
    have hQeval : |Q.eval y| = A * |P.eval y| := by
      dsimp [Q]
      rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_of_pos hApos]
    rw [hQeval, hPeval]
    have hscaled := mul_lt_mul_of_pos_left hlt hApos
    have hcancel : A * A⁻¹ = 1 := mul_inv_cancel₀ hAnz
    linarith
  have hQT : Q = Polynomial.Chebyshev.T ℝ K :=
    (Polynomial.Chebyshev.coeff_eq_iff_of_forall_abs_le_one
      hQdeg hbound).mp hQcoeff
  have hone : |Q.eval 1| = 1 := by
    have hnode := Polynomial.Chebyshev.eval_T_real_node
      (n := K) (i := 0) (Finset.mem_Iic.mpr hK.le)
    simpa [hQT, Polynomial.Chebyshev.node_eq_one] using congrArg abs hnode
  have hlt := hnot 1 (by simp)
  have hPeval : |P.eval 1| = ∏ i, |1 - u i| := by
    dsimp [P]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.abs_prod]
  have hQeval : |Q.eval 1| = A * |P.eval 1| := by
    dsimp [Q]
    rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_of_pos hApos]
  have hone' : A * (∏ i, |1 - u i|) = 1 := by
    rw [← hPeval, ← hQeval]
    exact hone
  have hscaled := mul_lt_mul_of_pos_left hlt hApos
  rw [mul_inv_cancel₀ hAnz] at hscaled
  linarith

/-- Affine interval form of the Chebyshev product gap. -/
theorem exists_interval_prod_abs_ge_chebyshev
    {K : ℕ} (hK : 0 < K) (u : Fin K → ℝ)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Icc a b,
      ((b - a) / 2) ^ K * ((2 : ℝ) ^ (K - 1))⁻¹ ≤
        ∏ i, |r - u i| := by
  let h : ℝ := (b - a) / 2
  let c : ℝ := (a + b) / 2
  let v : Fin K → ℝ := fun i ↦ (u i - c) / h
  have hh : 0 < h := by dsimp [h]; linarith
  obtain ⟨y, hy, hgap⟩ :=
    exists_unitInterval_prod_abs_ge_chebyshev hK v
  let r : ℝ := c + h * y
  have hr : r ∈ Set.Icc a b := by
    have hy' := hy
    dsimp [r, c, h]
    constructor <;> nlinarith [hy'.1, hy'.2]
  refine ⟨r, hr, ?_⟩
  have hterm : ∀ i : Fin K, |r - u i| = h * |y - v i| := by
    intro i
    have hid : r - u i = h * (y - v i) := by
      dsimp [r, v, c]
      field_simp [hh.ne']
      ring
    rw [hid, abs_mul, abs_of_pos hh]
  calc
    ((b - a) / 2) ^ K * ((2 : ℝ) ^ (K - 1))⁻¹ =
        h ^ K * ((2 : ℝ) ^ (K - 1))⁻¹ := rfl
    _ ≤ h ^ K * ∏ i, |y - v i| :=
      mul_le_mul_of_nonneg_left hgap (pow_nonneg hh.le _)
    _ = ∏ i, |r - u i| := by
      simp_rw [hterm]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]

/-- Numerical specialization used in the zero detector. -/
theorem exists_sixteenSeventeenths_prod_abs_gap
    {K : ℕ} (hK : 0 < K) (u : Fin K → ℝ) :
    ∃ r ∈ Set.Icc (16 / 17 : ℝ) 1,
      2 * (68 : ℝ)⁻¹ ^ K ≤ ∏ i, |r - u i| := by
  obtain ⟨r, hr, hgap⟩ := exists_interval_prod_abs_ge_chebyshev
    hK u (show (16 / 17 : ℝ) < 1 by norm_num)
  refine ⟨r, hr, ?_⟩
  calc
    2 * (68 : ℝ)⁻¹ ^ K =
        ((1 - 16 / 17 : ℝ) / 2) ^ K *
          ((2 : ℝ) ^ (K - 1))⁻¹ := by
      have hKsucc : K - 1 + 1 = K := by omega
      have htwo :
          (2 : ℝ) * (2 : ℝ)⁻¹ ^ K = (2 : ℝ)⁻¹ ^ (K - 1) := by
        rw [← hKsucc, pow_succ]
        norm_num
        ring
      rw [show (1 - 16 / 17 : ℝ) / 2 = (34 : ℝ)⁻¹ by norm_num,
        ← inv_pow]
      calc
        2 * (68 : ℝ)⁻¹ ^ K =
            2 * (((2 : ℝ)⁻¹ * (34 : ℝ)⁻¹) ^ K) := by norm_num
        _ = 2 * ((2 : ℝ)⁻¹ ^ K * (34 : ℝ)⁻¹ ^ K) := by rw [mul_pow]
        _ = (34 : ℝ)⁻¹ ^ K * ((2 : ℝ) * (2 : ℝ)⁻¹ ^ K) := by ring
        _ = (34 : ℝ)⁻¹ ^ K * (2 : ℝ)⁻¹ ^ (K - 1) := by rw [htwo]
    _ ≤ ∏ i, |r - u i| := hgap

/-! ## The inside/outside Cauchy coefficient

The contour coefficient used in Turan's second theorem contains a negative
power.  The following finite recurrence evaluates its Cauchy kernel without
appealing to a general residue theorem: the pole at zero cancels the pole at
`z` when `z` is inside the circle, while an outside point contributes the
negative reciprocal power. -/

private lemma CircleIntegrable.const_mul_complex
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (a : ℂ) :
    CircleIntegrable (fun z ↦ a * f z) c r := by
  unfold CircleIntegrable at hf ⊢
  simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using hf.const_mul a

private lemma circleIntegrable_invPow_div_sub
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : ‖z‖ ≠ r) (N : ℕ) :
    CircleIntegrable (fun ζ : ℂ ↦ (ζ⁻¹) ^ N / (ζ - z)) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.div
  · apply ContinuousOn.pow
    apply ContinuousOn.inv₀ continuousOn_id
    intro ζ hζ hζ0
    have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
    change ζ = 0 at hζ0
    rw [hζ0, norm_zero] at this
    linarith
  · exact continuousOn_id.sub continuousOn_const
  · intro ζ hζ hzero
    have hζz : ζ = z := sub_eq_zero.mp hzero
    have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
    exact hzr (hζz ▸ this)

private lemma circleIntegrable_invPow
    {r : ℝ} (hr : 0 < r) (N : ℕ) :
    CircleIntegrable (fun ζ : ℂ ↦ (ζ⁻¹) ^ N) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀ continuousOn_id
  intro ζ hζ hζ0
  have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
  change ζ = 0 at hζ0
  rw [hζ0, norm_zero] at this
  linarith

private lemma circleIntegral_invPow_succ_eq_zero
    {r : ℝ} (_hr : 0 < r) (N : ℕ) :
    (∮ ζ in C(0, r), (ζ⁻¹) ^ (N + 2)) = 0 := by
  have h := circleIntegral.integral_sub_zpow_of_ne
    (show (-((N + 2 : ℕ) : ℤ)) ≠ -1 by omega) (0 : ℂ) 0 r
  rw [show (fun ζ : ℂ ↦ (ζ⁻¹) ^ (N + 2)) =
      fun ζ ↦ (ζ - 0) ^ (-((N + 2 : ℕ) : ℤ)) by
    funext ζ
    rw [sub_zero, zpow_neg, zpow_natCast, inv_pow]]
  exact h

private lemma circleIntegral_invPow_div_sub_zero_of_lt
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r < ‖z‖) :
    (∮ ζ in C(0, r), (ζ - z)⁻¹) = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero hr.le
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (0 : ℂ) hr.ne']
  intro ζ hζ
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.inv
  · fun_prop
  · intro hzero
    have hζz : ζ = z := sub_eq_zero.mp hzero
    have hnorm : ‖ζ‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hζ
    rw [hζz] at hnorm
    linarith

private lemma circleIntegral_invPow_div_sub
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0)
    (hzr : ‖z‖ ≠ r) (M : ℕ) :
    (∮ ζ in C(0, r), (ζ⁻¹) ^ (M + 1) / (ζ - z)) =
      if ‖z‖ < r then 0 else
        -(2 * (Real.pi : ℂ) * Complex.I) * (z⁻¹) ^ (M + 1) := by
  induction M with
  | zero =>
      have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
          ζ⁻¹ / (ζ - z) = z⁻¹ * (ζ - z)⁻¹ - z⁻¹ * ζ⁻¹ := by
        intro ζ hζ
        have hζne : ζ ≠ 0 := by
          intro hzero
          have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
          rw [hzero, norm_zero] at this
          linarith
        have hsub : ζ - z ≠ 0 := by
          intro hzero
          have hζz : ζ = z := sub_eq_zero.mp hzero
          have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
          exact hzr (hζz ▸ this)
        field_simp [hζne, hz, hsub]
        ring
      simp only [zero_add, pow_one]
      rw [circleIntegral.integral_congr hr.le hpoint]
      have hintF : CircleIntegrable
          (fun ζ : ℂ ↦ z⁻¹ * (ζ - z)⁻¹) 0 r := by
        simpa using CircleIntegrable.const_mul_complex
          (circleIntegrable_invPow_div_sub hr hzr 0) z⁻¹
      have hintJ : CircleIntegrable
          (fun ζ : ℂ ↦ z⁻¹ * ζ⁻¹) 0 r := by
        simpa using CircleIntegrable.const_mul_complex
          (circleIntegrable_invPow hr 1) z⁻¹
      rw [circleIntegral.integral_sub hintF hintJ]
      simp only [circleIntegral.integral_const_mul]
      have hJ : (∮ ζ in C(0, r), ζ⁻¹) =
          2 * (Real.pi : ℂ) * Complex.I := by
        simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
      rw [hJ]
      split_ifs with hzin
      · rw [circleIntegral.integral_sub_inv_of_mem_ball]
        · ring
        · simpa [Metric.mem_ball, dist_zero_right] using hzin
      · have hzout : r < ‖z‖ := lt_of_le_of_ne (le_of_not_gt hzin) hzr.symm
        rw [circleIntegral_invPow_div_sub_zero_of_lt hr hzout]
        ring
  | succ M ih =>
      have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
          (ζ⁻¹) ^ (M + 2) / (ζ - z) =
            z⁻¹ * ((ζ⁻¹) ^ (M + 1) / (ζ - z)) -
              z⁻¹ * (ζ⁻¹) ^ (M + 2) := by
        intro ζ hζ
        have hζne : ζ ≠ 0 := by
          intro hzero
          have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
          rw [hzero, norm_zero] at this
          linarith
        have hsub : ζ - z ≠ 0 := by
          intro hzero
          have hζz : ζ = z := sub_eq_zero.mp hzero
          have : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
          exact hzr (hζz ▸ this)
        field_simp [hζne, hz, hsub]
        have hpow : (1 / ζ : ℂ) ^ (M + 2) * ζ =
            (1 / ζ : ℂ) ^ (M + 1) := by
          rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
          field_simp
        rw [← hpow]
        ring
      rw [show M + 1 + 1 = M + 2 by omega]
      rw [circleIntegral.integral_congr hr.le hpoint]
      have hintF : CircleIntegrable
          (fun ζ : ℂ ↦ z⁻¹ * ((ζ⁻¹) ^ (M + 1) / (ζ - z))) 0 r := by
        exact CircleIntegrable.const_mul_complex
          (circleIntegrable_invPow_div_sub hr hzr (M + 1)) z⁻¹
      have hintJ : CircleIntegrable
          (fun ζ : ℂ ↦ z⁻¹ * (ζ⁻¹) ^ (M + 2)) 0 r := by
        exact CircleIntegrable.const_mul_complex
          (circleIntegrable_invPow hr (M + 2)) z⁻¹
      rw [circleIntegral.integral_sub hintF hintJ]
      simp only [circleIntegral.integral_const_mul]
      rw [ih, circleIntegral_invPow_succ_eq_zero hr M]
      split_ifs <;> ring

private lemma turanRootPolynomial_norm_ge_radialProduct
    {K : ℕ} (w : Fin K → ℂ) {r : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = r) :
    (∏ j, |r - ‖w j‖|) ≤ ‖(turanRootPolynomial w).eval ζ‖ := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_prod]
  apply Finset.prod_le_prod
  · intro j hj
    exact abs_nonneg _
  · intro j hj
    simpa only [hζ] using abs_norm_sub_norm_le ζ (w j)

private lemma turanDividedCoeff_norm_le_unitCircle
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    (i : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
      (K + 1 : ℝ) * (2 : ℝ) ^ K := by
  rw [turanDividedCoeff]
  calc
    ‖∑ d ∈ Finset.range (K + 1),
        if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ ≤
        ∑ d ∈ Finset.range (K + 1),
          ‖if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (K + 1), (2 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with hid
      · rw [norm_mul, norm_pow]
        have hcoeff := turanRootPolynomial_coeff_norm_le_choose w hw d
        have hchoose : (K.choose d : ℝ) ≤ (2 : ℝ) ^ K := by
          exact_mod_cast Nat.choose_le_two_pow K d
        have hpow : ‖ζ‖ ^ (d - 1 - i) ≤ 1 := by
          exact pow_le_one₀ (norm_nonneg ζ) hζ
        nlinarith [norm_nonneg ((turanRootPolynomial w).coeff d),
          pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) K]
      · simp [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ = (K + 1 : ℝ) * (2 : ℝ) ^ K := by simp

private noncomputable def turanSecondCoeff
    {K : ℕ} (w : Fin K → ℂ) (r : ℝ) (M i : ℕ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∮ ζ in C(0, r),
      (ζ⁻¹) ^ (M + 1) * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ

private lemma turanSecondIntegrand_circleIntegrable
    {K : ℕ} (w : Fin K → ℂ) {r D : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hgap : D ≤ ∏ j, |r - ‖w j‖|) (M i : ℕ) :
    CircleIntegrable
      (fun ζ ↦ (ζ⁻¹) ^ (M + 1) *
        turanDividedCoeff (turanRootPolynomial w) K i ζ /
          (turanRootPolynomial w).eval ζ) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · apply ContinuousOn.pow
      apply ContinuousOn.inv₀ continuousOn_id
      intro ζ hζ hzero
      change ζ = 0 at hzero
      have hnorm : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
      rw [hzero, norm_zero] at hnorm
      linarith
    · unfold turanDividedCoeff
      exact (continuous_finsetSum _ fun d hd ↦ by
        by_cases hid : i < d
        · simp only [hid, if_true]
          fun_prop
        · simp only [hid, if_false]
          fun_prop).continuousOn
  · fun_prop
  · intro ζ hζ hzero
    have hnorm : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
    have hP := (hgap.trans
      (turanRootPolynomial_norm_ge_radialProduct w hnorm))
    rw [hzero, norm_zero] at hP
    linarith

private lemma turanSecondCoeff_norm_le
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    {r D : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hD : 0 < D)
    (hgap : D ≤ ∏ j, |r - ‖w j‖|) (M i : ℕ) :
    ‖turanSecondCoeff w r M i‖ ≤
      r * ((r⁻¹) ^ (M + 1) * ((K + 1 : ℝ) * (2 : ℝ) ^ K) / D) := by
  unfold turanSecondCoeff
  rw [neg_smul, norm_neg]
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
  intro ζ hζ
  have hζnorm : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
  have hP : D ≤ ‖(turanRootPolynomial w).eval ζ‖ :=
    hgap.trans (turanRootPolynomial_norm_ge_radialProduct w hζnorm)
  have hq := turanDividedCoeff_norm_le_unitCircle w hw i
    (hζnorm.trans_le hr1)
  rw [norm_div, norm_mul, norm_pow, norm_inv, hζnorm]
  apply div_le_div₀
  · positivity
  · exact mul_le_mul_of_nonneg_left hq (by positivity)
  · exact hD
  · exact hP

private lemma turanSecondCoeff_interpolates
    {K : ℕ} (w : Fin K → ℂ) (hw0 : ∀ j, w j ≠ 0)
    {r D : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hgap : D ≤ ∏ j, |r - ‖w j‖|) (M : ℕ) (j : Fin K) :
    ∑ i ∈ Finset.range K, turanSecondCoeff w r M i * w j ^ i =
      if ‖w j‖ < r then 0 else (w j)⁻¹ ^ (M + 1) := by
  let P : ℂ[X] := turanRootPolynomial w
  let c₀ : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)⁻¹
  let g : ℕ → ℂ → ℂ := fun i ζ ↦
    (ζ⁻¹) ^ (M + 1) * turanDividedCoeff P K i ζ / P.eval ζ
  have hsep : ∀ k, ‖w k‖ ≠ r := by
    intro k heq
    have hprodZero : (∏ j, |r - ‖w j‖|) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [heq, sub_self, abs_zero]
    rw [hprodZero] at hgap
    linarith
  have hint : ∀ i ∈ Finset.range K, CircleIntegrable (g i) 0 r := by
    intro i hi
    simpa only [g, P] using
      turanSecondIntegrand_circleIntegrable w hr hD hgap M i
  have hintMul : ∀ i ∈ Finset.range K,
      CircleIntegrable (fun ζ ↦ g i ζ * w j ^ i) 0 r := by
    intro i hi
    have h := hint i hi
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 r θ) * w j ^ i)
        MeasureTheory.volume 0 (2 * Real.pi)
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 r θ))
        MeasureTheory.volume 0 (2 * Real.pi) at h
    exact h.mul_const (w j ^ i)
  have hsumIntegral :
      (∮ ζ in C(0, r), ∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
        ∑ i ∈ Finset.range K, ∮ ζ in C(0, r), g i ζ * w j ^ i :=
    circleIntegral.integral_fun_sum hintMul
  have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
        (ζ⁻¹) ^ (M + 1) / (ζ - w j) := by
    intro ζ hζ
    have hζnorm : ‖ζ‖ = r := by simpa [Metric.mem_sphere] using hζ
    have hPnorm : D ≤ ‖P.eval ζ‖ := by
      dsimp [P]
      exact hgap.trans (turanRootPolynomial_norm_ge_radialProduct w hζnorm)
    have hPne : P.eval ζ ≠ 0 :=
      norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hD hPnorm))
    have hζwj : ζ - w j ≠ 0 := by
      intro hzero
      have heq : ζ = w j := sub_eq_zero.mp hzero
      exact hsep j (heq ▸ hζnorm)
    have hroot : P.eval (w j) = 0 := by
      exact turanRootPolynomial_eval_root w j
    have hid := turanDividedCoeff_sum_identity P
      (by dsimp [P]; rw [turanRootPolynomial_natDegree]) ζ (w j)
    rw [hroot, sub_zero] at hid
    have hqsum : (∑ i ∈ Finset.range K,
        turanDividedCoeff P K i ζ * w j ^ i) = P.eval ζ / (ζ - w j) := by
      apply (eq_div_iff hζwj).2
      simpa only [mul_comm] using hid
    calc
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
          ((ζ⁻¹) ^ (M + 1) / P.eval ζ) *
            ∑ i ∈ Finset.range K,
              turanDividedCoeff P K i ζ * w j ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [g]
        field_simp
      _ = ((ζ⁻¹) ^ (M + 1) / P.eval ζ) *
          (P.eval ζ / (ζ - w j)) := by rw [hqsum]
      _ = (ζ⁻¹) ^ (M + 1) / (ζ - w j) := by field_simp
  calc
    (∑ i ∈ Finset.range K, turanSecondCoeff w r M i * w j ^ i) =
        ∑ i ∈ Finset.range K,
          c₀ * ((∮ ζ in C(0, r), g i ζ) * w j ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [turanSecondCoeff, c₀, g, P, smul_eq_mul, mul_assoc]
    _ = c₀ * ∑ i ∈ Finset.range K,
        (∮ ζ in C(0, r), g i ζ) * w j ^ i := by rw [Finset.mul_sum]
    _ = c₀ * ∑ i ∈ Finset.range K,
        ∮ ζ in C(0, r), g i ζ * w j ^ i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∮ ζ in C(0, r), g i ζ) * w j ^ i =
          w j ^ i * ∮ ζ in C(0, r), g i ζ by ring,
        ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hr.le
      intro ζ hζ
      ring
    _ = c₀ * ∮ ζ in C(0, r),
        ∑ i ∈ Finset.range K, g i ζ * w j ^ i := by rw [hsumIntegral]
    _ = c₀ * ∮ ζ in C(0, r),
        (ζ⁻¹) ^ (M + 1) / (ζ - w j) := by
      congr 1
      apply circleIntegral.integral_congr hr.le
      exact hpoint
    _ = if ‖w j‖ < r then 0 else (w j)⁻¹ ^ (M + 1) := by
      rw [circleIntegral_invPow_div_sub hr (hw0 j) (hsep j) M]
      dsimp [c₀]
      split_ifs <;> simp
      have hconst : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp
      rw [Complex.I_sq]
      ring

/-- The explicit coefficient loss in the positive-weight form of Turan's
second main theorem. -/
noncomputable def turanSecondLoss (K M : ℕ) : ℝ :=
  (K : ℝ) * (((17 / 16 : ℝ) ^ M *
    ((K + 1 : ℝ) * (2 : ℝ) ^ K) /
      (2 * (68 : ℝ)⁻¹ ^ K)))

theorem turanSecondLoss_pos {K M : ℕ} (hK : 0 < K) :
    0 < turanSecondLoss K M := by
  unfold turanSecondLoss
  positivity

/-- Turan's second main theorem in the positive-weight form used by the
zero detector.  If all points lie in the closed unit disk and one point of
weight at least one lies on the unit circle, one of any `K` consecutive
powers following `M` is quantitatively large. -/
theorem exists_large_consecutive_weighted_powerSum_second
    {K M : ℕ} (hK : 0 < K) (w : Fin K → ℂ) (b : Fin K → ℝ)
    (hw0 : ∀ j, w j ≠ 0) (hw : ∀ j, ‖w j‖ ≤ 1)
    (hb : ∀ j, 0 ≤ b j) (j₀ : Fin K) (hwj₀ : ‖w j₀‖ = 1)
    (hbj₀ : 1 ≤ b j₀) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      1 ≤ (K : ℝ) *
          (((17 / 16 : ℝ) ^ M *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K) /
              (2 * (68 : ℝ)⁻¹ ^ K))) *
          ‖∑ j, (b j : ℂ) * w j ^ ν‖ := by
  obtain ⟨r, hr, hgap⟩ :=
    exists_sixteenSeventeenths_prod_abs_gap hK (fun j ↦ ‖w j‖)
  let D : ℝ := 2 * (68 : ℝ)⁻¹ ^ K
  let C : ℝ := r * ((r⁻¹) ^ (M + 1) *
    ((K + 1 : ℝ) * (2 : ℝ) ^ K) / D)
  let C₀ : ℝ := (17 / 16 : ℝ) ^ M *
    ((K + 1 : ℝ) * (2 : ℝ) ^ K) / D
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hr1 : r ≤ 1 := hr.2
  have hD : 0 < D := by dsimp [D]; positivity
  have hgap' : D ≤ ∏ j, |r - ‖w j‖| := by simpa only [D] using hgap
  have hcoeff : ∀ i, ‖turanSecondCoeff w r M i‖ ≤ C := by
    intro i
    exact turanSecondCoeff_norm_le w hw hrpos hr1 hD hgap' M i
  have hrinv : r⁻¹ ≤ (17 / 16 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hrpos]
    have h16 : (0 : ℝ) < 16 := by norm_num
    calc
      (1 : ℝ) ≤ (17 / 16 : ℝ) * (16 / 17 : ℝ) := by norm_num
      _ ≤ (17 / 16 : ℝ) * r := by
        exact mul_le_mul_of_nonneg_left hr.1 (by positivity)
  have hCnonneg : 0 ≤ C := by dsimp [C, D]; positivity
  have hC₀nonneg : 0 ≤ C₀ := by dsimp [C₀, D]; positivity
  have hCC₀ : C ≤ C₀ := by
    dsimp [C, C₀]
    have hrpow : (r⁻¹) ^ M ≤ (17 / 16 : ℝ) ^ M :=
      pow_le_pow_left₀ (by positivity) hrinv M
    have hrCancel : r * (r⁻¹) ^ (M + 1) = (r⁻¹) ^ M := by
      rw [pow_succ]
      field_simp
    calc
      r * (r⁻¹ ^ (M + 1) * ((K + 1 : ℝ) * 2 ^ K) / D) =
          (r * r⁻¹ ^ (M + 1)) * ((K + 1 : ℝ) * 2 ^ K) / D := by ring
      _ = r⁻¹ ^ M * ((K + 1 : ℝ) * 2 ^ K) / D := by rw [hrCancel]
      _ ≤ (17 / 16 : ℝ) ^ M * ((K + 1 : ℝ) * 2 ^ K) / D := by
        gcongr
  have hinterp := turanSecondCoeff_interpolates
    w hw0 hrpos hD hgap' M
  have hidentity :
      ∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ) =
        ∑ i ∈ Finset.range K, turanSecondCoeff w r M i *
          ∑ j, (b j : ℂ) * w j ^ (M + 1 + i) := by
    calc
      ∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ) =
          ∑ j, ((b j : ℂ) * w j ^ (M + 1)) *
            ∑ i ∈ Finset.range K,
              turanSecondCoeff w r M i * w j ^ i := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinterp j]
        split_ifs with hjin
        · simp
        · calc
            (b j : ℂ) = (b j : ℂ) * 1 := by ring
            _ = (b j : ℂ) *
                (w j ^ (M + 1) * (w j)⁻¹ ^ (M + 1)) := by
              rw [← mul_pow, mul_inv_cancel₀ (hw0 j), one_pow]
            _ = ((b j : ℂ) * w j ^ (M + 1)) *
                (w j)⁻¹ ^ (M + 1) := by ring
      _ = ∑ i ∈ Finset.range K, turanSecondCoeff w r M i *
          ∑ j, (b j : ℂ) * w j ^ (M + 1 + i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
  have hj₀out : ¬‖w j₀‖ < r := by rw [hwj₀]; linarith
  have houter : (1 : ℝ) ≤ ∑ j, (if ‖w j‖ < r then 0 else b j) := by
    calc
      (1 : ℝ) ≤ if ‖w j₀‖ < r then 0 else b j₀ := by
        simp only [hj₀out, if_false]
        exact hbj₀
      _ ≤ ∑ j, (if ‖w j‖ < r then 0 else b j) := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin K)))
          (f := fun j ↦ if ‖w j‖ < r then 0 else b j)
          (fun j hj ↦ by
            split_ifs
            · exact le_rfl
            · exact hb j)
          (Finset.mem_univ j₀)
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (Finset.range K)
    (fun i ↦ ‖∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖)
    ⟨0, Finset.mem_range.2 hK⟩
  refine ⟨M + 1 + i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have hiK : i < K := Finset.mem_range.1 hi
    omega
  · have houterNorm : (1 : ℝ) ≤
        ‖∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ)‖ := by
      calc
        (1 : ℝ) ≤ ∑ j, (if ‖w j‖ < r then 0 else b j) := houter
        _ = (∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ)).re := by simp
        _ ≤ ‖∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ)‖ :=
          Complex.re_le_norm _
    calc
      (1 : ℝ) ≤ ‖∑ j, ((if ‖w j‖ < r then 0 else b j : ℝ) : ℂ)‖ :=
        houterNorm
      _ = ‖∑ i ∈ Finset.range K, turanSecondCoeff w r M i *
          ∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖ := by rw [hidentity]
      _ ≤ ∑ i ∈ Finset.range K, ‖turanSecondCoeff w r M i *
          ∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.range K, C *
          ‖∑ j, (b j : ℂ) * w j ^ (M + 1 + q)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcoeff q) (norm_nonneg _)
      _ ≤ ∑ _q ∈ Finset.range K, C *
          ‖∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (himax q hq) hCnonneg
      _ = (K : ℝ) * C *
          ‖∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖ := by simp [mul_assoc]
      _ ≤ (K : ℝ) * C₀ *
          ‖∑ j, (b j : ℂ) * w j ^ (M + 1 + i)‖ := by
        gcongr

end

end Erdos48
