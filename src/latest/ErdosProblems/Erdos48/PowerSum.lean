/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos519

/-!
# Finite power-sum detectors for the Erdős 48 zero-density argument

Atkinson's proved form of Turán's power-sum theorem in `Erdos519` is
repackaged here in the normalization used for reciprocal zero distances.
The second result permits a prescribed positive spacing between the detected
exponents.  This is a useful first zero-detection layer; the consecutive
high-exponent form needed for the log-free density estimate is developed
separately.
-/

namespace Erdos48

open scoped BigOperators Polynomial

noncomputable section

/-- A distinguished nonzero term controls one of the first `n` pure power
sums.  No upper bound on the remaining terms is required. -/
theorem exists_norm_purePowerSum_gt_distinguished
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) (i₀ : Fin n)
    (hi₀ : z i₀ ≠ 0) :
    ∃ k : Fin n,
      (1 / 6 : ℝ) * ‖z i₀‖ ^ (k.val + 1) <
        ‖∑ i : Fin n, z i ^ (k.val + 1)‖ := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, hn⟩ i₀
  let w : Fin n → ℂ := fun i ↦ z (σ i) / z i₀
  have hw₀ : w ⟨0, hn⟩ = 1 := by
    simp only [w, σ, Equiv.swap_apply_left]
    exact div_self hi₀
  obtain ⟨k, hk⟩ := Erdos519.erdos519 hn w hw₀
  refine ⟨k, ?_⟩
  have hsum :
      (∑ i : Fin n, w i ^ (k.val + 1)) =
        (∑ i : Fin n, z i ^ (k.val + 1)) / z i₀ ^ (k.val + 1) := by
    calc
      (∑ i : Fin n, w i ^ (k.val + 1)) =
          Erdos519.powerSum (fun i ↦ z (σ i) / z i₀) (k.val + 1) := by
            rfl
      _ = Erdos519.powerSum (z ∘ σ) (k.val + 1) /
          z i₀ ^ (k.val + 1) := by
            change Erdos519.powerSum
                (fun i ↦ (z ∘ σ) i / z i₀) (k.val + 1) = _
            rw [Erdos519.powerSum_div]
      _ = Erdos519.powerSum z (k.val + 1) /
          z i₀ ^ (k.val + 1) := by
            rw [Erdos519.powerSum_perm]
      _ = _ := by rfl
  rw [Erdos519.powerSum, hsum, norm_div, norm_pow] at hk
  have hden : 0 < ‖z i₀‖ ^ (k.val + 1) := by positivity
  exact (lt_div_iff₀ hden).mp hk

/-- Applying the preceding detector after taking an `L`-th power forces
the selected exponent to be a positive multiple of `L`, while retaining a
linear upper bound in the number of terms. -/
theorem exists_norm_sparsePowerSum_gt_distinguished
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) (i₀ : Fin n)
    (hi₀ : z i₀ ≠ 0) {L : ℕ} (hL : 0 < L) :
    ∃ j : ℕ, L ≤ j ∧ j ≤ L * n ∧
      (1 / 6 : ℝ) * ‖z i₀‖ ^ j <
        ‖∑ i : Fin n, z i ^ j‖ := by
  let w : Fin n → ℂ := fun i ↦ z i ^ L
  have hwi₀ : w i₀ ≠ 0 := pow_ne_zero L hi₀
  obtain ⟨k, hk⟩ :=
    exists_norm_purePowerSum_gt_distinguished hn w i₀ hwi₀
  refine ⟨L * (k.val + 1), ?_, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_right L (Nat.succ_pos k.val)
  · exact Nat.mul_le_mul_left L (Nat.succ_le_iff.mpr k.isLt)
  · simpa only [w, norm_pow, ← pow_mul] using hk

/-! ## A consecutive high-exponent Turán detector

The log-free density argument needs a power in a prescribed translated
interval, not merely one of the first few powers.  The following interpolation
argument is the quantitative consecutive-power lemma already used in the
formal proof of Erdős 516, reproduced here so that its useful conclusion is a
public theorem of the present development. -/

noncomputable def turanRootPolynomial {K : ℕ} (w : Fin K → ℂ) : ℂ[X] :=
  ∏ j : Fin K, (Polynomial.X - Polynomial.C (w j))

lemma turanRootPolynomial_monic {K : ℕ} (w : Fin K → ℂ) :
    (turanRootPolynomial w).Monic := by
  simpa only [turanRootPolynomial] using
    Polynomial.monic_prod_X_sub_C w (Finset.univ : Finset (Fin K))

lemma turanRootPolynomial_natDegree {K : ℕ} (w : Fin K → ℂ) :
    (turanRootPolynomial w).natDegree = K := by
  rw [turanRootPolynomial]
  simpa using Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    (s := Finset.univ) w

lemma turanRootPolynomial_eval_root {K : ℕ} (w : Fin K → ℂ) (j : Fin K) :
    (turanRootPolynomial w).eval (w j) = 0 := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp

private lemma turanRootPolynomial_mahlerMeasure_eq_one {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) :
    (turanRootPolynomial w).mahlerMeasure = 1 := by
  rw [turanRootPolynomial]
  induction (Finset.univ : Finset (Fin K)) using Finset.induction with
  | empty => simp [Polynomial.mahlerMeasure_one]
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Polynomial.mahlerMeasure_mul, ih]
      rw [Polynomial.mahlerMeasure_X_sub_C]
      simp [max_eq_left (hw j)]

lemma turanRootPolynomial_coeff_norm_le_choose {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (d : ℕ) :
    ‖(turanRootPolynomial w).coeff d‖ ≤ K.choose d := by
  have h := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d
    (turanRootPolynomial w)
  rw [turanRootPolynomial_natDegree, turanRootPolynomial_mahlerMeasure_eq_one w hw,
    mul_one] at h
  exact h

private lemma turanRootPolynomial_norm_ge_one_on_sphere_two {K : ℕ}
    (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    1 ≤ ‖(turanRootPolynomial w).eval ζ‖ := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_prod]
  have hfactor : ∀ j : Fin K, 1 ≤ ‖ζ - w j‖ := by
    intro j
    have hrev := norm_sub_norm_le ζ (w j)
    rw [hζ] at hrev
    linarith [hw j]
  exact Finset.one_le_prod (fun j _ ↦ hfactor j)

noncomputable def turanDividedCoeff (P : ℂ[X]) (K i : ℕ) (ζ : ℂ) : ℂ :=
  ∑ d ∈ Finset.range (K + 1),
    if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0

private lemma mul_turanMonomialDividedSum (ζ x : ℂ) (d : ℕ) :
    (ζ - x) * ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i = ζ ^ d - x ^ d := by
  have hsum :
      (∑ i ∈ Finset.range d, ζ ^ i * x ^ (d - 1 - i)) =
        ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i := by
    simpa only [mul_comm] using geom_sum₂_comm ζ x d
  rw [mul_comm (ζ - x), ← hsum]
  exact (Commute.all ζ x).geom_sum₂_mul d

lemma turanDividedCoeff_sum_identity (P : ℂ[X]) {K : ℕ}
    (hP : P.natDegree ≤ K) (ζ x : ℂ) :
    (ζ - x) * ∑ i ∈ Finset.range K, turanDividedCoeff P K i ζ * x ^ i =
      P.eval ζ - P.eval x := by
  have hPK : P.natDegree < K + 1 := by omega
  rw [Polynomial.eval_eq_sum_range' hPK, Polynomial.eval_eq_sum_range' hPK,
    ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [turanDividedCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdK : d < K + 1 := Finset.mem_range.1 hd
  have hrange : Finset.range d ⊆ Finset.range K := by
    intro i hi
    have hid := Finset.mem_range.1 hi
    exact Finset.mem_range.2 (by omega)
  have htri :
      (∑ i ∈ Finset.range K,
          (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i) =
        P.coeff d * ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i := by
    calc
      (∑ i ∈ Finset.range K,
          (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i) =
          ∑ i ∈ Finset.range d,
            (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i := by
        rw [Finset.sum_subset hrange]
        intro i hiK hid
        have hnot : ¬ i < d := by
          simpa only [Finset.mem_range, not_lt] using hid
        simp [hnot]
      _ = ∑ i ∈ Finset.range d,
          P.coeff d * (ζ ^ (d - 1 - i) * x ^ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hid : i < d := Finset.mem_range.1 hi
        simp only [hid, if_true]
        ring
      _ = P.coeff d * ∑ i ∈ Finset.range d,
          ζ ^ (d - 1 - i) * x ^ i := by rw [Finset.mul_sum]
  rw [← Finset.mul_sum, htri]
  rw [show (ζ - x) * (P.coeff d * ∑ i ∈ Finset.range d,
      ζ ^ (d - 1 - i) * x ^ i) =
      P.coeff d * ((ζ - x) * ∑ i ∈ Finset.range d,
        ζ ^ (d - 1 - i) * x ^ i) by ring]
  rw [mul_turanMonomialDividedSum]
  ring

private lemma turanDividedCoeff_norm_le {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (i : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
      (K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
  rw [turanDividedCoeff]
  calc
    ‖∑ d ∈ Finset.range (K + 1),
        if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ ≤
        ∑ d ∈ Finset.range (K + 1),
          ‖if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (K + 1), (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with hid
      · rw [norm_mul, norm_pow, hζ]
        have hcoeff := turanRootPolynomial_coeff_norm_le_choose w hw d
        have hchoose : (K.choose d : ℝ) ≤ (2 : ℝ) ^ K := by
          exact_mod_cast Nat.choose_le_two_pow K d
        have hpow : (2 : ℝ) ^ (d - 1 - i) ≤ (2 : ℝ) ^ K := by
          have hdle : d ≤ K := by
            have := Finset.mem_range.1 hd
            omega
          have hexp : d - 1 - i ≤ K := by omega
          exact pow_le_pow_right₀ (by norm_num) hexp
        exact mul_le_mul (hcoeff.trans hchoose) hpow (by positivity) (by positivity)
      · simp
    _ = (K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
      simp [mul_assoc]

private noncomputable def turanInterpolationCoeff {K : ℕ} (w : Fin K → ℂ)
    (n i : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∮ ζ in C(0, 2),
      ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ

private lemma turanInterpolationCoeff_norm_le {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (n i : ℕ) :
    ‖turanInterpolationCoeff w n i‖ ≤
      2 * ((2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K)) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (show (0 : ℝ) ≤ 2 by norm_num)
  intro ζ hζ
  have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
  have hP := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
  have hq := turanDividedCoeff_norm_le w hw i hζnorm
  rw [norm_div, norm_mul, norm_pow, hζnorm]
  have hden : 0 < ‖(turanRootPolynomial w).eval ζ‖ := lt_of_lt_of_le zero_lt_one hP
  rw [div_le_iff₀ hden]
  calc
    (2 : ℝ) ^ n * ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
        (2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ ((2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K)) *
        ‖(turanRootPolynomial w).eval ζ‖ := by
      exact le_mul_of_one_le_right (by positivity) hP

private lemma turanInterpolationIntegrand_circleIntegrable {K : ℕ}
    (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1) (n i : ℕ) :
    CircleIntegrable
      (fun ζ ↦ ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ) 0 2 := by
  apply ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 2 by norm_num)
  apply ContinuousOn.div
  · have hq : Continuous (fun ζ ↦
        turanDividedCoeff (turanRootPolynomial w) K i ζ) := by
      unfold turanDividedCoeff
      apply continuous_finsetSum
      intro d hd
      by_cases hid : i < d
      · simp only [hid, if_true]
        fun_prop
      · simp only [hid, if_false]
        fun_prop
    exact ((continuous_id.pow n).mul hq).continuousOn
  · fun_prop
  · intro ζ hζ
    have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
    have hP := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hP))

private lemma turanInterpolationCoeff_interpolates {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (n : ℕ) (j : Fin K) :
    ∑ i ∈ Finset.range K, turanInterpolationCoeff w n i * w j ^ i = w j ^ n := by
  let P : ℂ[X] := turanRootPolynomial w
  let c₀ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  let g : ℕ → ℂ → ℂ := fun i ζ ↦
    ζ ^ n * turanDividedCoeff P K i ζ / P.eval ζ
  have hint : ∀ i ∈ Finset.range K, CircleIntegrable (g i) 0 2 := by
    intro i hi
    simpa only [g, P] using turanInterpolationIntegrand_circleIntegrable w hw n i
  have hintMul : ∀ i ∈ Finset.range K,
      CircleIntegrable (fun ζ ↦ g i ζ * w j ^ i) 0 2 := by
    intro i hi
    have h := hint i hi
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 2 θ) * w j ^ i) MeasureTheory.volume 0 (2 * Real.pi)
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 2 θ)) MeasureTheory.volume 0 (2 * Real.pi) at h
    exact h.mul_const (w j ^ i)
  have hsumIntegral :
      (∮ ζ in C(0, 2), ∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
        ∑ i ∈ Finset.range K, ∮ ζ in C(0, 2), g i ζ * w j ^ i :=
    circleIntegral.integral_fun_sum hintMul
  have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) 2,
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) = ζ ^ n / (ζ - w j) := by
    intro ζ hζ
    have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
    have hPnorm := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
    have hPne : P.eval ζ ≠ 0 := by
      dsimp [P]
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hPnorm))
    have hζwj : ζ - w j ≠ 0 := by
      intro hzero
      have heq : ζ = w j := sub_eq_zero.mp hzero
      have := hw j
      rw [← heq, hζnorm] at this
      norm_num at this
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
          (ζ ^ n / P.eval ζ) * ∑ i ∈ Finset.range K,
            turanDividedCoeff P K i ζ * w j ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [g]
        field_simp
      _ = (ζ ^ n / P.eval ζ) * (P.eval ζ / (ζ - w j)) := by rw [hqsum]
      _ = ζ ^ n / (ζ - w j) := by field_simp
  calc
    (∑ i ∈ Finset.range K, turanInterpolationCoeff w n i * w j ^ i) =
        ∑ i ∈ Finset.range K,
          c₀ * ((∮ ζ in C(0, 2), g i ζ) * w j ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [turanInterpolationCoeff, c₀, g, P, smul_eq_mul, mul_assoc]
    _ = c₀ * ∑ i ∈ Finset.range K, (∮ ζ in C(0, 2), g i ζ) * w j ^ i := by
      rw [Finset.mul_sum]
    _ = c₀ * ∑ i ∈ Finset.range K,
        ∮ ζ in C(0, 2), g i ζ * w j ^ i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∮ ζ in C(0, 2), g i ζ) * w j ^ i =
          w j ^ i * ∮ ζ in C(0, 2), g i ζ by ring,
        ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr (show (0 : ℝ) ≤ 2 by norm_num)
      intro ζ hζ
      ring
    _ = c₀ * ∮ ζ in C(0, 2),
        ∑ i ∈ Finset.range K, g i ζ * w j ^ i := by rw [hsumIntegral]
    _ = c₀ * ∮ ζ in C(0, 2), ζ ^ n / (ζ - w j) := by
      congr 1
      apply circleIntegral.integral_congr (show (0 : ℝ) ≤ 2 by norm_num)
      exact hpoint
    _ = w j ^ n := by
      have hwball : w j ∈ Metric.ball (0 : ℂ) 2 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact (hw j).trans_lt (by norm_num)
      have hcauchy := (differentiableOn_pow n).circleIntegral_sub_inv_smul
        (c := (0 : ℂ)) (R := (2 : ℝ)) hwball
      dsimp [c₀]
      rw [show (fun ζ : ℂ ↦ ζ ^ n / (ζ - w j)) =
          fun ζ ↦ (ζ - w j)⁻¹ • ζ ^ n by
        funext ζ
        simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]]
      rw [hcauchy]
      rw [smul_eq_mul]
      have hconst : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [← mul_assoc, inv_mul_cancel₀ hconst, one_mul]

/-- A separation-free consecutive power-sum estimate for points outside the unit
disk.  Among any `K` consecutive positive translates after `M`, one translate is
large compared with the zeroth power sum.  This is the form used for reciprocal
zero distances: points in a disk become points of norm at least one after
normalization by the disk radius. -/
theorem exists_large_consecutive_powerSum_of_one_le_norm
    {K M : ℕ} (hK : 0 < K) (w b : Fin K → ℂ)
    (hw : ∀ j, 1 ≤ ‖w j‖) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ ν‖ := by
  let v : Fin K → ℂ := fun j ↦ (w j)⁻¹
  let c : ℕ → ℂ := fun i ↦ turanInterpolationCoeff v (M + K) i
  have hv : ∀ j, ‖v j‖ ≤ 1 := by
    intro j
    dsimp [v]
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hw j))).2 (hw j)
  have hwne : ∀ j, w j ≠ 0 := fun j ↦ norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (hw j)))
  have hinterp : ∀ j, (w j ^ (M + K))⁻¹ =
      ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
    intro j
    have h := turanInterpolationCoeff_interpolates v hv (M + K) j
    simpa only [v, c, inv_pow] using h.symm
  have hidentity : (∑ j, b j) =
      ∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i) := by
    calc
      (∑ j, b j) = ∑ j, (b j * w j ^ (M + K)) *
          (w j ^ (M + K))⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          b j = b j * 1 := by rw [mul_one]
          _ = b j * (w j ^ (M + K) * (w j ^ (M + K))⁻¹) := by
            rw [mul_inv_cancel₀ (pow_ne_zero _ (hwne j))]
          _ = b j * w j ^ (M + K) * (w j ^ (M + K))⁻¹ := by ring
      _ = ∑ j, (b j * w j ^ (M + K)) *
          ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinterp]
      _ = ∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hiK : i < K := Finset.mem_range.1 hi
        have hiN : i ≤ M + K := by omega
        rw [pow_sub₀ _ (hwne j) hiN]
        ring
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (Finset.range K) (fun i ↦ ‖∑ j, b j * w j ^ (M + K - i)‖)
    ⟨0, Finset.mem_range.2 hK⟩
  refine ⟨M + K - i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have hiK : i < K := Finset.mem_range.1 hi
    omega
  · rw [hidentity]
    calc
      ‖∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i)‖ ≤
          ∑ i ∈ Finset.range K,
            ‖c i * ∑ j, b j * w j ^ (M + K - i)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.range K,
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
            ‖∑ j, b j * w j ^ (M + K - q)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (turanInterpolationCoeff_norm_le v hv (M + K) q) (norm_nonneg _)
      _ ≤ ∑ _q ∈ Finset.range K,
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
            ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (himax q hq) (by positivity)
      _ = (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        simp [mul_assoc]

/-- Unit-modulus specialization of
`exists_large_consecutive_powerSum_of_one_le_norm`. -/
theorem exists_large_consecutive_powerSum {K M : ℕ} (hK : 0 < K)
    (w b : Fin K → ℂ) (hw : ∀ j, ‖w j‖ = 1) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ ν‖ := by
  apply exists_large_consecutive_powerSum_of_one_le_norm hK w b
  intro j
  rw [hw j]

/-! ## A radius-optimized consecutive detector

The preceding interpolation argument used the fixed contour `|z| = 2`.
For the log-free zero-density argument that is too wasteful: its coefficient
bound contains `2 ^ M`, which exactly cancels the decay obtained by starting
the detected powers at a large exponent `M`.  The same argument on an
arbitrary circle of radius `R > 1` gives the optimized factor
`R ^ (M + O(K)) / (R - 1) ^ K`.  Taking `R = 1 + K / M` is the usual
radius-optimized form of Turan's consecutive power-sum argument.
-/

private lemma turanRootPolynomial_norm_ge_sub_one_pow_on_sphere
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    {R : ℝ} (hR : 1 < R) {ζ : ℂ} (hζ : ‖ζ‖ = R) :
    (R - 1) ^ K ≤ ‖(turanRootPolynomial w).eval ζ‖ := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_prod]
  have hfactor : ∀ j : Fin K, R - 1 ≤ ‖ζ - w j‖ := by
    intro j
    have hrev := norm_sub_norm_le ζ (w j)
    rw [hζ] at hrev
    linarith [hw j]
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin K)))
    (fun _ _ ↦ sub_nonneg.mpr hR.le) (fun j _ ↦ hfactor j)
  simpa using hprod

private lemma turanDividedCoeff_norm_le_radius
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    (i : ℕ) {R : ℝ} (hR : 1 ≤ R) {ζ : ℂ} (hζ : ‖ζ‖ = R) :
    ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
      (K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K := by
  rw [turanDividedCoeff]
  calc
    ‖∑ d ∈ Finset.range (K + 1),
        if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ ≤
        ∑ d ∈ Finset.range (K + 1),
          ‖if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (K + 1), (2 : ℝ) ^ K * R ^ K := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with hid
      · rw [norm_mul, norm_pow, hζ]
        have hcoeff := turanRootPolynomial_coeff_norm_le_choose w hw d
        have hchoose : (K.choose d : ℝ) ≤ (2 : ℝ) ^ K := by
          exact_mod_cast Nat.choose_le_two_pow K d
        have hpow : R ^ (d - 1 - i) ≤ R ^ K := by
          have hdle : d ≤ K := by
            have := Finset.mem_range.1 hd
            omega
          have hexp : d - 1 - i ≤ K := by omega
          exact pow_le_pow_right₀ hR hexp
        exact mul_le_mul (hcoeff.trans hchoose) hpow (by positivity) (by positivity)
      · simp [pow_nonneg (le_trans zero_le_one hR)]
    _ = (K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K := by
      simp [mul_assoc]

private noncomputable def turanInterpolationCoeffRadius
    {K : ℕ} (w : Fin K → ℂ) (R : ℝ) (n i : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∮ ζ in C(0, R),
      ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ

private lemma turanInterpolationCoeffRadius_norm_le
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    {R : ℝ} (hR : 1 < R) (n i : ℕ) :
    ‖turanInterpolationCoeffRadius w R n i‖ ≤
      R * (R ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K) /
        (R - 1) ^ K) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (zero_le_one.trans hR.le)
  intro ζ hζ
  have hζnorm : ‖ζ‖ = R := by simpa [Metric.mem_sphere] using hζ
  have hP := turanRootPolynomial_norm_ge_sub_one_pow_on_sphere
    w hw hR hζnorm
  have hq := turanDividedCoeff_norm_le_radius w hw i hR.le hζnorm
  rw [norm_div, norm_mul, norm_pow, hζnorm]
  apply div_le_div₀
  · positivity
  · exact mul_le_mul_of_nonneg_left hq (by positivity)
  · exact pow_pos (sub_pos.mpr hR) _
  · exact hP

private lemma turanInterpolationIntegrandRadius_circleIntegrable
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    {R : ℝ} (hR : 1 < R) (n i : ℕ) :
    CircleIntegrable
      (fun ζ ↦ ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ) 0 R := by
  apply ContinuousOn.circleIntegrable (zero_le_one.trans hR.le)
  apply ContinuousOn.div
  · have hq : Continuous (fun ζ ↦
        turanDividedCoeff (turanRootPolynomial w) K i ζ) := by
      unfold turanDividedCoeff
      apply continuous_finsetSum
      intro d hd
      by_cases hid : i < d
      · simp only [hid, if_true]
        fun_prop
      · simp only [hid, if_false]
        fun_prop
    exact ((continuous_id.pow n).mul hq).continuousOn
  · fun_prop
  · intro ζ hζ
    have hζnorm : ‖ζ‖ = R := by simpa [Metric.mem_sphere] using hζ
    have hP := turanRootPolynomial_norm_ge_sub_one_pow_on_sphere
      w hw hR hζnorm
    exact norm_ne_zero_iff.mp
      (ne_of_gt (lt_of_lt_of_le (pow_pos (sub_pos.mpr hR) _) hP))

private lemma turanInterpolationCoeffRadius_interpolates
    {K : ℕ} (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    {R : ℝ} (hR : 1 < R) (n : ℕ) (j : Fin K) :
    ∑ i ∈ Finset.range K,
        turanInterpolationCoeffRadius w R n i * w j ^ i = w j ^ n := by
  let P : ℂ[X] := turanRootPolynomial w
  let c₀ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  let g : ℕ → ℂ → ℂ := fun i ζ ↦
    ζ ^ n * turanDividedCoeff P K i ζ / P.eval ζ
  have hint : ∀ i ∈ Finset.range K, CircleIntegrable (g i) 0 R := by
    intro i hi
    simpa only [g, P] using
      turanInterpolationIntegrandRadius_circleIntegrable w hw hR n i
  have hintMul : ∀ i ∈ Finset.range K,
      CircleIntegrable (fun ζ ↦ g i ζ * w j ^ i) 0 R := by
    intro i hi
    have h := hint i hi
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 R θ) * w j ^ i)
        MeasureTheory.volume 0 (2 * Real.pi)
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 R θ))
        MeasureTheory.volume 0 (2 * Real.pi) at h
    exact h.mul_const (w j ^ i)
  have hsumIntegral :
      (∮ ζ in C(0, R), ∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
        ∑ i ∈ Finset.range K, ∮ ζ in C(0, R), g i ζ * w j ^ i :=
    circleIntegral.integral_fun_sum hintMul
  have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) R,
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) = ζ ^ n / (ζ - w j) := by
    intro ζ hζ
    have hζnorm : ‖ζ‖ = R := by simpa [Metric.mem_sphere] using hζ
    have hPnorm := turanRootPolynomial_norm_ge_sub_one_pow_on_sphere
      w hw hR hζnorm
    have hPne : P.eval ζ ≠ 0 := by
      dsimp [P]
      exact norm_ne_zero_iff.mp
        (ne_of_gt (lt_of_lt_of_le (pow_pos (sub_pos.mpr hR) _) hPnorm))
    have hζwj : ζ - w j ≠ 0 := by
      intro hzero
      have heq : ζ = w j := sub_eq_zero.mp hzero
      have := hw j
      rw [← heq, hζnorm] at this
      linarith
    have hroot : P.eval (w j) = 0 := turanRootPolynomial_eval_root w j
    have hid := turanDividedCoeff_sum_identity P
      (by dsimp [P]; rw [turanRootPolynomial_natDegree]) ζ (w j)
    rw [hroot, sub_zero] at hid
    have hqsum : (∑ i ∈ Finset.range K,
        turanDividedCoeff P K i ζ * w j ^ i) = P.eval ζ / (ζ - w j) := by
      apply (eq_div_iff hζwj).2
      simpa only [mul_comm] using hid
    calc
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
          (ζ ^ n / P.eval ζ) * ∑ i ∈ Finset.range K,
            turanDividedCoeff P K i ζ * w j ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [g]
        field_simp
      _ = (ζ ^ n / P.eval ζ) * (P.eval ζ / (ζ - w j)) := by rw [hqsum]
      _ = ζ ^ n / (ζ - w j) := by field_simp
  calc
    (∑ i ∈ Finset.range K,
        turanInterpolationCoeffRadius w R n i * w j ^ i) =
        ∑ i ∈ Finset.range K,
          c₀ * ((∮ ζ in C(0, R), g i ζ) * w j ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [turanInterpolationCoeffRadius, c₀, g, P, smul_eq_mul, mul_assoc]
    _ = c₀ * ∑ i ∈ Finset.range K,
        (∮ ζ in C(0, R), g i ζ) * w j ^ i := by rw [Finset.mul_sum]
    _ = c₀ * ∑ i ∈ Finset.range K,
        ∮ ζ in C(0, R), g i ζ * w j ^ i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∮ ζ in C(0, R), g i ζ) * w j ^ i =
          w j ^ i * ∮ ζ in C(0, R), g i ζ by ring,
        ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr (zero_le_one.trans hR.le)
      intro ζ hζ
      ring
    _ = c₀ * ∮ ζ in C(0, R),
        ∑ i ∈ Finset.range K, g i ζ * w j ^ i := by rw [hsumIntegral]
    _ = c₀ * ∮ ζ in C(0, R), ζ ^ n / (ζ - w j) := by
      congr 1
      apply circleIntegral.integral_congr (zero_le_one.trans hR.le)
      exact hpoint
    _ = w j ^ n := by
      have hwball : w j ∈ Metric.ball (0 : ℂ) R := by
        rw [Metric.mem_ball, dist_zero_right]
        exact (hw j).trans_lt hR
      have hcauchy := (differentiableOn_pow n).circleIntegral_sub_inv_smul
        (c := (0 : ℂ)) (R := R) hwball
      dsimp [c₀]
      rw [show (fun ζ : ℂ ↦ ζ ^ n / (ζ - w j)) =
          fun ζ ↦ (ζ - w j)⁻¹ • ζ ^ n by
        funext ζ
        simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]]
      rw [hcauchy]
      rw [smul_eq_mul]
      have hconst : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [← mul_assoc, inv_mul_cancel₀ hconst, one_mul]

/-- Radius-optimized consecutive power-sum inequality.  The contour radius
is a free parameter; unlike the fixed-radius version, the coefficient loss
need not contain an exponential factor in the starting exponent `M`. -/
theorem exists_large_consecutive_powerSum_of_one_le_norm_radius
    {K M : ℕ} (hK : 0 < K) (w b : Fin K → ℂ)
    (hw : ∀ j, 1 ≤ ‖w j‖) {R : ℝ} (hR : 1 < R) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (R * (R ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K) /
              (R - 1) ^ K)) *
          ‖∑ j, b j * w j ^ ν‖ := by
  let v : Fin K → ℂ := fun j ↦ (w j)⁻¹
  let c : ℕ → ℂ := fun i ↦
    turanInterpolationCoeffRadius v R (M + K) i
  have hv : ∀ j, ‖v j‖ ≤ 1 := by
    intro j
    dsimp [v]
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hw j))).2 (hw j)
  have hwne : ∀ j, w j ≠ 0 := fun j ↦ norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (hw j)))
  have hinterp : ∀ j, (w j ^ (M + K))⁻¹ =
      ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
    intro j
    have h := turanInterpolationCoeffRadius_interpolates
      v hv hR (M + K) j
    simpa only [v, c, inv_pow] using h.symm
  have hidentity : (∑ j, b j) =
      ∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i) := by
    calc
      (∑ j, b j) = ∑ j, (b j * w j ^ (M + K)) *
          (w j ^ (M + K))⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          b j = b j * 1 := by rw [mul_one]
          _ = b j * (w j ^ (M + K) * (w j ^ (M + K))⁻¹) := by
            rw [mul_inv_cancel₀ (pow_ne_zero _ (hwne j))]
          _ = b j * w j ^ (M + K) * (w j ^ (M + K))⁻¹ := by ring
      _ = ∑ j, (b j * w j ^ (M + K)) *
          ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinterp]
      _ = ∑ i ∈ Finset.range K,
          c i * ∑ j, b j * w j ^ (M + K - i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hiK : i < K := Finset.mem_range.1 hi
        have hiN : i ≤ M + K := by omega
        rw [pow_sub₀ _ (hwne j) hiN]
        ring
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (Finset.range K) (fun i ↦ ‖∑ j, b j * w j ^ (M + K - i)‖)
    ⟨0, Finset.mem_range.2 hK⟩
  refine ⟨M + K - i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have hiK : i < K := Finset.mem_range.1 hi
    omega
  · rw [hidentity]
    calc
      ‖∑ i ∈ Finset.range K,
          c i * ∑ j, b j * w j ^ (M + K - i)‖ ≤
          ∑ i ∈ Finset.range K,
            ‖c i * ∑ j, b j * w j ^ (M + K - i)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.range K,
          (R * (R ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K) /
              (R - 1) ^ K)) *
            ‖∑ j, b j * w j ^ (M + K - q)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (turanInterpolationCoeffRadius_norm_le
            v hv hR (M + K) q) (norm_nonneg _)
      _ ≤ ∑ _q ∈ Finset.range K,
          (R * (R ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K) /
              (R - 1) ^ K)) *
            ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (himax q hq) (by positivity)
      _ = (K : ℝ) *
          (R * (R ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * R ^ K) /
              (R - 1) ^ K)) *
          ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        simp [mul_assoc]

end

end Erdos48
