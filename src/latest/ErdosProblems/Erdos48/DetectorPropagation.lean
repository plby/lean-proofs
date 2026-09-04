/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.FiniteSeriesDetector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Propagation of the finite zero detector

The finite weighted von Mangoldt polynomial supplied by the zero detector
cannot collapse immediately as its height varies.  This file rewrites its
`LSeries` terms as ordinary Dirichlet phases and proves a uniform Lipschitz
estimate from a positive Chebyshev-majorized Dirichlet series.
-/

namespace Erdos48

open Complex LSeries
open BoundedGaps.Maynard

noncomputable section

/-- The positive majorant for an order-`k` weighted von Mangoldt series. -/
noncomputable def weightedVonMangoldtMajorant
    (eta : ℝ) (k n : ℕ) : ℝ :=
  Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
    (n : ℝ) ^ (-(1 + eta))

/-- The positive weighted von Mangoldt series is summable to the right of
the line `re s = 1`. -/
theorem summable_weightedVonMangoldtMajorant
    (eta : ℝ) (heta : 0 < eta) (k : ℕ) :
    Summable (weightedVonMangoldtMajorant eta k) := by
  let b : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(1 + eta / 2))
  let K : ℝ := k.factorial * (2 / eta) ^ k
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : Summable b := by
    dsimp [b]
    exact summable_vonMangoldt_mul_rpow_neg (by linarith)
  have ha0 : ∀ n, 0 ≤ weightedVonMangoldtMajorant eta k n := by
    intro n
    unfold weightedVonMangoldtMajorant
    positivity
  have hab : ∀ n, weightedVonMangoldtMajorant eta k n ≤ K * b n := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [weightedVonMangoldtMajorant, b]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := log_pow_mul_rpow_neg_quarter_le
      (2 * eta) (by positivity) n k hn
    have hlog' :
        Real.log n ^ k * (n : ℝ) ^ (-eta / 2) ≤ K := by
      simpa only [show -(2 * eta) / 4 = -eta / 2 by ring,
        show 4 / (2 * eta) = 2 / eta by field_simp [heta.ne']; ring,
        K] using hlog
    have hsplit :
        (n : ℝ) ^ (-(1 + eta)) =
          (n : ℝ) ^ (-eta / 2) *
            (n : ℝ) ^ (-(1 + eta / 2)) := by
      calc
        (n : ℝ) ^ (-(1 + eta)) =
            (n : ℝ) ^ ((-eta / 2) + (-(1 + eta / 2))) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hnR _ _
    have hweight :
        0 ≤ ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta / 2)) := by positivity
    unfold weightedVonMangoldtMajorant
    dsimp [b]
    rw [hsplit]
    calc
      Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-eta / 2) *
            (n : ℝ) ^ (-(1 + eta / 2))) =
        (Real.log n ^ k * (n : ℝ) ^ (-eta / 2)) *
          (ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-(1 + eta / 2))) := by ring
      _ ≤ K *
          (ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-(1 + eta / 2))) :=
        mul_le_mul_of_nonneg_right hlog' hweight
  exact Summable.of_nonneg_of_le ha0 hab (hb.mul_left K)

/-- A pole-order bound for every positive weighted von Mangoldt series used
by the propagation argument. -/
theorem weightedVonMangoldtMajorant_tsum_le
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) (k : ℕ) :
    (∑' n, weightedVonMangoldtMajorant eta k n) ≤
      3 * (Real.log 4 + 4) * k.factorial * (2 / eta) ^ k / eta := by
  let b : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(1 + eta / 2))
  let K : ℝ := k.factorial * (2 / eta) ^ k
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : Summable b := by
    dsimp [b]
    exact summable_vonMangoldt_mul_rpow_neg (by linarith)
  have ha := summable_weightedVonMangoldtMajorant eta heta k
  have hab : ∀ n, weightedVonMangoldtMajorant eta k n ≤ K * b n := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [weightedVonMangoldtMajorant, b]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := log_pow_mul_rpow_neg_quarter_le
      (2 * eta) (by positivity) n k hn
    have hlog' :
        Real.log n ^ k * (n : ℝ) ^ (-eta / 2) ≤ K := by
      simpa only [show -(2 * eta) / 4 = -eta / 2 by ring,
        show 4 / (2 * eta) = 2 / eta by field_simp [heta.ne']; ring,
        K] using hlog
    have hsplit :
        (n : ℝ) ^ (-(1 + eta)) =
          (n : ℝ) ^ (-eta / 2) *
            (n : ℝ) ^ (-(1 + eta / 2)) := by
      calc
        (n : ℝ) ^ (-(1 + eta)) =
            (n : ℝ) ^ ((-eta / 2) + (-(1 + eta / 2))) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hnR _ _
    have hweight :
        0 ≤ ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta / 2)) := by positivity
    unfold weightedVonMangoldtMajorant
    dsimp [b]
    rw [hsplit]
    calc
      Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-eta / 2) *
            (n : ℝ) ^ (-(1 + eta / 2))) =
        (Real.log n ^ k * (n : ℝ) ^ (-eta / 2)) *
          (ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-(1 + eta / 2))) := by ring
      _ ≤ K *
          (ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-(1 + eta / 2))) :=
        mul_le_mul_of_nonneg_right hlog' hweight
  have hpositive := vonMangoldt_tsum_le_chebyshev_div_sub_one
    (sigma := 1 + eta / 2) (by linarith)
  have htsumB :
      (∑' n, b n) ≤
        (Real.log 4 + 4) * (1 + eta / 2) / (eta / 2) := by
    have heq :
        (∑' n, b n) =
          ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ (1 + eta / 2) := by
      apply tsum_congr
      intro n
      dsimp [b]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      ring
    rw [heq]
    simpa only [add_sub_cancel_left] using hpositive
  have hratio :
      (Real.log 4 + 4) * (1 + eta / 2) / (eta / 2) ≤
        3 * (Real.log 4 + 4) / eta := by
    rw [div_le_div_iff₀ (by positivity : 0 < eta / 2) heta]
    have hsmall : 1 + eta / 2 ≤ (3 / 2 : ℝ) := by linarith
    have hnonneg : 0 ≤ (Real.log 4 + 4) * eta := by positivity
    calc
      (Real.log 4 + 4) * (1 + eta / 2) * eta =
          (1 + eta / 2) * ((Real.log 4 + 4) * eta) := by ring
      _ ≤ (3 / 2 : ℝ) * ((Real.log 4 + 4) * eta) :=
        mul_le_mul_of_nonneg_right hsmall hnonneg
      _ = 3 * (Real.log 4 + 4) * (eta / 2) := by ring
  calc
    (∑' n, weightedVonMangoldtMajorant eta k n) ≤
        ∑' n, K * b n := ha.tsum_le_tsum hab (hb.mul_left K)
    _ = K * ∑' n, b n := tsum_mul_left
    _ ≤ K * ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) :=
      mul_le_mul_of_nonneg_left htsumB hK
    _ ≤ K * (3 * (Real.log 4 + 4) / eta) :=
      mul_le_mul_of_nonneg_left hratio hK
    _ = 3 * (Real.log 4 + 4) * k.factorial * (2 / eta) ^ k / eta := by
      dsimp [K]
      ring

/-- The ordinary finite Dirichlet polynomial underlying the truncated
weighted `LSeries`.  Its phase convention is chosen so that evaluation at
`t` corresponds to the usual `LSeries` argument `1 + eta + t I`. -/
noncomputable def finiteZeroDetectorPolynomial
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
      Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))

/-- A term of the truncated weighted `LSeries` has the standard oscillatory
Dirichlet-polynomial form. -/
theorem weighted_vonMangoldt_LSeries_term_eq_phase
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta t : ℝ) (k n : ℕ) (hn : 0 < n) :
    LSeries.term (fun m : ℕ ↦
        (Real.log m : ℂ) ^ k * chi m *
          (ArithmeticFunction.vonMangoldt m : ℂ))
        (((1 + eta : ℝ) : ℂ) + t * I) n =
      (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn0]
  have hcpow :
      (n : ℂ) ^ (((1 + eta : ℝ) : ℂ) + t * I) =
        (((n : ℝ) ^ (1 + eta) : ℝ) : ℂ) *
          Complex.exp (I * (((t * Real.log n) : ℝ) : ℂ)) := by
    rw [Complex.cpow_add _ _ hnC]
    have hre :
        (n : ℂ) ^ (((1 + eta : ℝ) : ℂ)) =
          (((n : ℝ) ^ (1 + eta) : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + eta)).symm
    rw [hre]
    rw [Complex.cpow_def_of_ne_zero hnC]
    rw [← Complex.natCast_log]
    congr 1
    push_cast
    ring_nf
  rw [hcpow, div_eq_mul_inv, mul_inv, ← Complex.exp_neg]
  rw [← Complex.ofReal_inv, ← Real.rpow_neg hnR.le]
  unfold weightedVonMangoldtMajorant
  push_cast
  ring_nf

theorem weighted_vonMangoldt_LSeries_sum_eq_polynomial
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta t : ℝ) (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        LSeries.term (fun m : ℕ ↦
          (Real.log m : ℂ) ^ k * chi m *
            (ArithmeticFunction.vonMangoldt m : ℂ))
          (((1 + eta : ℝ) : ℂ) + t * I) n) =
      finiteZeroDetectorPolynomial chi eta k N t := by
  classical
  unfold finiteZeroDetectorPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  exact weighted_vonMangoldt_LSeries_term_eq_phase chi eta t k n
    (Finset.mem_Icc.mp hn).1

/-- Unit-circle phases are Lipschitz in their real frequency. -/
theorem norm_dirichletPhase_sub_le (u v x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (I * (((-u * x : ℝ) : ℂ))) -
        Complex.exp (I * (((-v * x : ℝ) : ℂ)))‖ ≤
      |u - v| * x := by
  have hid :
      Complex.exp (I * (((-u * x : ℝ) : ℂ))) -
          Complex.exp (I * (((-v * x : ℝ) : ℂ))) =
        Complex.exp (I * (((-v * x : ℝ) : ℂ))) *
          (Complex.exp (I * (((-(u - v) * x : ℝ) : ℂ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul]
  have hunit :
      ‖Complex.exp (I * (((-v * x : ℝ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hunit, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hx]

/-- The finite zero-detector polynomial is uniformly Lipschitz in height;
one additional logarithm occurs in the positive majorant. -/
theorem norm_finiteZeroDetectorPolynomial_sub_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k N : ℕ) (u v : ℝ) :
    ‖finiteZeroDetectorPolynomial chi eta k N u -
        finiteZeroDetectorPolynomial chi eta k N v‖ ≤
      |u - v| *
        ∑ n ∈ Finset.Icc 1 N,
          weightedVonMangoldtMajorant eta (k + 1) n := by
  classical
  unfold finiteZeroDetectorPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Icc 1 N,
        ((weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
            Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)) -
          (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
            Complex.exp (I * (((-v * Real.log n) : ℝ) : ℂ)))‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖(weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)) -
            (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
              Complex.exp (I * (((-v * Real.log n) : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |u - v| * weightedVonMangoldtMajorant eta (k + 1) n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hchi : ‖chi n‖ ≤ 1 := chi.norm_le_one (n : ZMod q)
      have hphase := norm_dirichletPhase_sub_le u v (Real.log n) hlog0
      have hmajor0 : 0 ≤ weightedVonMangoldtMajorant eta k n := by
        unfold weightedVonMangoldtMajorant
        positivity
      calc
        ‖(weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
              Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)) -
            (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
              Complex.exp (I * (((-v * Real.log n) : ℝ) : ℂ))‖ =
          ‖(weightedVonMangoldtMajorant eta k n : ℂ) * chi n‖ *
            ‖Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)) -
              Complex.exp (I * (((-v * Real.log n) : ℝ) : ℂ))‖ := by
            rw [← norm_mul]
            congr 1
            ring
        _ ≤ (weightedVonMangoldtMajorant eta k n * 1) *
              (|u - v| * Real.log n) := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hmajor0]
          exact mul_le_mul_of_nonneg_left hchi hmajor0
        _ = |u - v| * weightedVonMangoldtMajorant eta (k + 1) n := by
          unfold weightedVonMangoldtMajorant
          rw [pow_succ]
          ring
    _ = |u - v| *
        ∑ n ∈ Finset.Icc 1 N,
          weightedVonMangoldtMajorant eta (k + 1) n := by
      rw [Finset.mul_sum]

/-- Replacing the finite positive coefficient sum by the complete convergent
series gives a cutoff-independent Lipschitz bound. -/
theorem norm_finiteZeroDetectorPolynomial_sub_le_tsum
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (heta : 0 < eta) (k N : ℕ) (u v : ℝ) :
    ‖finiteZeroDetectorPolynomial chi eta k N u -
        finiteZeroDetectorPolynomial chi eta k N v‖ ≤
      |u - v| *
        ∑' n, weightedVonMangoldtMajorant eta (k + 1) n := by
  refine (norm_finiteZeroDetectorPolynomial_sub_le chi eta k N u v).trans ?_
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (summable_weightedVonMangoldtMajorant eta heta (k + 1)).sum_le_tsum
    (Finset.Icc 1 N) (fun n hn ↦ by
      unfold weightedVonMangoldtMajorant
      positivity)

/-- A single positive relative radius works for every derivative order up
to `J`.  This is the numerical budget behind interval propagation. -/
theorem detector_propagation_budget
    (J j : ℕ) (hJ : 1 ≤ J) (hj : 1 ≤ j) (hjJ : j ≤ J)
    (eta : ℝ) (heta : 0 < eta) :
    let C : ℝ := Real.log 4 + 4
    let delta : ℝ :=
      (144 * C * (J : ℝ) * (4 : ℝ) ^ J)⁻¹
    delta * eta *
          (3 * C * j.factorial * (2 / eta) ^ j / eta) ≤
      (j - 1).factorial * (1 / 48 : ℝ) *
        (2 * eta)⁻¹ ^ j := by
  dsimp only
  let C : ℝ := Real.log 4 + 4
  let D : ℝ := 144 * C * (J : ℝ) * (4 : ℝ) ^ J
  let delta : ℝ := D⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hD : 0 < D := by dsimp [D]; positivity
  have hpow : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hjJ
  have hbase :
      (j : ℝ) * (4 : ℝ) ^ j ≤ (J : ℝ) * (4 : ℝ) ^ J := by
    exact mul_le_mul (by exact_mod_cast hjJ) hpow (by positivity) (by positivity)
  have hcoef :
      delta * 3 * C * (j : ℝ) * (2 : ℝ) ^ j ≤
        1 / (48 * (2 : ℝ) ^ j) := by
    rw [le_div_iff₀ (by positivity : 0 < 48 * (2 : ℝ) ^ j)]
    calc
      delta * 3 * C * (j : ℝ) * (2 : ℝ) ^ j *
          (48 * (2 : ℝ) ^ j) =
        ((j : ℝ) * (4 : ℝ) ^ j) /
          ((J : ℝ) * (4 : ℝ) ^ J) := by
            dsimp [delta, D]
            rw [div_eq_mul_inv]
            field_simp
            rw [pow_two, ← mul_pow]
            ring
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hbase
  have hfac :
      (j.factorial : ℝ) = (j : ℝ) * ((j - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : j ≠ 0)).symm
  have hetaPow : 0 ≤ eta⁻¹ ^ j := by positivity
  have hmain :
      delta * 3 * C * (j.factorial : ℝ) * (2 : ℝ) ^ j *
          eta⁻¹ ^ j ≤
        (1 / (48 * (2 : ℝ) ^ j)) *
          ((j - 1).factorial : ℝ) * eta⁻¹ ^ j := by
    calc
      delta * 3 * C * (j.factorial : ℝ) * (2 : ℝ) ^ j *
          eta⁻¹ ^ j =
        (delta * 3 * C * (j : ℝ) * (2 : ℝ) ^ j) *
          ((j - 1).factorial : ℝ) * eta⁻¹ ^ j := by
            rw [hfac]
            ring
      _ ≤ (1 / (48 * (2 : ℝ) ^ j)) *
          ((j - 1).factorial : ℝ) * eta⁻¹ ^ j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hetaPow
  change
    (144 * C * (J : ℝ) * (4 : ℝ) ^ J)⁻¹ * eta *
          (3 * C * j.factorial * (2 / eta) ^ j / eta) ≤ _
  have hleft :
      (144 * C * (J : ℝ) * (4 : ℝ) ^ J)⁻¹ * eta *
          (3 * C * j.factorial * (2 / eta) ^ j / eta) =
        delta * 3 * C * (j.factorial : ℝ) * (2 : ℝ) ^ j *
          eta⁻¹ ^ j := by
    dsimp [delta, D]
    rw [div_pow, inv_pow]
    field_simp [heta.ne']
  have hright :
      ((j - 1).factorial : ℝ) * (1 / 48 : ℝ) *
          (2 * eta)⁻¹ ^ j =
        (1 / (48 * (2 : ℝ) ^ j)) *
          ((j - 1).factorial : ℝ) * eta⁻¹ ^ j := by
    rw [mul_inv_rev, mul_pow, inv_pow]
    field_simp [heta.ne']
    rw [← mul_pow]
    norm_num
  rw [hleft, hright]
  exact hmain

/-- Every detected zero produces an interval, of radius a fixed positive
multiple of `eta`, on which one of the finitely many detector polynomials
keeps at least half of its pointwise lower bound. -/
theorem exists_uniform_propagated_finite_series_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
              eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda →
                ∀ rho₀ : ℂ,
                  DirichletCharacter.LFunction chi rho₀ = 0 →
                  dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                    ∃ j : ℕ,
                      L ≤ j ∧ j ≤ J ∧
                        ∀ u : ℝ, |u - t| ≤ delta * eta →
                          (j - 1).factorial * (1 / 48 : ℝ) *
                              (2 * eta)⁻¹ ^ j <
                            ‖finiteZeroDetectorPolynomial chi eta (j - 1)
                              (zeroDetectorCutoff R eta) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, hlambda, hR, hdetector⟩ :=
    exists_uniform_finite_series_detector
  let C : ℝ := Real.log 4 + 4
  let delta : ℝ :=
    (144 * C * (J : ℝ) * (4 : ℝ) ^ J)⁻¹
  have hJ : 1 ≤ J := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta1 : delta ≤ 1 := by
    have hC1 : (1 : ℝ) ≤ C := by
      dsimp [C]
      have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      linarith
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hpow1 : (1 : ℝ) ≤ (4 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    apply inv_le_one_of_one_le₀
    calc
      (1 : ℝ) ≤ 144 * 1 * 1 * 1 := by norm_num
      _ ≤ 144 * C * (J : ℝ) * (4 : ℝ) ^ J := by gcongr
  refine ⟨L, J, hL2, hLJ, lambda, R, delta,
    hlambda, hR, hdelta, hdelta1, ?_⟩
  intro q _ hq chi hchi t eta heta heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjlargeRaw⟩ :=
    hdetector q hq chi hchi t eta heta heta8 hetalog rho₀ hzero hrho
  have hj : 1 ≤ j := by omega
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℝ → ℂ := fun u ↦
    finiteZeroDetectorPolynomial chi eta (j - 1) N u
  let B : ℝ := (j - 1).factorial * (1 / 48 : ℝ) *
    (2 * eta)⁻¹ ^ j
  have htlarge : 2 * B < ‖P t‖ := by
    have hdouble :
        2 * B = (j - 1).factorial * (1 / 24 : ℝ) *
          (2 * eta)⁻¹ ^ j := by
      dsimp [B]
      ring
    rw [hdouble]
    rw [show P t =
        ∑ n ∈ Finset.Icc 1 N,
          LSeries.term (fun m : ℕ ↦
            (Real.log m : ℂ) ^ (j - 1) * chi m *
              (ArithmeticFunction.vonMangoldt m : ℂ))
            (((1 + eta : ℝ) : ℂ) + t * I) n by
      dsimp [P]
      exact (weighted_vonMangoldt_LSeries_sum_eq_polynomial
        chi eta t (j - 1) N).symm]
    simpa only [N] using hjlargeRaw
  refine ⟨j, hjL, hjJ, ?_⟩
  intro u hu
  have heta1 : eta ≤ 1 := by linarith
  have hsum := weightedVonMangoldtMajorant_tsum_le
    eta heta heta1 j
  have hsum0 :
      0 ≤ ∑' n, weightedVonMangoldtMajorant eta j n :=
    tsum_nonneg fun n ↦ by
      unfold weightedVonMangoldtMajorant
      positivity
  have htu : |t - u| ≤ delta * eta := by
    simpa only [abs_sub_comm] using hu
  have hlip := norm_finiteZeroDetectorPolynomial_sub_le_tsum
    chi eta heta (j - 1) N t u
  have hlip' :
      ‖finiteZeroDetectorPolynomial chi eta (j - 1) N t -
          finiteZeroDetectorPolynomial chi eta (j - 1) N u‖ ≤
        |t - u| *
          ∑' n, weightedVonMangoldtMajorant eta j n := by
    simpa only [show j - 1 + 1 = j by omega] using hlip
  have hdiff : ‖P t - P u‖ ≤ B := by
    change ‖finiteZeroDetectorPolynomial chi eta (j - 1) N t -
      finiteZeroDetectorPolynomial chi eta (j - 1) N u‖ ≤ B
    refine hlip'.trans ((mul_le_mul htu hsum hsum0
      (by positivity)).trans ?_)
    have hbudget := detector_propagation_budget
      J j hJ hj hjJ eta heta
    simpa only [C, delta, show j - 1 + 1 = j by omega, B]
      using hbudget
  have htri : ‖P t‖ ≤ ‖P u‖ + ‖P t - P u‖ := by
    calc
      ‖P t‖ = ‖P u + (P t - P u)‖ := by congr 1; ring
      _ ≤ ‖P u‖ + ‖P t - P u‖ := norm_add_le _ _
  dsimp [B] at htlarge hdiff ⊢
  linarith

end

end Erdos48
