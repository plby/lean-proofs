/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This file contains statements related to Erdős Problem 119.
https://www.erdosproblems.com/119

The statements are adapted from the Formal Conjectures project:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/119.lean
-/

import Mathlib

open Filter Finset Set
open Metric

namespace Erdos119

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  sSup {‖p z n w‖ | (w : ℂ) (_ : ‖w‖ = 1)}

lemma p_differentiable (z : ℕ → ℂ) (n : ℕ) : Differentiable ℂ (p z n) := by
  unfold p
  fun_prop

lemma p_diffContOnCl (z : ℕ → ℂ) (n : ℕ) :
    DiffContOnCl ℂ (p z n) (ball 0 1) :=
  (p_differentiable z n).diffContOnCl

lemma norm_p_le_two_pow (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖p z n w‖ ≤ 2 ^ n := by
  simp only [p, norm_prod]
  calc
    ∏ i ∈ range n, ‖w - z i‖
        ≤ ∏ _i ∈ range n, (2 : ℝ) := by
          apply Finset.prod_le_prod
          · exact fun i hi => norm_nonneg _
          · intro i hi
            calc
              ‖w - z i‖ ≤ ‖w‖ + ‖z i‖ := norm_sub_le _ _
              _ = 2 := by rw [hw, hz]; norm_num
    _ = 2 ^ n := by simp

lemma norm_p_le_M_of_norm_eq_one (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖p z n w‖ ≤ M z n := by
  unfold M
  apply le_csSup
  · exact ⟨2 ^ n, by
      rintro y ⟨v, hv, rfl⟩
      exact norm_p_le_two_pow z hz n hv⟩
  · exact ⟨w, hw, rfl⟩

lemma norm_p_le_M_of_norm_le_one (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖p z n w‖ ≤ M z n := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := ball (0 : ℂ) 1) isBounded_ball (p_diffContOnCl z n)
      (C := M z n)
  · intro v hv
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), mem_sphere_iff_norm] at hv
    simpa using norm_p_le_M_of_norm_eq_one z hz n hv
  · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa [mem_closedBall] using hw

lemma norm_p_zero (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    ‖p z n 0‖ = 1 := by
  simp [p, norm_prod, hz]

lemma one_le_M (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    1 ≤ M z n := by
  rw [← norm_p_zero z hz n]
  exact norm_p_le_M_of_norm_le_one z hz n (by simp)

noncomputable def logPotential (z : ℕ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ range n, Complex.log (1 - w * (z i)⁻¹)

noncomputable def powerSum (z : ℕ → ℂ) (n m : ℕ) : ℂ :=
  ∑ i ∈ range n, (z i)⁻¹ ^ m

lemma unit_ne_zero (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (i : ℕ) : z i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [hz]; norm_num)

lemma one_sub_mul_inv_ne_zero (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (i : ℕ) :
    1 - w * (z i)⁻¹ ≠ 0 := by
  intro h
  have heq : w * (z i)⁻¹ = 1 := by
    rw [sub_eq_zero] at h
    exact h.symm
  have hnorm := congrArg norm heq
  simp [hz] at hnorm
  linarith

lemma p_eq_unit_mul_factors (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) (w : ℂ) :
    p z n w =
      (∏ i ∈ range n, -z i) * ∏ i ∈ range n, (1 - w * (z i)⁻¹) := by
  rw [p, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  field_simp [unit_ne_zero z hz i]
  ring

lemma norm_p_eq_prod_factors (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) (w : ℂ) :
    ‖p z n w‖ = ∏ i ∈ range n, ‖1 - w * (z i)⁻¹‖ := by
  rw [p_eq_unit_mul_factors z hz, norm_mul, norm_prod]
  simp [hz]

lemma logPotential_re (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    (logPotential z n w).re = Real.log ‖p z n w‖ := by
  rw [logPotential, Complex.re_sum]
  simp_rw [Complex.log_re]
  rw [norm_p_eq_prod_factors z hz, Real.log_prod]
  intro i hi
  exact norm_ne_zero_iff.mpr (one_sub_mul_inv_ne_zero z hz hw i)

lemma logPotential_zero (z : ℕ → ℂ) (n : ℕ) :
    logPotential z n 0 = 0 := by
  simp [logPotential]

lemma logPotential_differentiableOn (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) :
    DifferentiableOn ℂ (logPotential z n) (ball 0 1) := by
  intro w hw
  simp only [mem_ball, dist_zero_right] at hw
  unfold logPotential
  rw [show (fun w ↦ ∑ i ∈ range n, Complex.log (1 - w * (z i)⁻¹)) =
      ∑ i ∈ range n, fun w ↦ Complex.log (1 - w * (z i)⁻¹) by
        ext v
        simp]
  apply DifferentiableWithinAt.sum
  intro i hi
  have hslit : 1 - w * (z i)⁻¹ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre : (w * (z i)⁻¹).re ≤ ‖w * (z i)⁻¹‖ := Complex.re_le_norm _
    rw [norm_mul, norm_inv, hz i, inv_one, mul_one] at hre
    change 0 < 1 - (w * (z i)⁻¹).re
    linarith
  have hinner : DifferentiableAt ℂ (fun v : ℂ ↦ 1 - v * (z i)⁻¹) w := by
    fun_prop
  exact ((Complex.differentiableAt_log hslit).comp w hinner).differentiableWithinAt

lemma logPotential_re_le_log_M (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (logPotential z n w).re ≤ Real.log (M z n) := by
  have hw' : ‖w‖ < 1 := by simpa [mem_ball] using hw
  rw [logPotential_re z hz n hw']
  have hp_pos : 0 < ‖p z n w‖ := by
    rw [norm_p_eq_prod_factors z hz]
    exact Finset.prod_pos fun i hi =>
      norm_pos_iff.mpr (one_sub_mul_inv_ne_zero z hz hw' i)
  exact Real.log_le_log hp_pos
    (norm_p_le_M_of_norm_le_one z hz n hw'.le)

lemma iteratedDeriv_div_factorial_log_one_add_mul (a : ℂ) (m : ℕ) :
    iteratedDeriv m (fun w : ℂ ↦ Complex.log (1 + a * w)) 0 / (m.factorial : ℂ) =
      (-(-1 : ℂ) ^ m / m) * a ^ m := by
  let u : ℂ →L[ℂ] ℂ := a • ContinuousLinearMap.id ℂ ℂ
  have hp :
      HasFPowerSeriesAt
        ((fun x : ℂ ↦ Complex.log (1 + x)) ∘ u)
        ((FormalMultilinearSeries.ofScalars ℂ
          (fun n ↦ -(-1 : ℂ) ^ n / n)).compContinuousLinearMap u) 0 := by
    have hbase :
        HasFPowerSeriesAt (fun x : ℂ ↦ Complex.log (1 + x))
          (FormalMultilinearSeries.ofScalars ℂ
            (fun n ↦ -(-1 : ℂ) ^ n / n)) (u 0) := by
      simpa [u] using hasFPowerSeriesAt_clog_one_add
    exact hbase.compContinuousLinearMap
  have hcanonical := hp.analyticAt.hasFPowerSeriesAt
  have heq := hp.eq_formalMultilinearSeries hcanonical
  have happ := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff m) heq
  have hcoeff :
      ((FormalMultilinearSeries.ofScalars ℂ
          (fun n ↦ -(-1 : ℂ) ^ n / n)).compContinuousLinearMap u).coeff m =
        (-(-1 : ℂ) ^ m / m) * a ^ m := by
    unfold FormalMultilinearSeries.coeff
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [u, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars, Finset.prod_const]
    ring
  rw [hcoeff] at happ
  simpa [Function.comp_def, u] using happ.symm

lemma iteratedDeriv_div_factorial_logPotential (z : ℕ → ℂ) (n m : ℕ) :
    iteratedDeriv m (logPotential z n) 0 / (m.factorial : ℂ) =
      -powerSum z n m / m := by
  have hsum :
      iteratedDeriv m (logPotential z n) 0 =
        ∑ i ∈ range n,
          iteratedDeriv m (fun w : ℂ ↦
            Complex.log (1 - w * (z i)⁻¹)) 0 := by
    unfold logPotential
    apply iteratedDeriv_fun_sum
    intro i hi
    have hinner : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w * (z i)⁻¹) 0 := by
      fun_prop
    exact ((analyticAt_clog (by simp)).comp hinner).contDiffAt
  rw [hsum, Finset.sum_div]
  have heq (i : ℕ) :
      (fun w : ℂ ↦ Complex.log (1 - w * (z i)⁻¹)) =
        fun w : ℂ ↦ Complex.log (1 + (-(z i)⁻¹) * w) := by
    funext w
    congr 1
    ring
  simp_rw [heq, iteratedDeriv_div_factorial_log_one_add_mul]
  unfold powerSum
  ring_nf
  have hneg : (-1 : ℂ) ^ (m * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  simp [hneg, Finset.mul_sum]

lemma norm_powerSum_le (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n m : ℕ) (hm : 1 ≤ m) :
    ‖powerSum z n m‖ ≤ 6 * (m : ℝ) ^ 2 * (Real.log (M z n) + 1) := by
  let q : ℝ := (m : ℝ) / (m + 1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact div_lt_one (by positivity) |>.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log (M z n) :=
    Real.log_nonneg (one_le_M z hz n)
  have hA0 : 0 < Real.log (M z n) + 1 := by linarith
  have hmap :
      MapsTo (logPotential z n) (ball (0 : ℂ) 1)
        {w : ℂ | w.re ≤ Real.log (M z n) + 1} := by
    intro w hw
    exact (logPotential_re_le_log_M z hz n hw).trans (by linarith)
  have hsphere :
      ∀ w ∈ sphere (0 : ℂ) q,
        ‖logPotential z n w‖ ≤
          2 * (Real.log (M z n) + 1) * (m : ℝ) := by
    intro w hw
    have hwnorm : ‖w‖ = q := by
      simpa [mem_sphere_iff_norm] using hw
    have hwball : w ∈ ball (0 : ℂ) 1 := by
      simpa [mem_ball, hwnorm] using hq1
    calc
      ‖logPotential z n w‖
          ≤ 2 * (Real.log (M z n) + 1) * ‖w‖ / (1 - ‖w‖) :=
            Complex.borelCaratheodory_zero hA0
              (logPotential_differentiableOn z hz n) hmap (by norm_num)
              hwball (logPotential_zero z n)
      _ = 2 * (Real.log (M z n) + 1) * (m : ℝ) := by
        rw [hwnorm]
        dsimp [q]
        field_simp
        ring
  have hdiffcl :
      DiffContOnCl ℂ (logPotential z n) (ball (0 : ℂ) q) := by
    apply (logPotential_differentiableOn z hz n).diffContOnCl_ball
    intro w hw
    have hwnorm : ‖w‖ ≤ q := by
      simpa [mem_closedBall] using hw
    simpa [mem_ball] using hwnorm.trans_lt hq1
  have hderiv :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      m hq0 hdiffcl hsphere
  have hcoeff := iteratedDeriv_div_factorial_logPotential z n m
  have hfac0 : (0 : ℝ) < m.factorial := by positivity
  have hmcast0 : (0 : ℝ) < m := hm0
  have hnormcoeff :
      ‖iteratedDeriv m (logPotential z n) 0‖ / (m.factorial : ℝ) =
        ‖powerSum z n m‖ / (m : ℝ) := by
    have := congrArg norm hcoeff
    simpa [norm_div, Nat.cast_ofNat, hmcast0.ne', hfac0.ne',
      Real.norm_of_nonneg hfac0.le, Real.norm_of_nonneg hmcast0.le] using this
  have hqpow :
      q ^ m ≥ (1 / 3 : ℝ) := by
    have hplus : (1 + (m : ℝ)⁻¹) ^ m < 3 :=
      (Real.one_add_inv_pow_le_exp (n := m)).trans_lt Real.exp_one_lt_three
    have hqeq : q = (1 + (m : ℝ)⁻¹)⁻¹ := by
      dsimp [q]
      field_simp
    rw [hqeq, inv_pow]
    simpa [one_div] using
      (inv_le_inv₀ (by positivity : (0 : ℝ) < 3)
        (by positivity : 0 < (1 + (m : ℝ)⁻¹) ^ m)).mpr hplus.le
  have hnormalized :
    ‖iteratedDeriv m (logPotential z n) 0‖ / (m.factorial : ℝ)
        ≤ 6 * (m : ℝ) * (Real.log (M z n) + 1) := by
    calc
      ‖iteratedDeriv m (logPotential z n) 0‖ / (m.factorial : ℝ)
          ≤ (2 * (Real.log (M z n) + 1) * (m : ℝ)) / q ^ m := by
          apply (div_le_iff₀ hfac0).mpr
          calc
            ‖iteratedDeriv m (logPotential z n) 0‖
                ≤ (m.factorial : ℝ) *
                    (2 * (Real.log (M z n) + 1) * (m : ℝ)) / q ^ m := hderiv
            _ = ((2 * (Real.log (M z n) + 1) * (m : ℝ)) / q ^ m) *
                  (m.factorial : ℝ) := by ring
      _ ≤ 6 * (m : ℝ) * (Real.log (M z n) + 1) := by
        rw [div_le_iff₀ (pow_pos hq0 m)]
        calc
          2 * (Real.log (M z n) + 1) * (m : ℝ)
              = (6 * (m : ℝ) * (Real.log (M z n) + 1)) * (1 / 3) := by ring
          _ ≤ (6 * (m : ℝ) * (Real.log (M z n) + 1)) * q ^ m :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
  calc
    ‖powerSum z n m‖
        = (‖powerSum z n m‖ / (m : ℝ)) * (m : ℝ) := by
          field_simp
    _ = (‖iteratedDeriv m (logPotential z n) 0‖ /
          (m.factorial : ℝ)) * (m : ℝ) := by rw [hnormcoeff]
    _ ≤ (6 * (m : ℝ) * (Real.log (M z n) + 1)) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hnormalized hm0.le
    _ = 6 * (m : ℝ) ^ 2 * (Real.log (M z n) + 1) := by ring

noncomputable def pairCos (z : ℕ → ℂ) (n m : ℕ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, ((z j * (z i)⁻¹) ^ m).re

lemma two_mul_pairCos (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n m : ℕ) :
    2 * pairCos z n m = ‖powerSum z n m‖ ^ 2 - n := by
  induction n with
  | zero =>
      simp [pairCos, powerSum]
  | succ n ih =>
      rw [pairCos, sum_range_succ, powerSum, sum_range_succ]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
      rw [← Complex.normSq_eq_norm_sq] at ih
      have hunit : Complex.normSq ((z n)⁻¹ ^ m) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_pow, norm_inv, hz]
        simp
      rw [hunit]
      have hcross :
          ((∑ i ∈ range n, (z i)⁻¹ ^ m) *
              (starRingEnd ℂ) ((z n)⁻¹ ^ m)).re =
            ∑ i ∈ range n, ((z n * (z i)⁻¹) ^ m).re := by
        rw [Finset.sum_mul]
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        rw [map_pow, map_inv₀, ← Complex.inv_eq_conj (hz n)]
        field_simp [unit_ne_zero z hz n]
        ring
      rw [hcross]
      dsimp [pairCos, powerSum] at ih ⊢
      push_cast
      linarith

noncomputable def pairEnergy (z : ℕ → ℂ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, Real.log ‖(r : ℂ) * z j - z i‖

lemma norm_radial_sub_eq (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (r : ℝ) (i j : ℕ) :
    ‖(r : ℂ) * z j - z i‖ =
      ‖1 - (r : ℂ) * (z j * (z i)⁻¹)‖ := by
  have heq :
      (r : ℂ) * z j - z i =
        (-z i) * (1 - (r : ℂ) * (z j * (z i)⁻¹)) := by
    field_simp [unit_ne_zero z hz i]
    ring
  rw [heq, norm_mul, norm_neg, hz]
  simp

lemma hasSum_log_radial_sub (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (i j : ℕ) :
    HasSum
      (fun m : ℕ ↦ -(r ^ m * ((z j * (z i)⁻¹) ^ m).re / m))
      (Real.log ‖(r : ℂ) * z j - z i‖) := by
  let u : ℂ := z j * (z i)⁻¹
  have hu : ‖u‖ = 1 := by simp [u, hz]
  have hnorm : ‖(r : ℂ) * u‖ < 1 := by
    simp [hu, Real.norm_of_nonneg hr0, hr1]
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hnorm)
  have hsneg := hs.neg
  rw [norm_radial_sub_eq z hz]
  simpa only [u, ← Complex.ofReal_pow, Complex.div_natCast_re,
    Complex.ofReal_re, mul_pow, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.neg_re, neg_neg, Complex.log_re] using hsneg

lemma hasSum_pairEnergy (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum
      (fun m : ℕ ↦ r ^ m / (2 * m) * ((n : ℝ) - ‖powerSum z n m‖ ^ 2))
      (pairEnergy z n r) := by
  have hs :
      HasSum
        (fun m : ℕ ↦
          ∑ j ∈ range n, ∑ i ∈ range j,
            -(r ^ m * ((z j * (z i)⁻¹) ^ m).re / m))
        (pairEnergy z n r) := by
    simpa [pairEnergy] using
      (hasSum_sum fun j (_hj : j ∈ range n) =>
        hasSum_sum fun i (_hi : i ∈ range j) =>
          hasSum_log_radial_sub z hz hr0 hr1 i j)
  convert hs using 1
  funext m
  rw [show (n : ℝ) - ‖powerSum z n m‖ ^ 2 =
      -2 * pairCos z n m by
        linarith [two_mul_pairCos z hz n m]]
  simp only [pairCos]
  simp [Finset.mul_sum]
  ring_nf

lemma radial_sub_ne_zero (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (i j : ℕ) :
    (r : ℂ) * z j - z i ≠ 0 := by
  intro h
  have heq : (r : ℂ) * z j = z i := sub_eq_zero.mp h
  have hnorm := congrArg (fun w : ℂ => ‖w‖) heq
  simp [hz, Real.norm_of_nonneg hr0] at hnorm
  linarith

lemma prefix_log_le_log_M (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    ∑ i ∈ range j, Real.log ‖(r : ℂ) * z j - z i‖ ≤
      Real.log (M z j) := by
  have hw : ‖(r : ℂ) * z j‖ ≤ 1 := by
    simp [hz, Real.norm_of_nonneg hr0, hr1.le]
  have hp_le :=
    norm_p_le_M_of_norm_le_one z hz j (w := (r : ℂ) * z j) hw
  have hp_pos : 0 < ‖p z j ((r : ℂ) * z j)‖ := by
    rw [p, norm_prod]
    exact Finset.prod_pos fun i hi =>
      norm_pos_iff.mpr (radial_sub_ne_zero z hz hr0 hr1 i j)
  calc
    ∑ i ∈ range j, Real.log ‖(r : ℂ) * z j - z i‖
        = Real.log ‖p z j ((r : ℂ) * z j)‖ := by
          rw [p, norm_prod, Real.log_prod]
          intro i hi
          exact norm_ne_zero_iff.mpr
            (radial_sub_ne_zero z hz hr0 hr1 i j)
    _ ≤ Real.log (M z j) := Real.log_le_log hp_pos hp_le

lemma pairEnergy_le_sum_log_M (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    pairEnergy z n r ≤ ∑ j ∈ range n, Real.log (M z j) := by
  unfold pairEnergy
  exact Finset.sum_le_sum fun j hj =>
    prefix_log_le_log_M z hz hr0 hr1 j

lemma cube_le_six_choose (m : ℕ) :
    m ^ 3 ≤ 6 * (m + 3).choose 3 := by
  calc
    m ^ 3 ≤ (m + 3).descFactorial 3 := by
      norm_num [Nat.descFactorial_succ]
      have hsub : m + 3 - 2 = m + 1 := by omega
      rw [hsub]
      nlinarith
    _ = Nat.factorial 3 * (m + 3).choose 3 :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    _ = 6 * (m + 3).choose 3 := by norm_num

set_option maxHeartbeats 800000 in
-- Normalizing the closed-form bound for this real `tsum` is typeclass-intensive.
lemma tsum_cube_mul_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' m : ℕ, (m : ℝ) ^ 3 * r ^ m ≤ 6 / (1 - r) ^ 4 := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hleft : Summable (fun m : ℕ ↦ (m : ℝ) ^ 3 * r ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hnorm
  have hright : Summable (fun m : ℕ ↦
      6 * ((m + 3).choose 3 : ℝ) * r ^ m) :=
    by
      simpa [mul_assoc] using
        (summable_choose_mul_geometric_of_norm_lt_one
          (R := ℝ) 3 hnorm).mul_left 6
  calc
    ∑' m : ℕ, (m : ℝ) ^ 3 * r ^ m
        ≤ ∑' m : ℕ, 6 * ((m + 3).choose 3 : ℝ) * r ^ m := by
          apply Summable.tsum_le_tsum
          · intro m
            gcongr
            exact_mod_cast cube_le_six_choose m
          · exact hleft
          · exact hright
    _ = 6 / (1 - r) ^ 4 := by
      rw [show (fun m : ℕ ↦ 6 * ((m + 3).choose 3 : ℝ) * r ^ m) =
          fun m : ℕ ↦ 6 * (((m + 3).choose 3 : ℝ) * r ^ m) by
            funext m
            ring]
      rw [tsum_mul_left]
      rw [tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 3 hnorm]
      ring

lemma hasSum_pow_div (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ ↦ r ^ m / m) (-Real.log (1 - r)) := by
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Real.norm_of_nonneg hr0] using hr1
  have hs := Complex.hasSum_re
    (Complex.hasSum_taylorSeries_neg_log hnorm)
  have hone : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    exact abs_of_pos (sub_pos.mpr hr1)
  simpa only [← Complex.ofReal_pow, Complex.div_natCast_re,
    Complex.ofReal_re, Complex.neg_re, Complex.log_re,
    hone, neg_neg] using hs

set_option maxHeartbeats 800000 in
-- The ordered infinite-sum comparison below triggers expensive typeclass normalization.
lemma pairEnergy_lower_bound (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
        18 * (Real.log (M z n) + 1) ^ 2 *
          (∑' m : ℕ, (m : ℝ) ^ 3 * r ^ m)
      ≤ pairEnergy z n r := by
  let A : ℝ := Real.log (M z n) + 1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have := Real.log_nonneg (one_le_M z hz n)
    linarith
  have hgeom : Summable (fun m : ℕ ↦ (m : ℝ) ^ 3 * r ^ m) := by
    apply summable_pow_mul_geometric_of_norm_lt_one 3
    simpa [Real.norm_of_nonneg hr0] using hr1
  have hpos : Summable (fun m : ℕ ↦
      (n : ℝ) / 2 * (r ^ m / m)) :=
    (hasSum_pow_div r hr0 hr1).summable.mul_left _
  have herr : Summable (fun m : ℕ ↦
      18 * A ^ 2 * ((m : ℝ) ^ 3 * r ^ m)) :=
    hgeom.mul_left _
  have hrhs : Summable (fun m : ℕ ↦
      (n : ℝ) / 2 * (r ^ m / m) -
        18 * A ^ 2 * ((m : ℝ) ^ 3 * r ^ m)) :=
    hpos.sub herr
  have henergy := hasSum_pairEnergy z hz n hr0 hr1
  have hpoint (m : ℕ) :
      (n : ℝ) / 2 * (r ^ m / m) -
          18 * A ^ 2 * ((m : ℝ) ^ 3 * r ^ m)
        ≤ r ^ m / (2 * m) * ((n : ℝ) - ‖powerSum z n m‖ ^ 2) := by
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    have hm1 : 1 ≤ m := hm
    have hS := norm_powerSum_le z hz n m hm1
    change ‖powerSum z n m‖ ≤ 6 * (m : ℝ) ^ 2 * A at hS
    have hB0 : 0 ≤ 6 * (m : ℝ) ^ 2 * A := by positivity
    have hSsq :
        ‖powerSum z n m‖ ^ 2 ≤
          36 * (m : ℝ) ^ 4 * A ^ 2 := by
      calc
        ‖powerSum z n m‖ ^ 2
            ≤ (6 * (m : ℝ) ^ 2 * A) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hB0).mpr hS
        _ = 36 * (m : ℝ) ^ 4 * A ^ 2 := by ring
    have hmul :
        r ^ m / (2 * (m : ℝ)) * ‖powerSum z n m‖ ^ 2 ≤
          r ^ m / (2 * (m : ℝ)) *
            (36 * (m : ℝ) ^ 4 * A ^ 2) :=
      mul_le_mul_of_nonneg_left hSsq (by positivity)
    calc
      (n : ℝ) / 2 * (r ^ m / m) -
            18 * A ^ 2 * ((m : ℝ) ^ 3 * r ^ m)
          = (n : ℝ) / 2 * (r ^ m / m) -
              r ^ m / (2 * (m : ℝ)) *
                (36 * (m : ℝ) ^ 4 * A ^ 2) := by
            field_simp
            ring
      _ ≤ (n : ℝ) / 2 * (r ^ m / m) -
            r ^ m / (2 * (m : ℝ)) * ‖powerSum z n m‖ ^ 2 :=
          sub_le_sub_left hmul _
      _ = r ^ m / (2 * m) *
            ((n : ℝ) - ‖powerSum z n m‖ ^ 2) := by
          field_simp
  have htsum :
      ∑' m : ℕ, ((n : ℝ) / 2 * (r ^ m / m) -
          18 * A ^ 2 * ((m : ℝ) ^ 3 * r ^ m))
        ≤ ∑' m : ℕ,
          r ^ m / (2 * m) * ((n : ℝ) - ‖powerSum z n m‖ ^ 2) :=
    Summable.tsum_le_tsum hpoint hrhs henergy.summable
  rw [henergy.tsum_eq] at htsum
  rw [hpos.tsum_sub herr, tsum_mul_left,
    (hasSum_pow_div r hr0 hr1).tsum_eq, tsum_mul_left] at htsum
  simpa [A] using htsum

lemma pairEnergy_lower_bound_explicit (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
        108 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 4
      ≤ pairEnergy z n r := by
  have hbase := pairEnergy_lower_bound z hz n hr0 hr1
  have hcube := tsum_cube_mul_geometric_le hr0 hr1
  have hA : 0 ≤ 18 * (Real.log (M z n) + 1) ^ 2 := by positivity
  calc
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
          108 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 4
        = (n : ℝ) / 2 * (-Real.log (1 - r)) -
          18 * (Real.log (M z n) + 1) ^ 2 *
            (6 / (1 - r) ^ 4) := by ring
    _ ≤ (n : ℝ) / 2 * (-Real.log (1 - r)) -
          18 * (Real.log (M z n) + 1) ^ 2 *
            (∑' m : ℕ, (m : ℝ) ^ 3 * r ^ m) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hcube hA) _
    _ ≤ pairEnergy z n r := hbase

lemma card_mul_exp_average_log_le_sum_M (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.exp
        ((∑ k ∈ range n, Real.log (M z k)) / n)
      ≤ ∑ k ∈ range n, M z k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw0 :
      ∀ i ∈ range n, 0 ≤ (1 / (n : ℝ)) := by
    intro i hi
    positivity
  have hw1 :
      ∑ i ∈ range n, (1 / (n : ℝ)) = 1 := by
    simp [hnR.ne']
  have hj := convexOn_exp.map_sum_le
    (t := range n) (w := fun _ : ℕ => 1 / (n : ℝ))
    (p := fun k => Real.log (M z k))
    hw0 hw1 (fun i hi => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hrewrite :
      ∑ i ∈ range n, (1 / (n : ℝ)) * Real.log (M z i) =
        (∑ i ∈ range n, Real.log (M z i)) / n := by
    rw [← Finset.mul_sum]
    ring
  rw [hrewrite] at hj
  have hright :
      ∑ i ∈ range n, (1 / (n : ℝ)) * Real.exp (Real.log (M z i)) =
        (∑ i ∈ range n, M z i) / n := by
    calc
      ∑ i ∈ range n, (1 / (n : ℝ)) * Real.exp (Real.log (M z i))
          = (1 / (n : ℝ)) *
              ∑ i ∈ range n, Real.exp (Real.log (M z i)) := by
                rw [Finset.mul_sum]
      _ = (1 / (n : ℝ)) * ∑ i ∈ range n, M z i := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_M z hz i))]
      _ = (∑ i ∈ range n, M z i) / n := by ring
  rw [hright] at hj
  simpa [mul_comm] using (le_div_iff₀ hnR).mp hj

lemma logarithmic_error_small_eventually :
    ∀ᶠ n : ℕ in atTop,
      108 * (2 * Real.log (n : ℝ) + 1) ^ 2 *
          (n : ℝ) ^ (1 / 4 : ℝ)
        ≤ (n : ℝ) * Real.log (n : ℝ) / 64 := by
  have hlog :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 1
  have hpow :
      ∀ᶠ n : ℕ in atTop,
        (64 * 117612 : ℝ) ≤ (n : ℝ) ^ (5 / 8 : ℝ) := by
    have ht0 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)
    have ht := ht0.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop _
  filter_upwards [hlog, hpow, Filter.eventually_ge_atTop 1] with n hnlog hnpow hn1
  let x : ℝ := n
  let q : ℝ := x ^ (1 / 16 : ℝ)
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn1
  have hx0 : 0 ≤ x := hx1.trans' zero_le_one
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hq0 : 0 ≤ q := Real.rpow_nonneg hx0 _
  have hq1 : 1 ≤ q :=
    Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hlogupper : Real.log x ≤ 16 * q := by
    have h := Real.log_le_rpow_div hx0
      (by norm_num : (0 : ℝ) < 1 / 16)
    dsimp [q]
    convert h using 1
    norm_num
    ring
  have hA : 2 * Real.log x + 1 ≤ 33 * q := by
    nlinarith
  have hA0 : 0 ≤ 2 * Real.log x + 1 := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    linarith
  have hAsq : (2 * Real.log x + 1) ^ 2 ≤ (33 * q) ^ 2 :=
    (sq_le_sq₀ hA0 (by positivity)).mpr hA
  have hq4 : q ^ 4 = x ^ (1 / 4 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hx0]
    norm_num
  have hq6_mul : q ^ 6 * x ^ (5 / 8 : ℝ) = x := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hx0]
    norm_num
    rw [← Real.rpow_add hxpos]
    norm_num
  have herr_le :
      108 * (2 * Real.log x + 1) ^ 2 * x ^ (1 / 4 : ℝ)
        ≤ 117612 * q ^ 6 := by
    rw [← hq4]
    nlinarith [pow_nonneg hq0 4]
  have hpower_le : 117612 * q ^ 6 ≤ x / 64 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    calc
      117612 * q ^ 6 * 64
          = q ^ 6 * (64 * 117612) := by ring
      _ ≤ q ^ 6 * x ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hnpow (pow_nonneg hq0 6)
      _ = x := hq6_mul
  have hresult :
      108 * (2 * Real.log x + 1) ^ 2 * x ^ (1 / 4 : ℝ)
        ≤ x * Real.log x / 64 :=
    herr_le.trans (hpower_le.trans <| by
      apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 64)).mpr
      nlinarith)
  simpa [x] using hresult

lemma sum_log_M_lower_of_terminal_small (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) (hn : 0 < n)
    (hlog_one : 1 ≤ Real.log (n : ℝ))
    (hterminal : Real.log (M z n) ≤ 2 * Real.log (n : ℝ))
    (herror :
      108 * (2 * Real.log (n : ℝ) + 1) ^ 2 *
          (n : ℝ) ^ (1 / 4 : ℝ)
        ≤ (n : ℝ) * Real.log (n : ℝ) / 64) :
    (n : ℝ) * Real.log (n : ℝ) / 64 ≤
      ∑ k ∈ range n, Real.log (M z k) := by
  let x : ℝ := n
  let q : ℝ := x ^ (1 / 16 : ℝ)
  let r : ℝ := 1 - q⁻¹
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast hn
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hqpos : 0 < q := Real.rpow_pos_of_pos hxpos _
  have hq1 : 1 ≤ q :=
    Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact sub_nonneg.mpr ((inv_le_one₀ hqpos).mpr hq1)
  have hr1 : r < 1 := by
    dsimp [r]
    linarith [inv_pos.mpr hqpos]
  have hone_sub : 1 - r = q⁻¹ := by
    dsimp [r]
    ring
  have hlog_kernel :
      -Real.log (1 - r) = Real.log x / 16 := by
    rw [hone_sub, Real.log_inv, show q = x ^ (1 / 16 : ℝ) by rfl,
      Real.log_rpow hxpos]
    ring
  have hq4 : q ^ 4 = x ^ (1 / 4 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hx0]
    norm_num
  have herror_kernel :
      108 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 4 =
        108 * (Real.log (M z n) + 1) ^ 2 * x ^ (1 / 4 : ℝ) := by
    rw [hone_sub, inv_pow, hq4]
    field_simp [(Real.rpow_pos_of_pos hxpos (1 / 4 : ℝ)).ne']
  have henergy := pairEnergy_lower_bound_explicit z hz n hr0 hr1
  rw [hlog_kernel, herror_kernel] at henergy
  have hA0 : 0 ≤ Real.log (M z n) + 1 := by
    have := Real.log_nonneg (one_le_M z hz n)
    linarith
  have hB0 : 0 ≤ 2 * Real.log (n : ℝ) + 1 := by linarith
  have hsq :
      (Real.log (M z n) + 1) ^ 2 ≤
        (2 * Real.log (n : ℝ) + 1) ^ 2 :=
    (sq_le_sq₀ hA0 hB0).mpr (by linarith)
  have herror' :
      108 * (Real.log (M z n) + 1) ^ 2 * x ^ (1 / 4 : ℝ)
        ≤ x * Real.log x / 64 := by
    have hxpow : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0 _
    calc
      108 * (Real.log (M z n) + 1) ^ 2 * x ^ (1 / 4 : ℝ)
          ≤ 108 * (2 * Real.log (n : ℝ) + 1) ^ 2 *
              x ^ (1 / 4 : ℝ) := by gcongr
      _ ≤ x * Real.log x / 64 := by simpa [x] using herror
  have hlower :
      x * Real.log x / 64 ≤ pairEnergy z n r := by
    calc
      x * Real.log x / 64
          ≤ (n : ℝ) / 2 * (Real.log x / 16) -
              108 * (Real.log (M z n) + 1) ^ 2 *
                x ^ (1 / 4 : ℝ) := by
            dsimp [x] at hlog_one ⊢
            nlinarith
      _ ≤ pairEnergy z n r := by simpa [x] using henergy
  have hpair := pairEnergy_le_sum_log_M z hz n hr0 hr1
  have hfinal := hlower.trans hpair
  simpa [x] using hfinal

lemma eventually_succ_rpow_lt_rpow {a b : ℝ}
    (hb : 0 < b) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) ^ b < (n : ℝ) ^ a := by
  have hlarge :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℝ) ^ b < (n : ℝ) ^ (a - b) := by
    have ht0 := tendsto_rpow_atTop (sub_pos.mpr hab)
    have ht := ht0.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_gt_atTop _
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with n hnlarge hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn1)
  have hn_nonneg : (0 : ℝ) ≤ n := hnR.le
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsucc :
      ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * n := by
    push_cast
    nlinarith
  calc
    ((n + 1 : ℕ) : ℝ) ^ b
        ≤ ((2 : ℝ) * n) ^ b :=
      Real.rpow_le_rpow (by positivity) hsucc hb.le
    _ = (2 : ℝ) ^ b * (n : ℝ) ^ b :=
      Real.mul_rpow (by positivity) hn_nonneg
    _ < (n : ℝ) ^ (a - b) * (n : ℝ) ^ b :=
      mul_lt_mul_of_pos_right hnlarge (Real.rpow_pos_of_pos hnR _)
    _ = (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

lemma eventually_sum_M_succ_gt (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ range (n + 1), M z k >
        ((n + 1 : ℕ) : ℝ) ^ (1 + (1 / 256 : ℝ)) := by
  have hlog :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 1
  have hsmallcompare :
      ∀ᶠ n : ℕ in atTop,
        ((n + 1 : ℕ) : ℝ) ^ (1 + (1 / 256 : ℝ)) <
          (n : ℝ) ^ (1 + (1 / 64 : ℝ)) := by
    convert eventually_succ_rpow_lt_rpow
      (a := 1 + (1 / 64 : ℝ)) (b := 1 + (1 / 256 : ℝ))
      (by norm_num) (by norm_num) using 1
  have hlargecompare :
      ∀ᶠ n : ℕ in atTop,
        ((n + 1 : ℕ) : ℝ) ^ (1 + (1 / 256 : ℝ)) <
          (n : ℝ) ^ (2 : ℝ) := by
    convert eventually_succ_rpow_lt_rpow
      (a := (2 : ℝ)) (b := 1 + (1 / 256 : ℝ))
      (by norm_num) (by norm_num) using 1
  filter_upwards [hlog, logarithmic_error_small_eventually,
    hsmallcompare, hlargecompare, Filter.eventually_gt_atTop 0] with
      n hnlog hnerror hnsmall hnlarge hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  by_cases hterminal :
      Real.log (M z n) ≤ 2 * Real.log (n : ℝ)
  · have hsumlog :=
      sum_log_M_lower_of_terminal_small z hz n hnpos hnlog hterminal hnerror
    have havg :
        Real.log (n : ℝ) / 64 ≤
          (∑ k ∈ range n, Real.log (M z k)) / n := by
      rw [le_div_iff₀ hnR]
      calc
        Real.log (n : ℝ) / 64 * (n : ℝ)
            = (n : ℝ) * Real.log (n : ℝ) / 64 := by ring
        _ ≤ ∑ k ∈ range n, Real.log (M z k) := hsumlog
    have hexp :
        (n : ℝ) ^ (1 / 64 : ℝ) ≤
          Real.exp ((∑ k ∈ range n, Real.log (M z k)) / n) := by
      rw [Real.rpow_def_of_pos hnR]
      apply Real.exp_le_exp.mpr
      convert havg using 1
      ring
    have hjensen := card_mul_exp_average_log_le_sum_M z hz n hnpos
    have hpow_le :
        (n : ℝ) ^ (1 + (1 / 64 : ℝ)) ≤
          ∑ k ∈ range n, M z k := by
      calc
        (n : ℝ) ^ (1 + (1 / 64 : ℝ))
            = (n : ℝ) * (n : ℝ) ^ (1 / 64 : ℝ) := by
              rw [Real.rpow_add hnR, Real.rpow_one]
        _ ≤ (n : ℝ) * Real.exp
              ((∑ k ∈ range n, Real.log (M z k)) / n) :=
            mul_le_mul_of_nonneg_left hexp hnR.le
        _ ≤ ∑ k ∈ range n, M z k := hjensen
    rw [sum_range_succ]
    exact hnsmall.trans_le (hpow_le.trans
      (le_add_of_nonneg_right (one_le_M z hz n |>.trans' zero_le_one)))
  · have hterminal' :
        2 * Real.log (n : ℝ) < Real.log (M z n) := lt_of_not_ge hterminal
    have hMlarge : (n : ℝ) ^ (2 : ℝ) < M z n := by
      have he := Real.exp_lt_exp.mpr hterminal'
      have ht2 :
          Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
        rw [show 2 * Real.log (n : ℝ) =
            Real.log ((n : ℝ) ^ 2) by
              rw [Real.log_pow]
              norm_num]
        rw [Real.exp_log (pow_pos hnR 2)]
      rw [ht2, Real.exp_log
        (lt_of_lt_of_le zero_lt_one (one_le_M z hz n))] at he
      simpa [Real.rpow_natCast] using he
    rw [sum_range_succ]
    have hsum0 : 0 ≤ ∑ k ∈ range n, M z k :=
      Finset.sum_nonneg fun k hk => (one_le_M z hz k).trans' zero_le_one
    exact hnlarge.trans (lt_of_lt_of_le hMlarge (le_add_of_nonneg_left hsum0))

/-- Question 3:

Is it true that there exists $c > 0$ such that, for all large $n$,
$\sum_{k \leq n} M_k > n^{1 + c}$?

The proof below gives the affirmative answer with $c=1/256$.
-/
theorem erdos_119.parts.iii :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (_ : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c) := by
  intro z hz
  refine ⟨1 / 256, by norm_num, ?_⟩
  have hs := eventually_sum_M_succ_gt z hz
  have hshift :
      ∀ᶠ n : ℕ in atTop,
        ∑ k ∈ range ((n - 1) + 1), M z k >
          ((((n - 1) + 1 : ℕ) : ℝ) ^ (1 + (1 / 256 : ℝ))) :=
    (tendsto_sub_atTop_nat 1).eventually hs
  filter_upwards [hshift, Filter.eventually_gt_atTop 0] with n hn hnpos
  have hone : 1 ≤ n := hnpos
  simpa [Nat.sub_add_cancel hone] using hn

/-- Question 2:

Is it true that there exists $c > 0$ such that for infinitely many $n$ we have $M_n > n^c$?

Beck [Be91] proved that there exists some $c > 0$ such that $\max_{n \leq N} M_n > N^c$.

[Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős.
Annals of Math. (1991), 609--651.
-/
theorem erdos_119.parts.ii :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (_ : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
  intro z hz
  obtain ⟨c, hc, hsum⟩ := erdos_119.parts.iii z hz
  refine ⟨c, hc, Set.infinite_coe_iff.mpr ?_⟩
  have hlarge :
      ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k < n ∧ (n : ℝ) ^ c < M z k := by
    filter_upwards [hsum, Filter.eventually_gt_atTop 0] with n hn hn_pos
    by_contra h
    push Not at h
    have hsum_le :
        ∑ k ∈ range n, M z k ≤ (n : ℝ) * (n : ℝ) ^ c := by
      simpa using
        (Finset.sum_le_card_nsmul (range n) (M z) ((n : ℝ) ^ c)
          (fun k hk => h k (Finset.mem_range.mp hk)))
    have hrpow :
        (n : ℝ) ^ (1 + c) = (n : ℝ) * (n : ℝ) ^ c := by
      rw [Real.rpow_add (by positivity), Real.rpow_one]
    rw [hrpow] at hn
    exact (not_lt_of_ge hsum_le) hn
  by_contra h_infinite
  have hfinite : {n : ℕ | M z n > n ^ c}.Finite :=
    Set.not_infinite.mp h_infinite
  obtain ⟨B, hB⟩ := (hfinite.image (M z)).bddAbove
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn_large, hn_B⟩ :=
    (hlarge.and (hpow.eventually_gt_atTop B)).exists
  obtain ⟨k, hk_lt, hk_large⟩ := hn_large
  have hk_pow : (k : ℝ) ^ c ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk_lt.le) hc.le
  have hk_mem : k ∈ {n : ℕ | M z n > n ^ c} :=
    lt_of_le_of_lt hk_pow hk_large
  have hk_B : M z k ≤ B := hB ⟨k, hk_mem, rfl⟩
  exact (not_lt_of_ge hk_B) (hn_B.trans hk_large)

/-- Question 1:

Is it true that $\limsup M_n = \infty$?

Wagner [Wa80] proved that there is some $c > 0$ with $M_n > (\log n)^c$ infinitely often.

[Wa80] Wagner, Gerold, On a problem of Erdős in Diophantine approximation.
Bull. London Math. Soc. (1980), 81--88.
-/
theorem erdos_119.parts.i :
    ∀ (z : ℕ → ℂ) (_ : ∀ i : ℕ, ‖z i‖ = 1),
      atTop.limsup (fun n => (M z n : EReal)) = ⊤ := by
  intro z hz
  obtain ⟨c, hc, h_infinite⟩ := erdos_119.parts.ii z hz
  have hfreq :
      ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ c < M z n :=
    Nat.frequently_atTop_iff_infinite.mpr
      (Set.infinite_coe_iff.mp h_infinite)
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  refine (EReal.coe_lt_coe_iff.mpr (lt_add_one y)).trans_le
    (Filter.le_limsup_of_frequently_le' ?_)
  exact (hfreq.and_eventually (hpow.eventually_gt_atTop (y + 1))).mono
    (fun n hn => EReal.coe_le_coe_iff.mpr (hn.2.le.trans hn.1.le))

end Erdos119
