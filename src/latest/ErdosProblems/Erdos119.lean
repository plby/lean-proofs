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

noncomputable def rotationAverage (f : ℂ → ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j ∈ range m,
    f ((Complex.exp (2 * Real.pi * Complex.I / m)) ^ j * w)

lemma sum_root_powers {m k : ℕ} (hm : 0 < m) :
    ∑ j ∈ range m,
        ((Complex.exp (2 * Real.pi * Complex.I / m)) ^ j) ^ k =
      if m ∣ k then (m : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hζ : IsPrimitiveRoot ζ m :=
    Complex.isPrimitiveRoot_exp m hm.ne'
  change ∑ j ∈ range m, (ζ ^ j) ^ k = _
  split_ifs with hmk
  · have hpow : ζ ^ k = 1 := (hζ.pow_eq_one_iff_dvd k).mpr hmk
    calc
      ∑ j ∈ range m, (ζ ^ j) ^ k =
          ∑ j ∈ range m, (ζ ^ k) ^ j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← pow_mul, ← pow_mul, mul_comm j k]
      _ = m := by simp [hpow]
  · have hpow : ζ ^ k ≠ 1 := by
      simpa [hζ.pow_eq_one_iff_dvd k]
    have hgeom := geom_sum_mul (ζ ^ k) m
    have hmkpow : (ζ ^ k) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]
      simp
    have hzero :
        ∑ j ∈ range m, (ζ ^ k) ^ j = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr hpow)
      rw [hgeom, hmkpow, sub_self]
    calc
      ∑ j ∈ range m, (ζ ^ j) ^ k =
          ∑ j ∈ range m, (ζ ^ k) ^ j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← pow_mul, ← pow_mul, mul_comm j k]
      _ = 0 := hzero

lemma iteratedDeriv_rotationAverage
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    {m k : ℕ} (hm : 0 < m) :
    iteratedDeriv k (rotationAverage f m) 0 =
      (if m ∣ k then 1 else 0) * iteratedDeriv k f 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hζnorm : ‖ζ‖ = 1 := by
    dsimp [ζ]
    rw [Complex.norm_exp]
    simp
  have hfcont : ContDiffOn ℂ k f (ball 0 1) :=
    hf.contDiffOn isOpen_ball
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  rw [← iteratedDerivWithin_of_isOpen isOpen_ball hzero]
  unfold rotationAverage
  rw [iteratedDerivWithin_const_mul_field]
  rw [iteratedDerivWithin_fun_sum hzero isOpen_ball.uniqueDiffOn]
  · have hterm (j : ℕ) :
        iteratedDerivWithin k (fun w ↦ f (ζ ^ j * w)) (ball 0 1) 0 =
          (ζ ^ j) ^ k * iteratedDeriv k f 0 := by
      rw [iteratedDerivWithin_comp_const_smul hzero
        isOpen_ball.uniqueDiffOn hfcont (ζ ^ j)]
      · have heq :=
          iteratedDerivWithin_of_isOpen (f := f) (n := k) isOpen_ball hzero
        simpa only [mul_zero, smul_eq_mul] using
          congrArg (fun x : ℂ ↦ (ζ ^ j) ^ k * x) heq
      · intro w hw
        simpa [mem_ball, norm_mul, hζnorm] using hw
    simp_rw [show Complex.exp (2 * Real.pi * Complex.I / ↑m) = ζ by rfl,
      hterm]
    rw [← Finset.sum_mul, sum_root_powers hm]
    split_ifs with hmk
    · field_simp [hm.ne']
    · simp
  · intro j hj
    have hcomp :
        ContDiffWithinAt ℂ k (fun w ↦ f (ζ ^ j * w)) (ball 0 1) 0 :=
      (hfcont (ζ ^ j * 0) (by simpa using hzero)).comp (0 : ℂ) (by fun_prop) (by
        intro w hw
        simpa [mem_ball, norm_mul, hζnorm] using hw)
    simpa [ζ] using hcomp

lemma caratheodory_iteratedDeriv_bound
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) {A : ℝ} (hA : 0 < A)
    (hfre : ∀ w ∈ ball (0 : ℂ) 1, (f w).re ≤ A - 1)
    {m : ℕ} (hm : 0 < m) :
    ‖iteratedDeriv m f 0‖ / (m.factorial : ℝ) ≤ 2 * A := by
  let q : ℂ → ℂ := rotationAverage f m
  let d : ℂ → ℂ := fun w ↦ (2 * A : ℂ) - q w
  let h : ℂ → ℂ := fun w ↦ q w / d w
  have hζnorm :
      ‖Complex.exp (2 * Real.pi * Complex.I / m)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hrot (j : ℕ) :
      MapsTo
        (fun w : ℂ ↦
          Complex.exp (2 * Real.pi * Complex.I / m) ^ j * w)
        (ball 0 1) (ball 0 1) := by
    intro w hw
    simpa [mem_ball, norm_mul, hζnorm] using hw
  have hqdiff : DifferentiableOn ℂ q (ball 0 1) := by
    dsimp [q, rotationAverage]
    apply DifferentiableOn.const_mul
    rw [show
      (fun y ↦ ∑ j ∈ range m,
        f (Complex.exp (2 * Real.pi * Complex.I / ↑m) ^ j * y)) =
        ∑ j ∈ range m, fun y ↦
          f (Complex.exp (2 * Real.pi * Complex.I / ↑m) ^ j * y) by
            ext y
            simp]
    apply DifferentiableOn.sum
    intro j hj
    exact hf.comp (by fun_prop) (hrot j)
  have hq0 : q 0 = 0 := by
    simp [q, rotationAverage, hf0]
  have hqre (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      (q w).re ≤ A - 1 := by
    have hsum :
        (∑ j ∈ range m,
            f (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * w)).re
          ≤ (m : ℝ) * (A - 1) := by
      rw [Complex.re_sum]
      calc
        ∑ j ∈ range m,
              (f (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * w)).re
            ≤ ∑ _j ∈ range m, (A - 1) :=
          Finset.sum_le_sum fun j hj ↦ hfre _ (hrot j hw)
        _ = (m : ℝ) * (A - 1) := by
          simp
          ring
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    let S : ℂ :=
      ∑ j ∈ range m,
        f (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * w)
    have hsumS : S.re ≤ (m : ℝ) * (A - 1) := by
      simpa [S] using hsum
    dsimp [q, rotationAverage]
    rw [mul_comm (m : ℂ)⁻¹, ← div_eq_mul_inv]
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, mul_zero,
      zero_div, add_zero]
    have hmnorm : Complex.normSq (m : ℂ) = (m : ℝ) ^ 2 := by
      simp [Complex.normSq_apply]
      ring
    rw [hmnorm]
    change S.re * (m : ℝ) / (m : ℝ) ^ 2 ≤ A - 1
    calc
      S.re * (m : ℝ) / (m : ℝ) ^ 2 = S.re / (m : ℝ) := by
        field_simp
      _ ≤ ((m : ℝ) * (A - 1)) / (m : ℝ) :=
        (div_le_div_iff_of_pos_right hmR).mpr hsumS
      _ = A - 1 := by field_simp
  have hdne (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : d w ≠ 0 := by
    intro hd
    have heq : q w = (2 * A : ℂ) := by
      dsimp [d] at hd
      exact (sub_eq_zero.mp hd).symm
    have hre := hqre w hw
    rw [heq] at hre
    simp at hre
    linarith
  have hhdiff : DifferentiableOn ℂ h (ball 0 1) := by
    dsimp [h, d]
    exact hqdiff.div (hqdiff.const_sub _) hdne
  have hh0 : h 0 = 0 := by simp [h, hq0]
  have hhnorm (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      ‖h w‖ ≤ 1 := by
    have hre : (q w).re ≤ A := (hqre w hw).trans (by linarith)
    have hsq : ‖q w‖ ^ 2 ≤ ‖d w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [d, Complex.normSq_apply]
      nlinarith
    have hnorm : ‖q w‖ ≤ ‖d w‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    change ‖q w / d w‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hdne w hw))]
    exact hnorm
  have hhan : AnalyticAt ℂ h 0 :=
    hhdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hqan : AnalyticAt ℂ q 0 :=
    hqdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hqzero : ∀ k < m, iteratedDeriv k q 0 = 0 := by
    intro k hk
    rw [show q = rotationAverage f m by rfl,
      iteratedDeriv_rotationAverage hf hm]
    rcases k.eq_zero_or_pos with rfl | hk0
    · simpa using hf0
    · have hndvd : ¬m ∣ k :=
        fun hmk ↦ (not_le_of_gt hk) (Nat.le_of_dvd hk0 hmk)
      simp [hndvd]
  obtain ⟨g, hgan, hqfactor⟩ :=
    (natCast_le_analyticOrderAt hqan).mp
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hqan).mpr hqzero)
  have hdfan : AnalyticAt ℂ d 0 := by
    dsimp [d]
    fun_prop
  have hd0 : d 0 = (2 * A : ℂ) := by simp [d, hq0]
  have hdf0 : d 0 ≠ 0 := by
    rw [hd0]
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) hA).ne'
  have hhorder : m ≤ analyticOrderAt h 0 := by
    rw [natCast_le_analyticOrderAt hhan]
    refine ⟨fun w ↦ g w / d w, hgan.div hdfan hdf0, ?_⟩
    filter_upwards [hqfactor] with w hw
    dsimp [h]
    rw [hw]
    ring
  have hhzero : ∀ k < m, iteratedDeriv k h 0 = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hhan).mp hhorder
  have hproduct : (h * d) =ᶠ[nhds 0] q := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)] with w hw
    dsimp [h]
    exact div_mul_cancel₀ _ (hdne w hw)
  have hderiv_product := hproduct.iteratedDeriv_eq m
  rw [iteratedDeriv_mul hhan.contDiffAt hdfan.contDiffAt] at hderiv_product
  have hsum :
      ∑ i ∈ range (m + 1),
          (m.choose i : ℂ) * iteratedDeriv i h 0 *
            iteratedDeriv (m - i) d 0 =
        iteratedDeriv m h 0 * (2 * A : ℂ) := by
    rw [Finset.sum_eq_single m]
    · simp [hd0]
    · intro i hi him
      have hil : i < m := by
        have := Finset.mem_range.mp hi
        omega
      simp [hhzero i hil]
    · simp
  rw [hsum] at hderiv_product
  have hhcoeff :
      ‖iteratedDeriv m h 0‖ / (m.factorial : ℝ) ≤ 1 := by
    have hderiv :
        ‖iteratedDeriv m h 0‖ ≤ (m.factorial : ℝ) := by
      suffices ∀ᶠ r : ℝ in nhdsWithin 1 (Iio 1),
          ‖iteratedDeriv m h 0‖ ≤
            (m.factorial : ℝ) / r ^ m by
        refine ge_of_tendsto ?_ this
        have hc : ContinuousWithinAt
            (fun r : ℝ ↦ (m.factorial : ℝ) / r ^ m) (Iio 1) 1 :=
          (show ContinuousAt
              (fun r : ℝ ↦ (m.factorial : ℝ) / r ^ m) 1 by
            fun_prop (disch := norm_num)).continuousWithinAt
        simpa only [ContinuousWithinAt, one_pow, div_one] using hc
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
      have hdiffcl : DiffContOnCl ℂ h (ball (0 : ℂ) r) := by
        apply hhdiff.diffContOnCl_ball
        intro w hw
        have hwnorm : ‖w‖ ≤ r := by
          simpa [mem_closedBall] using hw
        simpa [mem_ball] using hwnorm.trans_lt hr.2
      have hsphere :
          ∀ w ∈ sphere (0 : ℂ) r, ‖h w‖ ≤ 1 := by
        intro w hw
        apply hhnorm w
        have hwnorm : ‖w‖ = r := by
          simpa [mem_sphere_iff_norm] using hw
        simpa [mem_ball, hwnorm] using hr.2
      simpa using
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          m hr.1 hdiffcl hsphere
    exact (div_le_one (by positivity : (0 : ℝ) < m.factorial)).mpr hderiv
  have hqderiv :
      iteratedDeriv m q 0 = iteratedDeriv m f 0 := by
    rw [show q = rotationAverage f m by rfl,
      iteratedDeriv_rotationAverage hf hm]
    simp
  have hfacpos : (0 : ℝ) < m.factorial := by positivity
  have hnorm2A : ‖(2 * A : ℂ)‖ = 2 * A := by
    simp [Real.norm_of_nonneg hA.le]
  rw [← hqderiv, ← hderiv_product, norm_mul, hnorm2A]
  calc
    ‖iteratedDeriv m h 0‖ * (2 * A) / (m.factorial : ℝ)
        = (‖iteratedDeriv m h 0‖ / (m.factorial : ℝ)) * (2 * A) := by
          ring
    _ ≤ 1 * (2 * A) :=
      mul_le_mul_of_nonneg_right hhcoeff (by positivity)
    _ = 2 * A := one_mul _

lemma norm_powerSum_le_linear (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (n m : ℕ) (hm : 1 ≤ m) :
    ‖powerSum z n m‖ ≤
      2 * (m : ℝ) * (Real.log (M z n) + 1) := by
  have hA0 : 0 < Real.log (M z n) + 1 := by
    have := Real.log_nonneg (one_le_M z hz n)
    linarith
  have hcar :=
    caratheodory_iteratedDeriv_bound
      (logPotential_differentiableOn z hz n)
      (logPotential_zero z n) hA0
      (fun w hw ↦ by
        simpa using logPotential_re_le_log_M z hz n hw)
      (Nat.zero_lt_of_lt hm)
  have hcoeff := iteratedDeriv_div_factorial_logPotential z n m
  have hfac0 : (0 : ℝ) < m.factorial := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnormcoeff :
      ‖iteratedDeriv m (logPotential z n) 0‖ / (m.factorial : ℝ) =
        ‖powerSum z n m‖ / (m : ℝ) := by
    have := congrArg norm hcoeff
    simpa [norm_div, Nat.cast_ofNat, hm0.ne', hfac0.ne',
      Real.norm_of_nonneg hfac0.le, Real.norm_of_nonneg hm0.le] using this
  rw [hnormcoeff] at hcar
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (div_le_iff₀ hm0).mp hcar

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
        <;> ring
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
  ring

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

set_option maxHeartbeats 800000 in
-- Comparing the two infinite series requires substantial typeclass normalization.
lemma pairEnergy_lower_bound_sharp (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
        2 * (Real.log (M z n) + 1) ^ 2 *
          (∑' m : ℕ, (m : ℝ) * r ^ m)
      ≤ pairEnergy z n r := by
  let A : ℝ := Real.log (M z n) + 1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have := Real.log_nonneg (one_le_M z hz n)
    linarith
  have hgeom : Summable (fun m : ℕ ↦ (m : ℝ) * r ^ m) := by
    simpa using
      (hasSum_coe_mul_geometric_of_norm_lt_one
        (by simpa [Real.norm_of_nonneg hr0] using hr1)).summable
  have hpos : Summable (fun m : ℕ ↦
      (n : ℝ) / 2 * (r ^ m / m)) :=
    (hasSum_pow_div r hr0 hr1).summable.mul_left _
  have herr : Summable (fun m : ℕ ↦
      2 * A ^ 2 * ((m : ℝ) * r ^ m)) :=
    hgeom.mul_left _
  have hrhs : Summable (fun m : ℕ ↦
      (n : ℝ) / 2 * (r ^ m / m) -
        2 * A ^ 2 * ((m : ℝ) * r ^ m)) :=
    hpos.sub herr
  have henergy := hasSum_pairEnergy z hz n hr0 hr1
  have hpoint (m : ℕ) :
      (n : ℝ) / 2 * (r ^ m / m) -
          2 * A ^ 2 * ((m : ℝ) * r ^ m)
        ≤ r ^ m / (2 * m) * ((n : ℝ) - ‖powerSum z n m‖ ^ 2) := by
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    have hm1 : 1 ≤ m := hm
    have hS := norm_powerSum_le_linear z hz n m hm1
    change ‖powerSum z n m‖ ≤ 2 * (m : ℝ) * A at hS
    have hB0 : 0 ≤ 2 * (m : ℝ) * A := by positivity
    have hSsq :
        ‖powerSum z n m‖ ^ 2 ≤ 4 * (m : ℝ) ^ 2 * A ^ 2 := by
      calc
        ‖powerSum z n m‖ ^ 2
            ≤ (2 * (m : ℝ) * A) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hB0).mpr hS
        _ = 4 * (m : ℝ) ^ 2 * A ^ 2 := by ring
    have hmul :
        r ^ m / (2 * (m : ℝ)) * ‖powerSum z n m‖ ^ 2 ≤
          r ^ m / (2 * (m : ℝ)) *
            (4 * (m : ℝ) ^ 2 * A ^ 2) :=
      mul_le_mul_of_nonneg_left hSsq (by positivity)
    calc
      (n : ℝ) / 2 * (r ^ m / m) -
            2 * A ^ 2 * ((m : ℝ) * r ^ m)
          = (n : ℝ) / 2 * (r ^ m / m) -
              r ^ m / (2 * (m : ℝ)) *
                (4 * (m : ℝ) ^ 2 * A ^ 2) := by
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
          2 * A ^ 2 * ((m : ℝ) * r ^ m))
        ≤ ∑' m : ℕ,
          r ^ m / (2 * m) * ((n : ℝ) - ‖powerSum z n m‖ ^ 2) :=
    Summable.tsum_le_tsum hpoint hrhs henergy.summable
  rw [henergy.tsum_eq] at htsum
  rw [hpos.tsum_sub herr, tsum_mul_left,
    (hasSum_pow_div r hr0 hr1).tsum_eq, tsum_mul_left] at htsum
  simpa [A] using htsum

lemma pairEnergy_lower_bound_sharp_explicit (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
        2 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 2
      ≤ pairEnergy z n r := by
  have hbase := pairEnergy_lower_bound_sharp z hz n hr0 hr1
  have hnorm : ‖r‖ < 1 := by
    simpa [Real.norm_of_nonneg hr0] using hr1
  have htsum :
      ∑' m : ℕ, (m : ℝ) * r ^ m = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  rw [htsum] at hbase
  have hden : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  have hgeom : r / (1 - r) ^ 2 ≤ 1 / (1 - r) ^ 2 :=
    (div_le_div_iff_of_pos_right hden).mpr hr1.le
  have hA : 0 ≤ 2 * (Real.log (M z n) + 1) ^ 2 := by positivity
  calc
    (n : ℝ) / 2 * (-Real.log (1 - r)) -
          2 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 2
        = (n : ℝ) / 2 * (-Real.log (1 - r)) -
          2 * (Real.log (M z n) + 1) ^ 2 *
            (1 / (1 - r) ^ 2) := by ring
    _ ≤ (n : ℝ) / 2 * (-Real.log (1 - r)) -
          2 * (Real.log (M z n) + 1) ^ 2 *
            (r / (1 - r) ^ 2) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hgeom hA) _
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
    convert h using 1 <;> norm_num <;> ring
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

lemma eventually_log_le_sqrt_nat :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).bound zero_lt_one
  have hsmall_nat :=
    (tendsto_natCast_atTop_atTop.eventually hsmall)
  filter_upwards [hsmall_nat, Filter.eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hpow0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hn' :
      Real.log (n : ℝ) ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0] using hn
  rw [abs_of_nonneg hpow0] at hn'
  simpa [Real.sqrt_eq_rpow] using hn'

lemma sum_log_M_lower_of_terminal_small_sharp (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) (hn : 0 < n)
    (hlog_one : 1 ≤ Real.log (n : ℝ))
    (hlog_sqrt : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ))
    (hterminal : Real.log (M z n) ≤ 2 * Real.log (n : ℝ)) :
    (n : ℝ) / 4 * Real.log (n : ℝ) -
        (n : ℝ) / 2 * Real.log (Real.log (n : ℝ)) -
        18 * (n : ℝ)
      ≤ ∑ k ∈ range n, Real.log (M z k) := by
  let x : ℝ := n
  let ell : ℝ := Real.log x
  let q : ℝ := Real.sqrt x / ell
  let r : ℝ := 1 - q⁻¹
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast hn
  have hx0 : 0 ≤ x := hxpos.le
  have hell1 : 1 ≤ ell := by simpa [ell, x] using hlog_one
  have hellpos : 0 < ell := zero_lt_one.trans_le hell1
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hqpos : 0 < q := div_pos hsqrtpos hellpos
  have hq1 : 1 ≤ q := by
    dsimp [q, ell, x]
    exact (le_div_iff₀ (by simpa [x] using hellpos)).mpr
      (by simpa [x] using hlog_sqrt)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact sub_nonneg.mpr ((inv_le_one₀ hqpos).mpr hq1)
  have hr1 : r < 1 := by
    dsimp [r]
    linarith [inv_pos.mpr hqpos]
  have hone_sub : 1 - r = q⁻¹ := by
    dsimp [r]
    ring
  have hlogq :
      -Real.log (1 - r) =
        Real.log x / 2 - Real.log ell := by
    rw [hone_sub, Real.log_inv, Real.log_div hsqrtpos.ne' hellpos.ne',
      Real.log_sqrt hx0]
    dsimp [q, ell]
    ring
  have hq_sq : q ^ 2 = x / ell ^ 2 := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt hx0]
  have herror_kernel :
      2 * (Real.log (M z n) + 1) ^ 2 / (1 - r) ^ 2 =
        2 * (Real.log (M z n) + 1) ^ 2 * q ^ 2 := by
    rw [hone_sub, inv_pow]
    field_simp [hqpos.ne']
  have henergy :=
    pairEnergy_lower_bound_sharp_explicit z hz n hr0 hr1
  rw [hlogq, herror_kernel] at henergy
  have hA0 : 0 ≤ Real.log (M z n) + 1 := by
    have := Real.log_nonneg (one_le_M z hz n)
    linarith
  have hA :
      Real.log (M z n) + 1 ≤ 3 * ell := by
    dsimp [ell, x] at hlog_one ⊢
    linarith
  have hAsq :
      (Real.log (M z n) + 1) ^ 2 ≤ (3 * ell) ^ 2 :=
    (sq_le_sq₀ hA0 (by positivity)).mpr hA
  have herror :
      2 * (Real.log (M z n) + 1) ^ 2 * q ^ 2 ≤ 18 * x := by
    calc
      2 * (Real.log (M z n) + 1) ^ 2 * q ^ 2
          ≤ 2 * (3 * ell) ^ 2 * q ^ 2 := by gcongr
      _ = 18 * x := by
        rw [hq_sq]
        field_simp [hellpos.ne']
        ring
  have hlower :
      x / 4 * Real.log x - x / 2 * Real.log ell - 18 * x
        ≤ pairEnergy z n r := by
    calc
      x / 4 * Real.log x - x / 2 * Real.log ell - 18 * x
          ≤ (n : ℝ) / 2 *
              (Real.log x / 2 - Real.log ell) -
              2 * (Real.log (M z n) + 1) ^ 2 * q ^ 2 := by
            dsimp [x]
            linarith
      _ ≤ pairEnergy z n r := henergy
  have hpair := pairEnergy_le_sum_log_M z hz n hr0 hr1
  simpa [x, ell] using hlower.trans hpair

lemma exp_quarter_log_bound_identity {x : ℝ} (hx : 0 < x)
    (hlog : 0 < Real.log x) :
    x * Real.exp
        (Real.log x / 4 - Real.log (Real.log x) / 2 - 18) =
      Real.exp (-18) * x ^ (5 / 4 : ℝ) /
        Real.sqrt (Real.log x) := by
  have hquarter :
      Real.exp (Real.log x / 4) = x ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hsqrt :
      Real.exp (Real.log (Real.log x) / 2) =
        Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlog]
    congr 1
    ring
  have hsqrtpos : 0 < Real.sqrt (Real.log x) :=
    Real.sqrt_pos.mpr hlog
  rw [show Real.log x / 4 - Real.log (Real.log x) / 2 - 18 =
      -18 + Real.log x / 4 - Real.log (Real.log x) / 2 by ring,
    Real.exp_sub, Real.exp_add, hquarter, hsqrt]
  field_simp [hsqrtpos.ne']
  calc
    x * x ^ (1 / 4 : ℝ) =
        x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + 1 / 4) :=
      (Real.rpow_add hx (1 : ℝ) (1 / 4 : ℝ)).symm
    _ = x ^ (5 / 4 : ℝ) := by norm_num

lemma eventually_sum_M_succ_quantitative (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-19) * (n : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log (n : ℝ)) <
        ∑ k ∈ range (n + 1), M z k := by
  have hlog :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 1
  filter_upwards [hlog, eventually_log_le_sqrt_nat,
    Filter.eventually_gt_atTop 0] with n hnlog hnlogsqrt hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hnlog
  have hsqrtlogpos : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_pos.mpr hlogpos
  by_cases hterminal :
      Real.log (M z n) ≤ 2 * Real.log (n : ℝ)
  · have hsumlog :=
      sum_log_M_lower_of_terminal_small_sharp
        z hz n hnpos hnlog hnlogsqrt hterminal
    have havg :
        Real.log (n : ℝ) / 4 -
            Real.log (Real.log (n : ℝ)) / 2 - 18
          ≤ (∑ k ∈ range n, Real.log (M z k)) / n := by
      rw [le_div_iff₀ hnR]
      calc
        (Real.log (n : ℝ) / 4 -
              Real.log (Real.log (n : ℝ)) / 2 - 18) * (n : ℝ)
            = (n : ℝ) / 4 * Real.log (n : ℝ) -
                (n : ℝ) / 2 * Real.log (Real.log (n : ℝ)) -
                18 * (n : ℝ) := by ring
        _ ≤ ∑ k ∈ range n, Real.log (M z k) := hsumlog
    have hexp :
        Real.exp
            (Real.log (n : ℝ) / 4 -
              Real.log (Real.log (n : ℝ)) / 2 - 18)
          ≤ Real.exp
              ((∑ k ∈ range n, Real.log (M z k)) / n) :=
      Real.exp_le_exp.mpr havg
    have hjensen := card_mul_exp_average_log_le_sum_M z hz n hnpos
    have hmain :
        Real.exp (-18) * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))
          ≤ ∑ k ∈ range n, M z k := by
      rw [← exp_quarter_log_bound_identity hnR hlogpos]
      exact (mul_le_mul_of_nonneg_left hexp hnR.le).trans hjensen
    have hconst :
        Real.exp (-19) * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))
          < Real.exp (-18) * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ)) := by
      apply div_lt_div_of_pos_right _ hsqrtlogpos
      apply mul_lt_mul_of_pos_right
      · exact Real.exp_lt_exp.mpr (by norm_num)
      · exact Real.rpow_pos_of_pos hnR _
    rw [sum_range_succ]
    exact hconst.trans_le (hmain.trans
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
    have htarget_le :
        Real.exp (-19) * (n : ℝ) ^ (5 / 4 : ℝ) /
            Real.sqrt (Real.log (n : ℝ))
          ≤ (n : ℝ) ^ (2 : ℝ) := by
      have hexp_le : Real.exp (-19) ≤ 1 :=
        (Real.exp_le_one_iff.mpr (by norm_num))
      have hsqrt1 : 1 ≤ Real.sqrt (Real.log (n : ℝ)) :=
        (Real.le_sqrt (by norm_num) hlogpos.le).mpr (by nlinarith)
      have hpow :
          (n : ℝ) ^ (5 / 4 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.succ_le_iff.mpr hnpos)) (by norm_num)
      calc
        Real.exp (-19) * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))
            ≤ 1 * (n : ℝ) ^ (5 / 4 : ℝ) / 1 := by gcongr
        _ ≤ (n : ℝ) ^ (2 : ℝ) := by simpa using hpow
    rw [sum_range_succ]
    have hsum0 : 0 ≤ ∑ k ∈ range n, M z k :=
      Finset.sum_nonneg fun k hk => (one_le_M z hz k).trans' zero_le_one
    exact htarget_le.trans_lt
      (hMlarge.trans_le (le_add_of_nonneg_left hsum0))

lemma eventually_quantitative_succ_compare :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp (-19) / 5) *
            (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)))
        < Real.exp (-19) *
            ((n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))) := by
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hnR : (0 : ℝ) < n := by positivity
  have hn1R : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hsuccR : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hsucc_le : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    nlinarith
  have hpow2 :
      (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (5 / 4 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hpowsucc :
      (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))
        ≤ 4 * (n : ℝ) ^ (5 / 4 : ℝ) := by
    calc
      (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))
          ≤ (2 * (n : ℝ)) ^ (5 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hsucc_le (by norm_num)
      _ = (2 : ℝ) ^ (5 / 4 : ℝ) *
            (n : ℝ) ^ (5 / 4 : ℝ) :=
        Real.mul_rpow (by norm_num) hnR.le
      _ ≤ 4 * (n : ℝ) ^ (5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg hnR.le _)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1R
  have hlogmono :
      Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log hnR
    exact_mod_cast Nat.le_succ n
  have hsqrtmono :
      Real.sqrt (Real.log (n : ℝ)) ≤
        Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hlogmono
  have hsqrtn : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_pos.mpr hlogn
  have hfrac :
      (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)))
        ≤ 4 * (n : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log (n : ℝ)) := by
    calc
      (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
            Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)))
          ≤ (4 * (n : ℝ) ^ (5 / 4 : ℝ)) /
              Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_right hpowsucc (Real.sqrt_nonneg _)
      _ ≤ 4 * (n : ℝ) ^ (5 / 4 : ℝ) /
            Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hsqrtn hsqrtmono
  have htpos :
      0 < (n : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log (n : ℝ)) := by positivity
  calc
    (Real.exp (-19) / 5) *
          (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
            Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)))
        ≤ (Real.exp (-19) / 5) *
            (4 * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ < Real.exp (-19) *
          ((n : ℝ) ^ (5 / 4 : ℝ) /
            Real.sqrt (Real.log (n : ℝ))) := by
      have hexp := Real.exp_pos (-19)
      rw [show
        4 * (n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ)) =
            4 * ((n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))) by ring]
      have hprod :
          0 < Real.exp (-19) *
            ((n : ℝ) ^ (5 / 4 : ℝ) /
              Real.sqrt (Real.log (n : ℝ))) :=
        mul_pos hexp htpos
      calc
        Real.exp (-19) / 5 *
              (4 * ((n : ℝ) ^ (5 / 4 : ℝ) /
                Real.sqrt (Real.log (n : ℝ))))
            = (4 / 5 : ℝ) *
                (Real.exp (-19) *
                  ((n : ℝ) ^ (5 / 4 : ℝ) /
                    Real.sqrt (Real.log (n : ℝ)))) := by ring
        _ < Real.exp (-19) *
              ((n : ℝ) ^ (5 / 4 : ℝ) /
                Real.sqrt (Real.log (n : ℝ))) := by nlinarith

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
      convert havg using 1 <;> ring
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

/-- The quantitative form proved in the writeup:
for some absolute positive constant, the partial sums are eventually bounded below by
$n^{5/4}/\sqrt{\log n}$. -/
theorem erdos_119.parts.iii_quantitative :
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        C * ((n : ℝ) ^ (5 / 4 : ℝ) /
          Real.sqrt (Real.log (n : ℝ))) <
            ∑ k ∈ range n, M z k := by
  intro z hz
  refine ⟨Real.exp (-19) / 5, by positivity, ?_⟩
  have hs := eventually_sum_M_succ_quantitative z hz
  have hcompare := eventually_quantitative_succ_compare
  have hsucc :
      ∀ᶠ n : ℕ in atTop,
        (Real.exp (-19) / 5) *
              (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
                Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ))) <
          ∑ k ∈ range (n + 1), M z k := by
    filter_upwards [hs, hcompare] with n hn hnc
    exact hnc.trans (by simpa [div_eq_mul_inv, mul_assoc] using hn)
  have hshift :
      ∀ᶠ n : ℕ in atTop,
        (Real.exp (-19) / 5) *
              (((n - 1 + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ) /
                Real.sqrt (Real.log ((n - 1 + 1 : ℕ) : ℝ))) <
          ∑ k ∈ range (n - 1 + 1), M z k :=
    (tendsto_sub_atTop_nat 1).eventually hsucc
  filter_upwards [hshift, Filter.eventually_gt_atTop 0] with n hn hnpos
  simpa [Nat.sub_add_cancel hnpos] using hn

/-- Question 3:

Is it true that there exists $c > 0$ such that, for all large $n$,
$\sum_{k \leq n} M_k > n^{1 + c}$?

The proof below gives the affirmative answer with $c=1/256$.
-/
theorem erdos_119.parts.iii :
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
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
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
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
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
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
