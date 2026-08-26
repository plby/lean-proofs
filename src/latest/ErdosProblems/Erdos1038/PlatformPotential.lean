import ErdosProblems.Erdos1038.PlatformPoisson

/-!
# Logarithmic potentials of the constant-platform reference

This file develops the exact interval-potential identities used in equation
`(4.6)` of the manuscript.  We first evaluate the equilibrium (arcsine)
potential directly from the classical logarithmic sine integral.
-/

open Set MeasureTheory

namespace Erdos1038

noncomputable section

private def logAbsSin (x : ℝ) : ℝ := Real.log |Real.sin x|

private lemma logAbsSin_eq (x : ℝ) :
    logAbsSin x = Real.log (Real.sin x) := by
  simp only [logAbsSin, Real.log_abs]

private lemma logAbsSin_periodic : Function.Periodic logAbsSin Real.pi := by
  intro x
  simp only [logAbsSin, Real.sin_add_pi, abs_neg]

private lemma integral_logAbsSin_zero_pi :
    (∫ x : ℝ in 0..Real.pi, logAbsSin x) =
      -Real.log 2 * Real.pi := by
  simpa only [logAbsSin_eq] using! integral_log_sin_zero_pi

private lemma integral_logAbsSin_shifted_period (s : ℝ) :
    (∫ x : ℝ in s..s + Real.pi, logAbsSin x) =
      -Real.log 2 * Real.pi := by
  rw [logAbsSin_periodic.intervalIntegral_add_eq s 0]
  simpa only [zero_add] using! integral_logAbsSin_zero_pi

private lemma integral_logAbsSin_half_add (theta : ℝ) :
    (∫ phi : ℝ in 0..2 * Real.pi,
        logAbsSin ((phi + theta) / 2)) =
      -2 * Real.log 2 * Real.pi := by
  calc
    (∫ phi : ℝ in 0..2 * Real.pi,
        logAbsSin ((phi + theta) / 2)) =
        2 * ∫ u : ℝ in 0..Real.pi, logAbsSin (u + theta / 2) := by
          rw [show (fun phi : ℝ ↦ logAbsSin ((phi + theta) / 2)) =
              fun phi : ℝ ↦ (fun u ↦ logAbsSin (u + theta / 2)) (phi / 2) by
            funext phi
            congr 1
            ring]
          rw [intervalIntegral.integral_comp_div (f :=
            fun u : ℝ ↦ logAbsSin (u + theta / 2)) (by norm_num : (2 : ℝ) ≠ 0)]
          simp only [smul_eq_mul]
          congr 1
          ring_nf
    _ = 2 * ∫ u : ℝ in theta / 2..theta / 2 + Real.pi, logAbsSin u := by
          rw [intervalIntegral.integral_comp_add_right]
          congr 2 <;> ring
    _ = -2 * Real.log 2 * Real.pi := by
          rw [integral_logAbsSin_shifted_period]
          ring

private lemma integral_logAbsSin_half_sub (theta : ℝ) :
    (∫ phi : ℝ in 0..2 * Real.pi,
        logAbsSin ((phi - theta) / 2)) =
      -2 * Real.log 2 * Real.pi := by
  calc
    (∫ phi : ℝ in 0..2 * Real.pi,
        logAbsSin ((phi - theta) / 2)) =
        2 * ∫ u : ℝ in 0..Real.pi, logAbsSin (u - theta / 2) := by
          rw [show (fun phi : ℝ ↦ logAbsSin ((phi - theta) / 2)) =
              fun phi : ℝ ↦ (fun u ↦ logAbsSin (u - theta / 2)) (phi / 2) by
            funext phi
            congr 1
            ring]
          rw [intervalIntegral.integral_comp_div (f :=
            fun u : ℝ ↦ logAbsSin (u - theta / 2)) (by norm_num : (2 : ℝ) ≠ 0)]
          simp only [smul_eq_mul]
          congr 1
          ring_nf
    _ = 2 * ∫ u : ℝ in -theta / 2..-theta / 2 + Real.pi, logAbsSin u := by
          rw [intervalIntegral.integral_comp_sub_right]
          congr 2 <;> ring
    _ = -2 * Real.log 2 * Real.pi := by
          rw [integral_logAbsSin_shifted_period]
          ring

private lemma intervalIntegrable_log_abs_cos_sub (theta : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun phi : ℝ ↦ Real.log |Real.cos phi - Real.cos theta|)
      volume a b := by
  have han : AnalyticOnNhd ℝ
      (fun phi : ℝ ↦ Real.cos phi - Real.cos theta) Set.univ :=
    fun _ _ ↦ by fun_prop
  have hmer : MeromorphicOn (fun phi : ℝ ↦ Real.cos phi - Real.cos theta)
      (Set.uIcc a b) := fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using! MeromorphicOn.intervalIntegrable_log_norm hmer

private lemma integral_log_abs_cos_sub_full (theta : ℝ) :
    (∫ phi : ℝ in 0..2 * Real.pi,
        Real.log |Real.cos phi - Real.cos theta|) =
      -2 * Real.log 2 * Real.pi := by
  have hplus :
      IntervalIntegrable (fun phi : ℝ ↦ logAbsSin ((phi + theta) / 2))
        volume 0 (2 * Real.pi) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.sin ((phi + theta) / 2)) Set.univ :=
      fun _ _ ↦ by fun_prop (disch := norm_num)
    have hmer : MeromorphicOn
        (fun phi : ℝ ↦ Real.sin ((phi + theta) / 2))
        (Set.uIcc 0 (2 * Real.pi)) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [logAbsSin, Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hminus :
      IntervalIntegrable (fun phi : ℝ ↦ logAbsSin ((phi - theta) / 2))
        volume 0 (2 * Real.pi) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.sin ((phi - theta) / 2)) Set.univ :=
      fun _ _ ↦ by fun_prop (disch := norm_num)
    have hmer : MeromorphicOn
        (fun phi : ℝ ↦ Real.sin ((phi - theta) / 2))
        (Set.uIcc 0 (2 * Real.pi)) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [logAbsSin, Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hsinPlus :
      {phi : ℝ | Real.sin ((phi + theta) / 2) ≠ 0} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) (2 * Real.pi)) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.sin ((phi + theta) / 2)) Set.univ :=
      fun _ _ ↦ by fun_prop (disch := norm_num)
    apply Filter.codiscreteWithin_mono (Set.subset_univ _)
    apply han.preimage_zero_mem_codiscrete (x := Real.pi - theta)
    simp
  have hsinMinus :
      {phi : ℝ | Real.sin ((phi - theta) / 2) ≠ 0} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) (2 * Real.pi)) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.sin ((phi - theta) / 2)) Set.univ :=
      fun _ _ ↦ by fun_prop (disch := norm_num)
    apply Filter.codiscreteWithin_mono (Set.subset_univ _)
    apply han.preimage_zero_mem_codiscrete (x := Real.pi + theta)
    simp
  calc
    (∫ phi : ℝ in 0..2 * Real.pi,
        Real.log |Real.cos phi - Real.cos theta|) =
        ∫ phi : ℝ in 0..2 * Real.pi,
          (Real.log 2 + logAbsSin ((phi + theta) / 2)) +
            logAbsSin ((phi - theta) / 2) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [hsinPlus, hsinMinus] with phi hp hm
      rw [Real.cos_sub_cos, abs_mul, abs_mul,
        Real.log_mul
          (mul_ne_zero (abs_ne_zero.mpr (by norm_num : (-2 : ℝ) ≠ 0))
            (abs_ne_zero.mpr hp))
          (abs_ne_zero.mpr hm),
        Real.log_mul (abs_ne_zero.mpr (by norm_num : (-2 : ℝ) ≠ 0))
          (abs_ne_zero.mpr hp)]
      simp only [abs_neg, logAbsSin]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (∫ _phi : ℝ in 0..2 * Real.pi, Real.log 2) +
          (∫ phi : ℝ in 0..2 * Real.pi, logAbsSin ((phi + theta) / 2)) +
          (∫ phi : ℝ in 0..2 * Real.pi, logAbsSin ((phi - theta) / 2)) := by
      rw [intervalIntegral.integral_add
        ((intervalIntegrable_const : IntervalIntegrable
          (fun _phi : ℝ ↦ Real.log 2) volume 0 (2 * Real.pi)).add hplus) hminus,
        intervalIntegral.integral_add intervalIntegrable_const hplus]
    _ = -2 * Real.log 2 * Real.pi := by
      rw [intervalIntegral.integral_const, integral_logAbsSin_half_add,
        integral_logAbsSin_half_sub]
      simp only [sub_zero, smul_eq_mul]
      ring

/-- The arcsine logarithmic potential on `[-1,1]`, in cosine coordinates. -/
theorem integral_log_abs_cos_sub_zero_pi {theta : ℝ}
    (_htheta : theta ∈ Icc 0 Real.pi) :
    (∫ phi : ℝ in 0..Real.pi,
        Real.log |Real.cos phi - Real.cos theta|) =
      -Real.log 2 * Real.pi := by
  let F : ℝ → ℝ := fun phi ↦ Real.log |Real.cos phi - Real.cos theta|
  have hF : IntervalIntegrable F volume 0 (2 * Real.pi) := by
    simpa only [F] using! intervalIntegrable_log_abs_cos_sub theta 0 (2 * Real.pi)
  have hFleft : IntervalIntegrable F volume 0 Real.pi :=
    hF.mono_set (by
      rw [uIcc_of_le Real.pi_pos.le,
        uIcc_of_le (mul_pos (by norm_num) Real.pi_pos).le]
      exact Icc_subset_Icc_right (by linarith [Real.pi_pos]))
  have hFright : IntervalIntegrable F volume Real.pi (2 * Real.pi) :=
    hF.mono_set (by
      rw [uIcc_of_le (by linarith [Real.pi_pos]),
        uIcc_of_le (mul_pos (by norm_num) Real.pi_pos).le]
      exact Icc_subset_Icc_left Real.pi_pos.le)
  have hsym : (∫ phi : ℝ in Real.pi..2 * Real.pi, F phi) =
      ∫ phi : ℝ in 0..Real.pi, F phi := by
    calc
      (∫ phi : ℝ in Real.pi..2 * Real.pi, F phi) =
          ∫ phi : ℝ in 0..Real.pi, F (2 * Real.pi - phi) := by
            rw [intervalIntegral.integral_comp_sub_left]
            congr 1 <;> ring
      _ = ∫ phi : ℝ in 0..Real.pi, F phi := by
            apply intervalIntegral.integral_congr
            intro phi _hphi
            simp only [F, Real.cos_two_pi_sub]
  have hsplit :
      (∫ phi : ℝ in 0..2 * Real.pi, F phi) =
        (∫ phi : ℝ in 0..Real.pi, F phi) +
          ∫ phi : ℝ in Real.pi..2 * Real.pi, F phi := by
    exact (intervalIntegral.integral_add_adjacent_intervals hFleft hFright).symm
  have hfull : (∫ phi : ℝ in 0..2 * Real.pi, F phi) =
      -2 * Real.log 2 * Real.pi := by
    simpa only [F] using! integral_log_abs_cos_sub_full theta
  rw [hsplit, hsym] at hfull
  linarith

/-! ## Generic affine-cosine interval formulae -/

/-- The standard angular parametrization of a real interval `[A,B]`. -/
def intervalAngularDistance (A B theta : ℝ) : ℝ :=
  (A + B) / 2 - (B - A) / 2 * Real.cos theta

/-- The logarithmic capacity of `[A,B]`. -/
def intervalLogCapacity (A B : ℝ) : ℝ := (B - A) / 4

/-- The exponential of the exterior equilibrium potential at zero for a
positive interval `[A,B]`. -/
def intervalExteriorD0 (A B : ℝ) : ℝ :=
  (A + B + 2 * Real.sqrt (A * B)) / 4

@[simp] lemma intervalAngularDistance_zero (A B : ℝ) :
    intervalAngularDistance A B 0 = A := by
  simp [intervalAngularDistance]
  ring

@[simp] lemma intervalAngularDistance_pi (A B : ℝ) :
    intervalAngularDistance A B Real.pi = B := by
  simp [intervalAngularDistance]
  ring

/-- The equilibrium probability of an arbitrary nondegenerate interval has
constant logarithmic potential equal to the logarithm of its capacity. -/
theorem integral_intervalEquilibrium_log_potential
    {A B theta : ℝ} (hAB : A < B) (htheta : theta ∈ Icc 0 Real.pi) :
    (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs
            (intervalAngularDistance A B theta -
              intervalAngularDistance A B phi))) =
      Real.log (intervalLogCapacity A B) := by
  have hr : 0 < (B - A) / 2 := by linarith
  have hcos := intervalIntegrable_log_abs_cos_sub theta 0 Real.pi
  have hzero :
      {phi : ℝ | Real.cos phi - Real.cos theta ≠ 0} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) Real.pi) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.cos phi - Real.cos theta) Set.univ :=
      fun _ _ ↦ by fun_prop
    by_cases hc : Real.cos theta = 1
    · apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      apply han.preimage_zero_mem_codiscrete (x := Real.pi)
      norm_num [hc]
    · apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      apply han.preimage_zero_mem_codiscrete (x := 0)
      exact sub_ne_zero.mpr (fun h ↦ hc (by simpa using! h.symm))
  have hrewrite :
      (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs
            (intervalAngularDistance A B theta -
              intervalAngularDistance A B phi))) =
        ∫ phi : ℝ in 0..Real.pi,
          Real.log ((B - A) / 2) +
            Real.log |Real.cos phi - Real.cos theta| := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    filter_upwards [hzero] with phi hphi
    have hfactor :
        intervalAngularDistance A B theta -
            intervalAngularDistance A B phi =
          ((B - A) / 2) * (Real.cos phi - Real.cos theta) := by
      unfold intervalAngularDistance
      ring
    rw [hfactor, abs_mul,
      Real.log_mul (abs_ne_zero.mpr hr.ne') (abs_ne_zero.mpr hphi),
      abs_of_pos hr]
  rw [hrewrite, intervalIntegral.integral_add intervalIntegrable_const hcos,
    intervalIntegral.integral_const, integral_log_abs_cos_sub_zero_pi htheta]
  simp only [sub_zero, smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcap : intervalLogCapacity A B = ((B - A) / 2) / 2 := by
    simp only [intervalLogCapacity]
    ring
  rw [hcap, Real.log_div hr.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [hpi]
  ring

private lemma intervalExteriorRho_mem_Ioo {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    (B - A) / (A + B + 2 * Real.sqrt (A * B)) ∈ Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt (A * B) := Real.sqrt_pos.2 (mul_pos hA (hA.trans hAB))
  have hB : 0 < B := hA.trans hAB
  have hden : 0 < A + B + 2 * Real.sqrt (A * B) := by linarith
  constructor
  · exact div_pos (sub_pos.mpr hAB) hden
  · rw [div_lt_one hden]
    linarith

private lemma intervalAngularDistance_factor_exterior
    {A B theta : ℝ} (hA : 0 < A) (hAB : A < B) :
    intervalAngularDistance A B theta =
      intervalExteriorD0 A B *
        (1 - 2 *
            ((B - A) / (A + B + 2 * Real.sqrt (A * B))) *
              Real.cos theta +
          ((B - A) / (A + B + 2 * Real.sqrt (A * B))) ^ 2) := by
  have hsSq : (Real.sqrt (A * B)) ^ 2 = A * B :=
    Real.sq_sqrt (mul_nonneg hA.le (hA.trans hAB).le)
  have hs : 0 < Real.sqrt (A * B) := Real.sqrt_pos.2 (mul_pos hA (hA.trans hAB))
  have hB : 0 < B := hA.trans hAB
  have hden : A + B + 2 * Real.sqrt (A * B) ≠ 0 := by
    linarith
  unfold intervalAngularDistance intervalExteriorD0
  field_simp [hden]
  nlinarith

private lemma circleMap_sub_real_norm_sq (q phi : ℝ) :
    ‖circleMap 0 1 phi - (q : ℂ)‖ ^ 2 =
      1 - 2 * q * Real.cos phi + q ^ 2 := by
  rw [Complex.sq_norm]
  have hre : (circleMap 0 1 phi).re = Real.cos phi := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re]
  have him : (circleMap 0 1 phi).im = Real.sin phi := by
    simp [circleMap, Complex.exp_ofReal_mul_I_im]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    hre, him, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq phi]

private lemma integral_log_exteriorDenominator_zero {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∫ phi : ℝ in 0..Real.pi,
      Real.log (1 - 2 * q * Real.cos phi + q ^ 2)) = 0 := by
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using! hq1
  have hcircle := circleAverage_log_norm_sub_const₀ (a := (q : ℂ)) hqnorm
  rw [Real.circleAverage] at hcircle
  simp only [smul_eq_mul] at hcircle
  have hfullNorm :
      (∫ phi : ℝ in 0..2 * Real.pi,
        Real.log ‖circleMap 0 1 phi - (q : ℂ)‖) = 0 := by
    apply (mul_eq_zero.mp hcircle).resolve_left
    exact inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hfull :
      (∫ phi : ℝ in 0..2 * Real.pi,
        Real.log (1 - 2 * q * Real.cos phi + q ^ 2)) = 0 := by
    calc
      (∫ phi : ℝ in 0..2 * Real.pi,
          Real.log (1 - 2 * q * Real.cos phi + q ^ 2)) =
          ∫ phi : ℝ in 0..2 * Real.pi,
            2 * Real.log ‖circleMap 0 1 phi - (q : ℂ)‖ := by
        apply intervalIntegral.integral_congr
        intro phi _hphi
        change Real.log (1 - 2 * q * Real.cos phi + q ^ 2) =
          2 * Real.log ‖circleMap 0 1 phi - (q : ℂ)‖
        rw [← circleMap_sub_real_norm_sq q phi, Real.log_pow]
        norm_num
      _ = 0 := by
        rw [intervalIntegral.integral_const_mul, hfullNorm]
        ring
  let F : ℝ → ℝ := fun phi ↦
    Real.log (1 - 2 * q * Real.cos phi + q ^ 2)
  have hden : ∀ phi : ℝ, 0 < 1 - 2 * q * Real.cos phi + q ^ 2 :=
    fun phi ↦ platformPoissonKernel_den_pos hq0 hq1
  have hF : IntervalIntegrable F volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    unfold F
    have hbase : Continuous
        (fun phi : ℝ ↦ 1 - 2 * q * Real.cos phi + q ^ 2) := by
      fun_prop
    exact hbase.log (fun phi ↦ (hden phi).ne')
  have hFleft : IntervalIntegrable F volume 0 Real.pi :=
    hF.mono_set (by
      rw [uIcc_of_le Real.pi_pos.le,
        uIcc_of_le (mul_pos (by norm_num) Real.pi_pos).le]
      exact Icc_subset_Icc_right (by linarith [Real.pi_pos]))
  have hFright : IntervalIntegrable F volume Real.pi (2 * Real.pi) :=
    hF.mono_set (by
      rw [uIcc_of_le (by linarith [Real.pi_pos]),
        uIcc_of_le (mul_pos (by norm_num) Real.pi_pos).le]
      exact Icc_subset_Icc_left Real.pi_pos.le)
  have hsym : (∫ phi : ℝ in Real.pi..2 * Real.pi, F phi) =
      ∫ phi : ℝ in 0..Real.pi, F phi := by
    calc
      (∫ phi : ℝ in Real.pi..2 * Real.pi, F phi) =
          ∫ phi : ℝ in 0..Real.pi, F (2 * Real.pi - phi) := by
            rw [intervalIntegral.integral_comp_sub_left]
            congr 1 <;> ring
      _ = ∫ phi : ℝ in 0..Real.pi, F phi := by
            apply intervalIntegral.integral_congr
            intro phi _hphi
            simp only [F, Real.cos_two_pi_sub]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hFleft hFright
  have hfullF : (∫ phi : ℝ in 0..2 * Real.pi, F phi) = 0 := by
    simpa only [F] using! hfull
  have hhalf : (∫ phi : ℝ in 0..Real.pi, F phi) = 0 := by
    linarith [hsplit, hfullF, hsym]
  simpa only [F] using! hhalf

/-- Exterior equilibrium potential at zero for a positive interval. -/
theorem integral_intervalEquilibrium_log_exterior
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          Real.log (intervalAngularDistance A B phi)) =
      Real.log (intervalExteriorD0 A B) := by
  let q : ℝ :=
    (B - A) / (A + B + 2 * Real.sqrt (A * B))
  have hq := intervalExteriorRho_mem_Ioo hA hAB
  change q ∈ Ioo (0 : ℝ) 1 at hq
  have hD : 0 < intervalExteriorD0 A B := by
    unfold intervalExteriorD0
    have hs : 0 < Real.sqrt (A * B) :=
      Real.sqrt_pos.2 (mul_pos hA (hA.trans hAB))
    have hnum : 0 < A + B + 2 * Real.sqrt (A * B) := by
      linarith [hA.trans hAB]
    positivity
  have hden : ∀ phi : ℝ,
      0 < 1 - 2 * q * Real.cos phi + q ^ 2 :=
    fun phi ↦ platformPoissonKernel_den_pos hq.1.le hq.2
  have hdenInt : IntervalIntegrable
      (fun phi : ℝ ↦ Real.log (1 - 2 * q * Real.cos phi + q ^ 2))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    have hbase : Continuous
        (fun phi : ℝ ↦ 1 - 2 * q * Real.cos phi + q ^ 2) := by
      fun_prop
    exact hbase.log (fun phi ↦ (hden phi).ne')
  have hrewrite :
      (∫ phi : ℝ in 0..Real.pi,
          Real.log (intervalAngularDistance A B phi)) =
        ∫ phi : ℝ in 0..Real.pi,
          Real.log (intervalExteriorD0 A B) +
            Real.log (1 - 2 * q * Real.cos phi + q ^ 2) := by
    apply intervalIntegral.integral_congr
    intro phi _hphi
    change Real.log (intervalAngularDistance A B phi) =
      Real.log (intervalExteriorD0 A B) +
        Real.log (1 - 2 * q * Real.cos phi + q ^ 2)
    rw [intervalAngularDistance_factor_exterior hA hAB]
    change Real.log
        (intervalExteriorD0 A B *
          (1 - 2 * q * Real.cos phi + q ^ 2)) = _
    rw [Real.log_mul hD.ne' (hden phi).ne']
  rw [hrewrite,
    intervalIntegral.integral_add intervalIntegrable_const hdenInt,
    intervalIntegral.integral_const,
    integral_log_exteriorDenominator_zero hq.1.le hq.2]
  simp only [sub_zero, smul_eq_mul, add_zero]
  field_simp [Real.pi_ne_zero]

/-! ## Change of variables for interval equilibrium measure -/

lemma intervalAngularDistance_sub_mul (A B theta : ℝ) :
    (intervalAngularDistance A B theta - A) *
        (B - intervalAngularDistance A B theta) =
      (((B - A) / 2) * Real.sin theta) ^ 2 := by
  unfold intervalAngularDistance
  have htrig := Real.sin_sq_add_cos_sq theta
  have hsinSq : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by
    nlinarith
  rw [mul_pow, hsinSq]
  ring

lemma sqrt_intervalAngularDistance_sub_mul {A B theta : ℝ}
    (hAB : A ≤ B) (htheta : theta ∈ Icc 0 Real.pi) :
    Real.sqrt
        ((intervalAngularDistance A B theta - A) *
          (B - intervalAngularDistance A B theta)) =
      ((B - A) / 2) * Real.sin theta := by
  rw [intervalAngularDistance_sub_mul, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg]
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hAB) (by norm_num))
    (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2)

lemma hasDerivAt_intervalAngularDistance (A B theta : ℝ) :
    HasDerivAt (intervalAngularDistance A B)
      (((B - A) / 2) * Real.sin theta) theta := by
  unfold intervalAngularDistance
  convert! (hasDerivAt_const theta ((A + B) / 2)).sub
    ((Real.hasDerivAt_cos theta).const_mul ((B - A) / 2)) using 1
  all_goals ring

theorem intervalAngularDistance_strictMonoOn {A B : ℝ} (hAB : A < B) :
    StrictMonoOn (intervalAngularDistance A B) (Icc 0 Real.pi) := by
  intro theta htheta phi hphi hthetaPhi
  have hcos : Real.cos phi < Real.cos theta :=
    Real.strictAntiOn_cos htheta hphi hthetaPhi
  unfold intervalAngularDistance
  nlinarith [mul_pos (sub_pos.mpr hAB) (sub_pos.mpr hcos)]

theorem intervalAngularDistance_image_Icc {A B : ℝ} (hAB : A < B) :
    intervalAngularDistance A B '' Icc 0 Real.pi = Icc A B := by
  have hcont : ContinuousOn (intervalAngularDistance A B) (Icc 0 Real.pi) := by
    unfold intervalAngularDistance
    fun_prop
  have hmono := (intervalAngularDistance_strictMonoOn hAB).monotoneOn
  calc
    intervalAngularDistance A B '' Icc 0 Real.pi =
        Icc (sInf (intervalAngularDistance A B '' Icc 0 Real.pi))
          (sSup (intervalAngularDistance A B '' Icc 0 Real.pi)) :=
      hcont.image_Icc Real.pi_pos.le
    _ = Icc (intervalAngularDistance A B 0)
        (intervalAngularDistance A B Real.pi) := by
      rw [hmono.sInf_image_Icc Real.pi_pos.le,
        hmono.sSup_image_Icc Real.pi_pos.le]
    _ = Icc A B := by simp

/-- Angular equilibrium integration is exactly the distance-coordinate
arcsine integral.  The statement is valid for arbitrary real-valued `g`,
including logarithmic kernels; both sides use the usual Bochner convention
when an integrand is not integrable. -/
theorem integral_intervalAngular_comp_eq_arcsine
    {A B : ℝ} (hAB : A < B) (g : ℝ → ℝ) :
    (∫ theta : ℝ in 0..Real.pi,
        g (intervalAngularDistance A B theta)) =
      ∫ y : ℝ in A..B,
        g y / Real.sqrt ((y - A) * (B - y)) := by
  let m : ℝ → ℝ := intervalAngularDistance A B
  let radius : ℝ := (B - A) / 2
  let G : ℝ → ℝ := fun y ↦
    g y / Real.sqrt ((y - A) * (B - y))
  have hmono : MonotoneOn m (Icc 0 Real.pi) :=
    (intervalAngularDistance_strictMonoOn hAB).monotoneOn
  have hderiv : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      HasDerivWithinAt m (radius * Real.sin theta) (Icc 0 Real.pi) theta := by
    intro theta _htheta
    exact (hasDerivAt_intervalAngularDistance A B theta).hasDerivWithinAt
  have hsubst := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc hderiv hmono G
  have himage : m '' Icc 0 Real.pi = Icc A B := by
    exact intervalAngularDistance_image_Icc hAB
  rw [himage] at hsubst
  simp only [smul_eq_mul] at hsubst
  have hae : ∀ᵐ theta : ℝ ∂volume,
      theta ∈ Icc (0 : ℝ) Real.pi →
        radius * Real.sin theta * G (m theta) = g (m theta) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0,
      Measure.ae_ne (volume : Measure ℝ) Real.pi] with theta htheta0 hthetaPi
    intro htheta
    have hthetaPos : 0 < theta :=
      lt_of_le_of_ne htheta.1 (Ne.symm htheta0)
    have hthetaLt : theta < Real.pi :=
      lt_of_le_of_ne htheta.2 hthetaPi
    have hsin : 0 < Real.sin theta :=
      Real.sin_pos_of_pos_of_lt_pi hthetaPos hthetaLt
    have hradius : 0 < radius := by
      dsimp only [radius]
      linarith
    have hsqrt :
        Real.sqrt ((m theta - A) * (B - m theta)) =
          radius * Real.sin theta := by
      dsimp only [m, radius]
      exact sqrt_intervalAngularDistance_sub_mul hAB.le htheta
    dsimp only [G]
    rw [hsqrt]
    field_simp [(mul_pos hradius hsin).ne']
  have hsetCongr :
      (∫ theta in Icc (0 : ℝ) Real.pi,
          radius * Real.sin theta * G (m theta)) =
        ∫ theta in Icc (0 : ℝ) Real.pi, g (m theta) :=
    setIntegral_congr_ae measurableSet_Icc hae
  have hset :
      (∫ theta in Icc (0 : ℝ) Real.pi, g (m theta)) =
        ∫ y in Icc A B, G y := by
    rw [← hsetCongr]
    exact hsubst.symm
  calc
    (∫ theta : ℝ in 0..Real.pi,
        g (intervalAngularDistance A B theta)) =
        ∫ theta in Icc (0 : ℝ) Real.pi, g (m theta) := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ y in Icc A B, G y := hset
    _ = ∫ y : ℝ in A..B,
        g y / Real.sqrt ((y - A) * (B - y)) := by
      rw [intervalIntegral.integral_of_le hAB.le,
        ← integral_Icc_eq_integral_Ioc]

private lemma sqrt_inverted_arcsine_product
    {a e : ℝ} (ha : 0 < a) (he : e ∈ Icc a 2) :
    Real.sqrt ((e⁻¹ - (1 / 2 : ℝ)) * (a⁻¹ - e⁻¹)) =
      Real.sqrt ((e - a) * (2 - e)) /
        (Real.sqrt (2 * a) * e) := by
  have he0 : 0 < e := ha.trans_le he.1
  have ha2 : 0 < (2 : ℝ) := by norm_num
  have hK : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hX : 0 ≤ (e - a) * (2 - e) :=
    mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr he.2)
  have hY : 0 ≤ (e⁻¹ - (1 / 2 : ℝ)) * (a⁻¹ - e⁻¹) := by
    have hleft : (1 / 2 : ℝ) ≤ e⁻¹ := by
      rw [one_div, inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) he0]
      exact he.2
    have hright : e⁻¹ ≤ a⁻¹ := by
      exact inv_anti₀ ha he.1
    exact mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)
  have hrightNonneg :
      0 ≤ Real.sqrt ((e - a) * (2 - e)) /
        (Real.sqrt (2 * a) * e) := by positivity
  rw [Real.sqrt_eq_iff_eq_sq hY hrightNonneg]
  have hKsq : Real.sqrt (2 * a) ^ 2 = 2 * a :=
    Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
  rw [div_pow, Real.sq_sqrt hX, mul_pow, hKsq]
  field_simp [ha.ne', he0.ne']

private lemma inv_image_Icc {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    (fun e : ℝ ↦ e⁻¹) '' Icc a 2 = Icc (1 / 2 : ℝ) a⁻¹ := by
  let f : ℝ → ℝ := fun e ↦ e⁻¹
  have hanti : AntitoneOn f (Icc a 2) := by
    intro x hx y hy hxy
    exact inv_anti₀ (ha.trans_le hx.1) hxy
  have hcont : ContinuousOn f (Icc a 2) := by
    apply continuousOn_id.inv₀
    intro x hx
    exact (ha.trans_le hx.1).ne'
  calc
    f '' Icc a 2 = Icc (sInf (f '' Icc a 2)) (sSup (f '' Icc a 2)) :=
      hcont.image_Icc ha2.le
    _ = Icc (f 2) (f a) := by
      rw [hanti.sInf_image_Icc ha2.le, hanti.sSup_image_Icc ha2.le]
    _ = Icc (1 / 2 : ℝ) a⁻¹ := by
      simp only [f]
      norm_num

/-- Inversion transports the balayage-weighted arcsine density on `[a,2]`
to the ordinary arcsine density on `[1/2,1/a]`. -/
theorem integral_arcsine_balayage_inversion
    {a : ℝ} (ha : 0 < a) (ha2 : a < 2) (H : ℝ → ℝ) :
    (∫ e : ℝ in a..2,
        (Real.sqrt (2 * a) / e) * H e /
          Real.sqrt ((e - a) * (2 - e))) =
      ∫ y : ℝ in (1 / 2 : ℝ)..a⁻¹,
        H y⁻¹ /
          Real.sqrt ((y - (1 / 2 : ℝ)) * (a⁻¹ - y)) := by
  let f : ℝ → ℝ := fun e ↦ e⁻¹
  let G : ℝ → ℝ := fun y ↦
    H y⁻¹ / Real.sqrt ((y - (1 / 2 : ℝ)) * (a⁻¹ - y))
  have hanti : AntitoneOn f (Icc a 2) := by
    intro x hx y hy hxy
    exact inv_anti₀ (ha.trans_le hx.1) hxy
  have hderiv : ∀ e ∈ Icc a 2,
      HasDerivWithinAt f (-(e ^ 2)⁻¹) (Icc a 2) e := by
    intro e he
    exact (hasDerivAt_inv (ha.trans_le he.1).ne').hasDerivWithinAt
  have hsubst := integral_image_eq_integral_deriv_smul_of_antitone
    measurableSet_Icc hderiv hanti G
  have himage : f '' Icc a 2 = Icc (1 / 2 : ℝ) a⁻¹ :=
    inv_image_Icc ha ha2
  rw [himage] at hsubst
  simp only [neg_neg, smul_eq_mul] at hsubst
  have hae : ∀ᵐ e : ℝ ∂volume,
      e ∈ Icc a 2 →
        (e ^ 2)⁻¹ * G (f e) =
          (Real.sqrt (2 * a) / e) * H e /
            Real.sqrt ((e - a) * (2 - e)) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) a,
      Measure.ae_ne (volume : Measure ℝ) 2] with e hea he2
    intro he
    have hae' : a < e := lt_of_le_of_ne he.1 (Ne.symm hea)
    have he2' : e < 2 := lt_of_le_of_ne he.2 he2
    have he0 : 0 < e := ha.trans hae'
    have hK : 0 < Real.sqrt (2 * a) :=
      Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
    have hX : 0 < (e - a) * (2 - e) :=
      mul_pos (sub_pos.mpr hae') (sub_pos.mpr he2')
    have hsqrtX : 0 < Real.sqrt ((e - a) * (2 - e)) :=
      Real.sqrt_pos.2 hX
    have hsqrtInv := sqrt_inverted_arcsine_product ha he
    dsimp only [G, f]
    rw [inv_inv, hsqrtInv]
    field_simp [he0.ne', hK.ne', hsqrtX.ne']
  have hsetCongr :
      (∫ e in Icc a 2, (e ^ 2)⁻¹ * G (f e)) =
        ∫ e in Icc a 2,
          (Real.sqrt (2 * a) / e) * H e /
            Real.sqrt ((e - a) * (2 - e)) :=
    setIntegral_congr_ae measurableSet_Icc hae
  have hset :
      (∫ e in Icc a 2,
          (Real.sqrt (2 * a) / e) * H e /
            Real.sqrt ((e - a) * (2 - e))) =
        ∫ y in Icc (1 / 2 : ℝ) a⁻¹, G y := by
    rw [← hsetCongr]
    exact hsubst.symm
  have hhalfInv : (1 / 2 : ℝ) < a⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  calc
    (∫ e : ℝ in a..2,
        (Real.sqrt (2 * a) / e) * H e /
          Real.sqrt ((e - a) * (2 - e))) =
        ∫ e in Icc a 2,
          (Real.sqrt (2 * a) / e) * H e /
            Real.sqrt ((e - a) * (2 - e)) := by
      rw [intervalIntegral.integral_of_le ha2.le,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ y in Icc (1 / 2 : ℝ) a⁻¹, G y := hset
    _ = ∫ y : ℝ in (1 / 2 : ℝ)..a⁻¹,
        H y⁻¹ /
          Real.sqrt ((y - (1 / 2 : ℝ)) * (a⁻¹ - y)) := by
      rw [intervalIntegral.integral_of_le hhalfInv.le,
        ← integral_Icc_eq_integral_Ioc]

lemma platformAngularDistance_eq_intervalAngularDistance (a theta : ℝ) :
    platformAngularDistance a theta = intervalAngularDistance a 2 theta := by
  unfold platformAngularDistance platformCenter platformRadius
    intervalAngularDistance
  ring

/-- Angular form of the inversion transport: the factor
`sqrt(2a) / d(theta)` turns the equilibrium angle on `[a,2]` into the
equilibrium angle on `[1/2,1/a]`. -/
theorem integral_platformBalayage_comp_eq_invertedInterval
    {a : ℝ} (ha : 0 < a) (ha2 : a < 2) (H : ℝ → ℝ) :
    (∫ theta : ℝ in 0..Real.pi,
        (Real.sqrt (2 * a) / platformAngularDistance a theta) *
          H (platformAngularDistance a theta)) =
      ∫ psi : ℝ in 0..Real.pi,
        H (intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi)⁻¹ := by
  have hJ : (1 / 2 : ℝ) < a⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  calc
    (∫ theta : ℝ in 0..Real.pi,
        (Real.sqrt (2 * a) / platformAngularDistance a theta) *
          H (platformAngularDistance a theta)) =
        ∫ theta : ℝ in 0..Real.pi,
          (Real.sqrt (2 * a) /
              intervalAngularDistance a 2 theta) *
            H (intervalAngularDistance a 2 theta) := by
      apply intervalIntegral.integral_congr
      intro theta _htheta
      change
        (Real.sqrt (2 * a) / platformAngularDistance a theta) *
            H (platformAngularDistance a theta) =
          (Real.sqrt (2 * a) /
              intervalAngularDistance a 2 theta) *
            H (intervalAngularDistance a 2 theta)
      rw [platformAngularDistance_eq_intervalAngularDistance]
    _ = ∫ e : ℝ in a..2,
        ((Real.sqrt (2 * a) / e) * H e) /
          Real.sqrt ((e - a) * (2 - e)) :=
      integral_intervalAngular_comp_eq_arcsine ha2
        (fun e ↦ (Real.sqrt (2 * a) / e) * H e)
    _ = ∫ y : ℝ in (1 / 2 : ℝ)..a⁻¹,
        H y⁻¹ /
          Real.sqrt ((y - (1 / 2 : ℝ)) * (a⁻¹ - y)) :=
      integral_arcsine_balayage_inversion ha ha2 H
    _ = ∫ psi : ℝ in 0..Real.pi,
        H (intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi)⁻¹ := by
      symm
      exact integral_intervalAngular_comp_eq_arcsine hJ (fun y ↦ H y⁻¹)

private lemma invertedInterval_capacity {a : ℝ} (ha : 0 < a) :
    intervalLogCapacity (1 / 2 : ℝ) a⁻¹ =
      platformCapacity a / (2 * a) := by
  unfold intervalLogCapacity platformCapacity
  field_simp [ha.ne']

private lemma sqrt_half_mul_inv {a : ℝ} (ha : 0 < a) :
    Real.sqrt ((1 / 2 : ℝ) * a⁻¹) =
      Real.sqrt (2 * a) / (2 * a) := by
  have hrewrite : (1 / 2 : ℝ) * a⁻¹ = (2 * a)⁻¹ := by
    field_simp [ha.ne']
  rw [hrewrite, Real.sqrt_inv, ← Real.sqrt_div_self]

private lemma invertedInterval_exteriorD0 {a : ℝ} (ha : 0 < a) :
    intervalExteriorD0 (1 / 2 : ℝ) a⁻¹ =
      platformD0 a / (2 * a) := by
  rw [intervalExteriorD0, platformD0, sqrt_half_mul_inv ha]
  field_simp [ha.ne']

private lemma platformD0_pos {a : ℝ} (ha : 0 < a) :
    0 < platformD0 a := by
  unfold platformD0
  have hs : 0 < Real.sqrt (2 * a) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  positivity

private lemma inverted_logCapacity_sub_logD0
    {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    Real.log (intervalLogCapacity (1 / 2 : ℝ) a⁻¹) -
        Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) =
      Real.log (platformCapacity a) - Real.log (platformD0 a) := by
  have hcap : 0 < platformCapacity a := platformCapacity_pos ha2
  have hD : 0 < platformD0 a := platformD0_pos ha
  have hscale : 0 < 2 * a := mul_pos (by norm_num) ha
  rw [invertedInterval_capacity ha, invertedInterval_exteriorD0 ha,
    Real.log_div hcap.ne' hscale.ne', Real.log_div hD.ne' hscale.ne']
  ring

/-- Exact balayage potential identity from `(4.2)`: on `[a,2]`, the
weighted equilibrium potential is `log d + log H - log D₀`. -/
theorem integral_platformBalayage_log_potential
    {a theta : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (htheta : theta ∈ Icc 0 Real.pi) :
    (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          (Real.sqrt (2 * a) / platformAngularDistance a phi) *
            Real.log (abs
              (platformAngularDistance a theta -
                platformAngularDistance a phi))) =
      Real.log (platformAngularDistance a theta) +
        Real.log (platformCapacity a) - Real.log (platformD0 a) := by
  let d : ℝ := platformAngularDistance a theta
  let J : ℝ → ℝ :=
    intervalAngularDistance (1 / 2 : ℝ) a⁻¹
  have hdmem : d ∈ Icc a 2 :=
    platformAngularDistance_mem_Icc ha2.le htheta
  have hd : 0 < d := ha.trans_le hdmem.1
  have hJ : (1 / 2 : ℝ) < a⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) ha]
    exact ha2
  have hdinvMem : d⁻¹ ∈ Icc (1 / 2 : ℝ) a⁻¹ := by
    constructor
    · simpa only [one_div] using! inv_anti₀ hd hdmem.2
    · exact inv_anti₀ ha hdmem.1
  obtain ⟨thetaJ, hthetaJ, hthetaJEq⟩ :
      ∃ thetaJ ∈ Icc (0 : ℝ) Real.pi, J thetaJ = d⁻¹ := by
    have himage := intervalAngularDistance_image_Icc hJ
    rw [← himage] at hdinvMem
    rcases hdinvMem with ⟨thetaJ, hthetaJ, hthetaJEq⟩
    exact ⟨thetaJ, hthetaJ, hthetaJEq⟩
  have hEq := integral_intervalEquilibrium_log_potential hJ hthetaJ
  change (1 / Real.pi) *
      (∫ psi : ℝ in 0..Real.pi,
        Real.log (abs (J thetaJ - J psi))) =
    Real.log (intervalLogCapacity (1 / 2 : ℝ) a⁻¹) at hEq
  rw [hthetaJEq] at hEq
  have hExt := integral_intervalEquilibrium_log_exterior
    (show (0 : ℝ) < 1 / 2 by norm_num) hJ
  change (1 / Real.pi) *
      (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) =
    Real.log (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) at hExt
  have hJpos : ∀ psi ∈ Icc (0 : ℝ) Real.pi, 0 < J psi := by
    intro psi hpsi
    change 0 < intervalAngularDistance (1 / 2 : ℝ) a⁻¹ psi
    have hJmem : J psi ∈ Icc (1 / 2 : ℝ) a⁻¹ := by
      rw [← intervalAngularDistance_image_Icc hJ]
      exact ⟨psi, hpsi, rfl⟩
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hJmem.1
  have hzero :
      {psi : ℝ | d⁻¹ - J psi ≠ 0} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) Real.pi) := by
    have han : AnalyticOnNhd ℝ (fun psi ↦ d⁻¹ - J psi) Set.univ :=
      fun _ _ ↦ by
        dsimp only [J, intervalAngularDistance]
        fun_prop
    by_cases h0 : d⁻¹ - J 0 = 0
    · have hpi : d⁻¹ - J Real.pi ≠ 0 := by
        intro hpi
        have heq : J 0 = J Real.pi := by linarith
        have hne : J 0 ≠ J Real.pi := by
          dsimp only [J]
          simp only [intervalAngularDistance_zero,
            intervalAngularDistance_pi]
          exact ne_of_lt hJ
        exact hne heq
      apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      exact han.preimage_zero_mem_codiscrete hpi
    · apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      exact han.preimage_zero_mem_codiscrete h0
  have hdecomp :
      (∫ psi : ℝ in 0..Real.pi,
          Real.log (abs (d - (J psi)⁻¹))) =
        ∫ psi : ℝ in 0..Real.pi,
          Real.log d + Real.log (abs (d⁻¹ - J psi)) -
            Real.log (J psi) := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    filter_upwards [hzero,
      Filter.self_mem_codiscreteWithin (Set.uIoc (0 : ℝ) Real.pi)]
      with psi hne hpsi
    have hpsiIcc : psi ∈ Icc (0 : ℝ) Real.pi := by
      rw [uIoc_of_le Real.pi_pos.le] at hpsi
      exact ⟨hpsi.1.le, hpsi.2⟩
    have hy := hJpos psi hpsiIcc
    have hfactor : d - (J psi)⁻¹ = d * (J psi - d⁻¹) / J psi := by
      field_simp [hd.ne', hy.ne']
    have hsub : J psi - d⁻¹ ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hne (sub_eq_zero.mpr h.symm))
    have habsSub : |J psi - d⁻¹| ≠ 0 := abs_ne_zero.mpr hsub
    rw [hfactor, abs_div, abs_mul]
    rw [Real.log_div
      (mul_ne_zero (abs_ne_zero.mpr hd.ne') habsSub)
      (abs_ne_zero.mpr hy.ne')]
    rw [Real.log_mul (abs_ne_zero.mpr hd.ne') habsSub]
    rw [abs_of_pos hd, abs_of_pos hy, abs_sub_comm]
  have hlogEqInt :
      (∫ psi : ℝ in 0..Real.pi,
        Real.log (abs (d⁻¹ - J psi))) =
      Real.pi * Real.log
        (intervalLogCapacity (1 / 2 : ℝ) a⁻¹) := by
    calc
      (∫ psi : ℝ in 0..Real.pi,
          Real.log (abs (d⁻¹ - J psi))) =
          Real.pi * ((1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi,
              Real.log (abs (d⁻¹ - J psi)))) := by
            field_simp [Real.pi_ne_zero]
      _ = Real.pi * Real.log
          (intervalLogCapacity (1 / 2 : ℝ) a⁻¹) := by rw [hEq]
  have hlogExtInt :
      (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) =
      Real.pi * Real.log
        (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) := by
    calc
      (∫ psi : ℝ in 0..Real.pi, Real.log (J psi)) =
          Real.pi * ((1 / Real.pi) *
            (∫ psi : ℝ in 0..Real.pi, Real.log (J psi))) := by
            field_simp [Real.pi_ne_zero]
      _ = Real.pi * Real.log
          (intervalExteriorD0 (1 / 2 : ℝ) a⁻¹) := by rw [hExt]
  have hEqIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log (abs (d⁻¹ - J psi)))
      volume 0 Real.pi := by
    have han : AnalyticOnNhd ℝ (fun psi ↦ d⁻¹ - J psi) Set.univ :=
      fun _ _ ↦ by
        dsimp only [J, intervalAngularDistance]
        fun_prop
    have hmer : MeromorphicOn (fun psi ↦ d⁻¹ - J psi)
        (Set.uIcc 0 Real.pi) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hExtIntegrable : IntervalIntegrable
      (fun psi : ℝ ↦ Real.log (J psi)) volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    have hJcont : ContinuousOn J (Set.uIcc 0 Real.pi) := by
      change ContinuousOn
        (fun psi : ℝ ↦
          ((1 / 2 : ℝ) + a⁻¹) / 2 -
            (a⁻¹ - (1 / 2 : ℝ)) / 2 * Real.cos psi)
        (Set.uIcc 0 Real.pi)
      fun_prop
    exact hJcont.log (fun psi hpsi ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hpsi
      exact (hJpos psi hpsi).ne')
  have hInv := integral_platformBalayage_comp_eq_invertedInterval ha ha2
    (fun e ↦ Real.log (abs (d - e)))
  change (∫ phi : ℝ in 0..Real.pi,
      (Real.sqrt (2 * a) / platformAngularDistance a phi) *
        Real.log (abs (d - platformAngularDistance a phi))) =
    ∫ psi : ℝ in 0..Real.pi,
      Real.log (abs (d - (J psi)⁻¹)) at hInv
  rw [hInv, hdecomp,
    intervalIntegral.integral_sub
      ((intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ ↦ Real.log d) volume 0 Real.pi).add hEqIntegrable)
      hExtIntegrable,
    intervalIntegral.integral_add intervalIntegrable_const hEqIntegrable,
    intervalIntegral.integral_const, hlogEqInt, hlogExtInt]
  simp only [sub_zero, smul_eq_mul]
  dsimp only [d]
  field_simp [Real.pi_ne_zero]
  calc
    Real.log (platformAngularDistance a theta) +
          Real.log (intervalLogCapacity (1 / 2 : ℝ) (1 / a)) -
          Real.log (intervalExteriorD0 (1 / 2 : ℝ) (1 / a)) =
        Real.log (platformAngularDistance a theta) +
          (Real.log (intervalLogCapacity (1 / 2 : ℝ) (1 / a)) -
            Real.log (intervalExteriorD0 (1 / 2 : ℝ) (1 / a))) := by ring
    _ = Real.log (platformAngularDistance a theta) +
          (Real.log (platformCapacity a) - Real.log (platformD0 a)) := by
      rw [show
        Real.log (intervalLogCapacity (1 / 2 : ℝ) (1 / a)) -
              Real.log (intervalExteriorD0 (1 / 2 : ℝ) (1 / a)) =
            Real.log (platformCapacity a) - Real.log (platformD0 a) by
          simpa only [one_div] using! inverted_logCapacity_sub_logD0 ha ha2]
    _ = Real.log (platformAngularDistance a theta) +
          Real.log (platformCapacity a) - Real.log (platformD0 a) := by ring

private lemma intervalIntegrable_platform_equilibrium_kernel
    {a theta : ℝ} (_ha2 : a < 2) :
    IntervalIntegrable
      (fun phi : ℝ ↦ Real.log (abs
        (platformAngularDistance a theta - platformAngularDistance a phi)))
      volume 0 Real.pi := by
  have han : AnalyticOnNhd ℝ
      (fun phi : ℝ ↦
        platformAngularDistance a theta - platformAngularDistance a phi)
      Set.univ := fun _ _ ↦ by
        unfold platformAngularDistance
        fun_prop
  have hmer : MeromorphicOn
      (fun phi : ℝ ↦
        platformAngularDistance a theta - platformAngularDistance a phi)
      (Set.uIcc 0 Real.pi) :=
    fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using! MeromorphicOn.intervalIntegrable_log_norm hmer

/-- The equilibrium probability of `[a,2]` has constant logarithmic
potential `log ((2-a)/4)` on its support. -/
theorem integral_platformEquilibrium_log_potential
    {a theta : ℝ} (ha2 : a < 2) (htheta : theta ∈ Icc 0 Real.pi) :
    (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs
            (platformAngularDistance a theta - platformAngularDistance a phi))) =
      Real.log (platformCapacity a) := by
  have hr : 0 < platformRadius a := platformRadius_pos ha2
  have hcos := intervalIntegrable_log_abs_cos_sub theta 0 Real.pi
  have hzero :
      {phi : ℝ | Real.cos phi - Real.cos theta ≠ 0} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) Real.pi) := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ Real.cos phi - Real.cos theta) Set.univ :=
      fun _ _ ↦ by fun_prop
    by_cases hc : Real.cos theta = 1
    · apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      apply han.preimage_zero_mem_codiscrete (x := Real.pi)
      norm_num [hc]
    · apply Filter.codiscreteWithin_mono (Set.subset_univ _)
      apply han.preimage_zero_mem_codiscrete (x := 0)
      exact sub_ne_zero.mpr (fun h ↦ hc (by simpa using! h.symm))
  have hrewrite :
      (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs
            (platformAngularDistance a theta - platformAngularDistance a phi))) =
        ∫ phi : ℝ in 0..Real.pi,
          Real.log (platformRadius a) +
            Real.log |Real.cos phi - Real.cos theta| := by
    apply intervalIntegral.integral_congr_codiscreteWithin
    filter_upwards [hzero] with phi hphi
    have hfactor :
        platformAngularDistance a theta - platformAngularDistance a phi =
          platformRadius a * (Real.cos phi - Real.cos theta) := by
      unfold platformAngularDistance
      ring
    rw [hfactor, abs_mul,
      Real.log_mul (abs_ne_zero.mpr hr.ne') (abs_ne_zero.mpr hphi),
      abs_of_pos hr]
  rw [hrewrite, intervalIntegral.integral_add intervalIntegrable_const hcos,
    intervalIntegral.integral_const, integral_log_abs_cos_sub_zero_pi htheta]
  simp only [sub_zero, smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcap : platformCapacity a = platformRadius a / 2 := by
    simp only [platformCapacity, platformRadius]
    ring
  rw [hcap, Real.log_div hr.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [hpi]
  ring

/-- Equation `(4.6)` in angular coordinates.  The identity itself is
algebraic in `k`; the assumptions `k ≥ 1` and
`platformThreshold k ≤ a` are only needed elsewhere to make the reference
density nonnegative. -/
theorem integral_platformAngularDensity_log_potential
    {k a theta : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (htheta : theta ∈ Icc 0 Real.pi) :
    k * Real.log (platformAngularDistance a theta) +
        (1 / Real.pi) *
          (∫ phi : ℝ in 0..Real.pi,
            Real.log (abs
                (platformAngularDistance a theta -
                  platformAngularDistance a phi)) *
              platformAngularDensity k a phi) =
      Real.log (platformCapacity a) + k * Real.log (platformD0 a) := by
  let F : ℝ → ℝ := fun phi ↦
    Real.log (abs
      (platformAngularDistance a theta - platformAngularDistance a phi))
  let W : ℝ → ℝ := fun phi ↦
    (Real.sqrt (2 * a) / platformAngularDistance a phi) * F phi
  have hF : IntervalIntegrable F volume 0 Real.pi := by
    simpa only [F] using!
      intervalIntegrable_platform_equilibrium_kernel (a := a) (theta := theta) ha2
  have hweightContinuous : ContinuousOn
      (fun phi : ℝ ↦
        Real.sqrt (2 * a) / platformAngularDistance a phi)
      (Set.uIcc 0 Real.pi) := by
    apply continuousOn_const.div
    · unfold platformAngularDistance
      fun_prop
    · intro phi hphi
      rw [uIcc_of_le Real.pi_pos.le] at hphi
      exact (platformAngularDistance_pos ha ha2.le hphi).ne'
  have hW : IntervalIntegrable W volume 0 Real.pi := by
    simpa only [W] using! hF.continuousOn_mul hweightContinuous
  have hEq := integral_platformEquilibrium_log_potential ha2 htheta
  change (1 / Real.pi) * (∫ phi : ℝ in 0..Real.pi, F phi) =
    Real.log (platformCapacity a) at hEq
  have hBal := integral_platformBalayage_log_potential ha ha2 htheta
  change (1 / Real.pi) * (∫ phi : ℝ in 0..Real.pi, W phi) =
    Real.log (platformAngularDistance a theta) +
      Real.log (platformCapacity a) - Real.log (platformD0 a) at hBal
  have hDensity :
      (fun phi : ℝ ↦ F phi * platformAngularDensity k a phi) =
        fun phi ↦ (k + 1) * F phi - k * W phi := by
    funext phi
    simp only [F, W, platformAngularDensity, platformDensityCoefficient]
    ring
  have hsplit :
      (∫ phi : ℝ in 0..Real.pi,
          F phi * platformAngularDensity k a phi) =
        (k + 1) * (∫ phi : ℝ in 0..Real.pi, F phi) -
          k * (∫ phi : ℝ in 0..Real.pi, W phi) := by
    rw [hDensity,
      intervalIntegral.integral_sub (hF.const_mul (k + 1)) (hW.const_mul k),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  change k * Real.log (platformAngularDistance a theta) +
        (1 / Real.pi) *
          (∫ phi : ℝ in 0..Real.pi,
            F phi * platformAngularDensity k a phi) =
      Real.log (platformCapacity a) + k * Real.log (platformD0 a)
  rw [hsplit]
  calc
    k * Real.log (platformAngularDistance a theta) +
          (1 / Real.pi) *
            ((k + 1) * (∫ phi : ℝ in 0..Real.pi, F phi) -
              k * (∫ phi : ℝ in 0..Real.pi, W phi)) =
        k * Real.log (platformAngularDistance a theta) +
          (k + 1) *
            ((1 / Real.pi) * (∫ phi : ℝ in 0..Real.pi, F phi)) -
          k * ((1 / Real.pi) * (∫ phi : ℝ in 0..Real.pi, W phi)) := by ring
    _ = k * Real.log (platformAngularDistance a theta) +
          (k + 1) * Real.log (platformCapacity a) -
          k * (Real.log (platformAngularDistance a theta) +
            Real.log (platformCapacity a) - Real.log (platformD0 a)) := by
      rw [hEq, hBal]
    _ = Real.log (platformCapacity a) + k * Real.log (platformD0 a) := by ring

/-- The support-coordinate form of `(4.6)`, valid for every `d ∈ [a,2]`. -/
theorem integral_platformAngularDensity_log_potential_of_mem
    {k a d : ℝ} (ha : 0 < a) (ha2 : a < 2) (hd : d ∈ Icc a 2) :
    k * Real.log d +
        (1 / Real.pi) *
          (∫ phi : ℝ in 0..Real.pi,
            Real.log (abs (d - platformAngularDistance a phi)) *
              platformAngularDensity k a phi) =
      Real.log (platformCapacity a) + k * Real.log (platformD0 a) := by
  have hdimage : d ∈ platformAngularDistance a '' Icc (0 : ℝ) Real.pi := by
    rw [show platformAngularDistance a = intervalAngularDistance a 2 by
      funext theta
      exact platformAngularDistance_eq_intervalAngularDistance a theta,
      intervalAngularDistance_image_Icc ha2]
    exact hd
  rcases hdimage with ⟨theta, htheta, rfl⟩
  exact integral_platformAngularDensity_log_potential ha ha2 htheta

/-- Integration against the pushed constant-platform reference measure is
the normalized weighted angular integral. -/
theorem integral_platformConstantReferenceMeasure_log_kernel_eq_angular
    {k a d : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    (∫ e : ℝ, Real.log (abs (d - e))
        ∂(platformConstantReferenceMeasure k a)) =
      (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs (d - platformAngularDistance a phi)) *
            platformAngularDensity k a phi) := by
  let G : ℝ → ℝ := fun e ↦ Real.log (abs (d - e))
  let rho : ℝ → ℝ := fun phi ↦
    (1 / Real.pi) * platformAngularDensity k a phi
  have hDistanceMeasurable : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hGMeasurable : Measurable G := by
    dsimp only [G]
    fun_prop
  have hRhoMeasurable : Measurable
      (fun phi ↦ ENNReal.ofReal (rho phi)) := by
    apply Measurable.ennreal_ofReal
    dsimp only [rho, platformAngularDensity, platformDensityCoefficient,
      platformAngularDistance]
    fun_prop
  rw [platformConstantReferenceMeasure,
    integral_map hDistanceMeasurable.aemeasurable
      hGMeasurable.aestronglyMeasurable,
    platformAngularReferenceMeasure]
  change (∫ phi : ℝ, G (platformAngularDistance a phi)
      ∂(volume.restrict (Ioc 0 Real.pi)).withDensity
        (fun phi ↦ ENNReal.ofReal (rho phi))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hRhoMeasurable
    (ae_of_all _ fun phi ↦ ENNReal.ofReal_lt_top)]
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  calc
    (∫ phi : ℝ in 0..Real.pi,
        (ENNReal.ofReal (rho phi)).toReal •
          G (platformAngularDistance a phi)) =
        ∫ phi : ℝ in 0..Real.pi,
          (1 / Real.pi) *
            (G (platformAngularDistance a phi) *
              platformAngularDensity k a phi) := by
      apply intervalIntegral.integral_congr
      intro phi hphi
      rw [uIcc_of_le Real.pi_pos.le] at hphi
      have hnonneg : 0 ≤ rho phi :=
        mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
          (platformAngularDensity_nonneg hk ha ha2.le hthreshold hphi)
      change (ENNReal.ofReal (rho phi)).toReal •
          G (platformAngularDistance a phi) =
        (1 / Real.pi) *
          (G (platformAngularDistance a phi) *
            platformAngularDensity k a phi)
      rw [ENNReal.toReal_ofReal hnonneg]
      simp only [rho, smul_eq_mul]
      ring
    _ = (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          G (platformAngularDistance a phi) *
            platformAngularDensity k a phi) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / Real.pi) *
        (∫ phi : ℝ in 0..Real.pi,
          Real.log (abs (d - platformAngularDistance a phi)) *
            platformAngularDensity k a phi) := by
      rfl

/-- Measure-theoretic form of manuscript equation `(4.6)`.  The threshold
assumption makes the density nonnegative, hence the pushed object above is
the reference probability measure. -/
theorem integral_platformConstantReferenceMeasure_log_potential
    {k a d : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (hd : d ∈ Icc a 2) :
    k * Real.log d +
        (∫ e : ℝ, Real.log (abs (d - e))
          ∂(platformConstantReferenceMeasure k a)) =
      Real.log (platformCapacity a) + k * Real.log (platformD0 a) := by
  rw [integral_platformConstantReferenceMeasure_log_kernel_eq_angular
    hk ha ha2 hthreshold]
  exact integral_platformAngularDensity_log_potential_of_mem ha ha2 hd

end

end Erdos1038
