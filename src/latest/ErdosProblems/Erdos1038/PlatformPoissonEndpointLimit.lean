import ErdosProblems.Erdos1038.PlatformPoissonIntegral

/-!
# One-sided endpoint convergence of the platform Poisson kernel

The half-circle Poisson kernel is an approximate identity at the right
endpoint.  The proof is elementary: a short terminal arc is controlled by
continuity and the exact mass identity, while the complementary arc is
handled by dominated convergence away from the singular endpoint.
-/

set_option warningAsError false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

lemma platformPoissonKernel_nonneg {rho theta : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    0 ≤ platformPoissonKernel rho theta := by
  unfold platformPoissonKernel
  exact div_nonneg (by nlinarith [sq_nonneg rho])
    (platformPoissonKernel_den_pos hrho0 hrho1).le

lemma integral_platformPoissonKernel_reflected {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    (∫ theta in 0..Real.pi,
        platformPoissonKernel rho (Real.pi - theta)) = Real.pi := by
  rw [intervalIntegral.integral_comp_sub_left]
  simpa using! integral_platformPoissonKernel hrho0 hrho1

/-- A nonnegative sequence of interior radii converging to one sends the
half-circle Poisson convolution of an integrable function to its one-sided
continuous value at `pi`. -/
theorem tendsto_platformPoissonEndpointIntegral
    {F : ℝ → ℝ}
    (hFmeas : Measurable F)
    (hFint : IntervalIntegrable F volume 0 Real.pi)
    (hFcont : ContinuousWithinAt F (Icc (0 : ℝ) Real.pi) Real.pi)
    {lambda : ℕ → ℝ}
    (hlambda0 : ∀ n, 0 ≤ lambda n)
    (hlambda1 : ∀ n, lambda n < 1)
    (hlambda : Tendsto lambda atTop (nhds 1)) :
    Tendsto
      (fun n ↦ (1 / Real.pi) *
        ∫ theta in 0..Real.pi,
          F theta * platformPoissonKernel (lambda n) (Real.pi - theta))
      atTop (nhds (F Real.pi)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let eta := epsilon / 4
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  obtain ⟨delta, hdelta, hcontinuous⟩ :=
    (Metric.continuousWithinAt_iff.mp hFcont) eta heta
  let width := min (delta / 2) (Real.pi / 2)
  let cut := Real.pi - width
  have hwidth : 0 < width := by
    dsimp only [width]
    exact lt_min (half_pos hdelta) (half_pos Real.pi_pos)
  have hwidthDelta : width < delta := by
    dsimp only [width]
    exact (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have hwidthPi : width ≤ Real.pi := by
    dsimp only [width]
    exact (min_le_right _ _).trans (half_le_self Real.pi_pos.le)
  have hcut0 : 0 ≤ cut := by
    dsimp only [cut]
    linarith
  have hcutPi : cut < Real.pi := by
    dsimp only [cut]
    linarith
  have hcutPiLe : cut ≤ Real.pi := hcutPi.le
  have hwidthMem : width ∈ Icc (0 : ℝ) Real.pi :=
    ⟨hwidth.le, hwidthPi⟩
  have hcosWidth : 0 < 1 - Real.cos width := by
    have hcoslt : Real.cos width < Real.cos 0 :=
      Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ hwidthMem hwidth
    simpa only [Real.cos_zero] using! sub_pos.mpr hcoslt
  have herrorInt : IntervalIntegrable (fun theta ↦ F theta - F Real.pi)
      volume 0 Real.pi := hFint.sub intervalIntegrable_const
  have hhalf : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ lambda n := by
    have hnhds : Ioi (1 / 2 : ℝ) ∈ nhds (1 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    filter_upwards [hlambda.eventually hnhds] with n hn
    exact hn.le
  let farTerm : ℕ → ℝ → ℝ := fun n theta ↦
    (F theta - F Real.pi) *
      platformPoissonKernel (lambda n) (Real.pi - theta)
  let farBound : ℝ → ℝ := fun theta ↦
    (1 / (1 - Real.cos width)) * |F theta - F Real.pi|
  have hfarMeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (farTerm n)
        (volume.restrict (uIoc (0 : ℝ) cut)) := by
    apply Eventually.of_forall
    intro n
    apply Measurable.aestronglyMeasurable
    dsimp only [farTerm]
    exact (hFmeas.sub measurable_const).mul (by
      unfold platformPoissonKernel
      fun_prop)
  have hfarBound : ∀ᶠ n : ℕ in atTop, ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) cut →
        ‖farTerm n theta‖ ≤ farBound theta := by
    filter_upwards [hhalf] with n hn
    filter_upwards with theta
    intro htheta
    rw [uIoc_of_le hcut0] at htheta
    have htheta0 : 0 ≤ theta := htheta.1.le
    have hthetaCut : theta ≤ cut := htheta.2
    have ht0 : 0 ≤ Real.pi - theta := by linarith
    have htPi : Real.pi - theta ≤ Real.pi := by linarith
    have hwidthT : width ≤ Real.pi - theta := by
      dsimp only [cut] at hthetaCut
      linarith
    have hcos : Real.cos (Real.pi - theta) ≤ Real.cos width :=
      Real.cos_le_cos_of_nonneg_of_le_pi hwidth.le htPi hwidthT
    have hr0 := hlambda0 n
    have hr1 := hlambda1 n
    have hdenPos := platformPoissonKernel_den_pos
      (θ := Real.pi - theta) hr0 hr1
    have hdenLower :
        1 - Real.cos width ≤
          1 - 2 * lambda n * Real.cos (Real.pi - theta) + lambda n ^ 2 := by
      have htwor : 1 ≤ 2 * lambda n := by linarith
      have honeCos : 0 ≤ 1 - Real.cos (Real.pi - theta) :=
        sub_nonneg.mpr (Real.cos_le_one _)
      have hfactor :
          1 - Real.cos width ≤
            2 * lambda n * (1 - Real.cos (Real.pi - theta)) := by
        calc
          1 - Real.cos width ≤ 1 - Real.cos (Real.pi - theta) := by
            linarith
          _ ≤ 2 * lambda n * (1 - Real.cos (Real.pi - theta)) := by
            nlinarith
      nlinarith [sq_nonneg (1 - lambda n)]
    have hnum1 : 1 - lambda n ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (lambda n)]
    have hkernelBound :
        platformPoissonKernel (lambda n) (Real.pi - theta) ≤
          1 / (1 - Real.cos width) := by
      unfold platformPoissonKernel
      apply (div_le_div_iff₀ hdenPos hcosWidth).2
      calc
        (1 - lambda n ^ 2) * (1 - Real.cos width) ≤
            1 * (1 - Real.cos width) :=
          mul_le_mul_of_nonneg_right hnum1 hcosWidth.le
        _ = 1 - Real.cos width := one_mul _
        _ ≤ 1 *
            (1 - 2 * lambda n * Real.cos (Real.pi - theta) +
              lambda n ^ 2) := by simpa using! hdenLower
    have hkernel0 := platformPoissonKernel_nonneg
      (theta := Real.pi - theta) hr0 hr1
    dsimp only [farTerm, farBound]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel0]
    calc
      |F theta - F Real.pi| *
          platformPoissonKernel (lambda n) (Real.pi - theta) ≤
          |F theta - F Real.pi| * (1 / (1 - Real.cos width)) :=
        mul_le_mul_of_nonneg_left hkernelBound (abs_nonneg _)
      _ = 1 / (1 - Real.cos width) * |F theta - F Real.pi| := by
        ring
  have hfarBoundInt : IntervalIntegrable farBound volume 0 cut := by
    have hsubset : uIcc (0 : ℝ) cut ⊆ uIcc (0 : ℝ) Real.pi := by
      rw [uIcc_of_le hcut0, uIcc_of_le Real.pi_pos.le]
      exact Icc_subset_Icc le_rfl hcutPiLe
    dsimp only [farBound]
    exact (herrorInt.mono_set hsubset).abs.const_mul
      (1 / (1 - Real.cos width))
  have hfarPointwise : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) cut →
        Tendsto (fun n ↦ farTerm n theta) atTop (nhds 0) := by
    filter_upwards with theta
    intro htheta
    rw [uIoc_of_le hcut0] at htheta
    have htheta0 : 0 < theta := htheta.1
    have hthetaCut : theta ≤ cut := htheta.2
    have ht0 : 0 < Real.pi - theta := by linarith
    have htPi : Real.pi - theta ≤ Real.pi := by linarith
    have hcoslt : Real.cos (Real.pi - theta) < 1 := by
      have := Real.strictAntiOn_cos
        ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht0.le, htPi⟩ ht0
      simpa only [Real.cos_zero] using! this
    have hdenLimit : 1 - 2 * Real.cos (Real.pi - theta) + 1 ≠ 0 := by
      nlinarith
    have hnumTendsto : Tendsto
        (fun n ↦ 1 - lambda n ^ 2) atTop (nhds 0) := by
      convert! tendsto_const_nhds.sub (hlambda.pow 2) using 1
      all_goals norm_num
    have hdenTendsto : Tendsto
        (fun n ↦ 1 - 2 * lambda n * Real.cos (Real.pi - theta) +
          lambda n ^ 2)
        atTop (nhds (1 - 2 * Real.cos (Real.pi - theta) + 1)) := by
      convert!
        (tendsto_const_nhds.sub
          ((tendsto_const_nhds.mul hlambda).mul tendsto_const_nhds)).add
            (hlambda.pow 2) using 1
      all_goals norm_num
    have hkernelTendsto : Tendsto
        (fun n ↦ platformPoissonKernel (lambda n) (Real.pi - theta))
        atTop (nhds 0) := by
      unfold platformPoissonKernel
      simpa using! hnumTendsto.div hdenTendsto hdenLimit
    dsimp only [farTerm]
    simpa using! (tendsto_const_nhds.mul hkernelTendsto)
  have hfarTendsto : Tendsto
      (fun n ↦ ∫ theta in 0..cut, farTerm n theta)
      atTop (nhds 0) := by
    simpa using! intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      farBound hfarMeas hfarBound hfarBoundInt hfarPointwise
  have hfarSmall : ∀ᶠ n : ℕ in atTop,
      |∫ theta in 0..cut, farTerm n theta| < eta * Real.pi := by
    have hball := hfarTendsto.eventually
      (Metric.ball_mem_nhds 0 (mul_pos heta Real.pi_pos))
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using! hball
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hfarSmall)
  refine ⟨N, ?_⟩
  intro n hn
  have hfarSmallN := hN n hn
  have hr0 := hlambda0 n
  have hr1 := hlambda1 n
  let reflectedKernel : ℝ → ℝ := fun theta ↦
    platformPoissonKernel (lambda n) (Real.pi - theta)
  have hreflectedContinuous : Continuous reflectedKernel := by
    dsimp only [reflectedKernel]
    unfold platformPoissonKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro theta
      exact (platformPoissonKernel_den_pos
        (θ := Real.pi - theta) hr0 hr1).ne'
  have hreflectedInt : IntervalIntegrable reflectedKernel volume 0 Real.pi :=
    hreflectedContinuous.intervalIntegrable 0 Real.pi
  have hreflectedNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) Real.pi)]
      reflectedKernel := by
    filter_upwards with theta
    exact platformPoissonKernel_nonneg hr0 hr1
  have hnearMass :
      (∫ theta in cut..Real.pi, reflectedKernel theta) ≤ Real.pi := by
    calc
      (∫ theta in cut..Real.pi, reflectedKernel theta) ≤
          ∫ theta in 0..Real.pi, reflectedKernel theta :=
        intervalIntegral.integral_mono_interval hcut0 hcutPiLe le_rfl
          hreflectedNonneg hreflectedInt
      _ = Real.pi := integral_platformPoissonKernel_reflected hr0 hr1
  have hnearContinuity : ∀ theta ∈ Icc cut Real.pi,
      |F theta - F Real.pi| < eta := by
    intro theta htheta
    have hthetaCut : cut ≤ theta := htheta.1
    have hthetaFull : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hcut0.trans htheta.1, htheta.2⟩
    have hdist : dist theta Real.pi < delta := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htheta.2)]
      dsimp only [cut] at hthetaCut
      linarith
    simpa only [Real.dist_eq] using! hcontinuous hthetaFull hdist
  have hnearErrorInt : IntervalIntegrable
      (fun theta ↦ F theta - F Real.pi) volume cut Real.pi := by
    have hsubset : uIcc cut Real.pi ⊆ uIcc (0 : ℝ) Real.pi := by
      rw [uIcc_of_le hcutPiLe, uIcc_of_le Real.pi_pos.le]
      exact Icc_subset_Icc hcut0 le_rfl
    exact herrorInt.mono_set hsubset
  have hnearProductInt : IntervalIntegrable
      (fun theta ↦ (F theta - F Real.pi) * reflectedKernel theta)
      volume cut Real.pi :=
    hnearErrorInt.mul_continuousOn hreflectedContinuous.continuousOn
  have hnearMajorantInt : IntervalIntegrable
      (fun theta ↦ eta * reflectedKernel theta) volume cut Real.pi :=
    (continuous_const.mul hreflectedContinuous).intervalIntegrable cut Real.pi
  have hnearAbs :
      |∫ theta in cut..Real.pi,
          (F theta - F Real.pi) * reflectedKernel theta| ≤
        eta * Real.pi := by
    calc
      |∫ theta in cut..Real.pi,
          (F theta - F Real.pi) * reflectedKernel theta| ≤
          ∫ theta in cut..Real.pi,
            |(F theta - F Real.pi) * reflectedKernel theta| :=
        intervalIntegral.abs_integral_le_integral_abs hcutPiLe
      _ ≤ ∫ theta in cut..Real.pi, eta * reflectedKernel theta := by
        apply intervalIntegral.integral_mono_on hcutPiLe
          hnearProductInt.abs hnearMajorantInt
        intro theta htheta
        have hkernel0 : 0 ≤ reflectedKernel theta :=
          platformPoissonKernel_nonneg hr0 hr1
        rw [abs_mul, abs_of_nonneg hkernel0]
        exact mul_le_mul_of_nonneg_right
          (hnearContinuity theta htheta |>.le) hkernel0
      _ = eta * ∫ theta in cut..Real.pi, reflectedKernel theta := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ eta * Real.pi := mul_le_mul_of_nonneg_left hnearMass heta.le
  have hfullMass :
      (∫ theta in 0..Real.pi, reflectedKernel theta) = Real.pi :=
    integral_platformPoissonKernel_reflected hr0 hr1
  have hconstantConvolution :
      (1 / Real.pi) *
          (∫ theta in 0..Real.pi, F Real.pi * reflectedKernel theta) =
        F Real.pi := by
    rw [intervalIntegral.integral_const_mul, hfullMass]
    field_simp [Real.pi_ne_zero]
  have hconstantInt : IntervalIntegrable
      (fun _theta : ℝ ↦ F Real.pi) volume 0 Real.pi :=
    intervalIntegrable_const
  have hFProductInt : IntervalIntegrable
      (fun theta ↦ F theta * reflectedKernel theta) volume 0 Real.pi :=
    hFint.mul_continuousOn hreflectedContinuous.continuousOn
  have hconstantProductInt : IntervalIntegrable
      (fun theta ↦ F Real.pi * reflectedKernel theta) volume 0 Real.pi :=
    hconstantInt.mul_continuousOn hreflectedContinuous.continuousOn
  have hconvolutionError :
      (1 / Real.pi) *
          (∫ theta in 0..Real.pi, F theta * reflectedKernel theta) -
        F Real.pi =
      (1 / Real.pi) *
          ∫ theta in 0..Real.pi,
            (F theta - F Real.pi) * reflectedKernel theta := by
    calc
      (1 / Real.pi) *
          (∫ theta in 0..Real.pi, F theta * reflectedKernel theta) -
        F Real.pi =
          (1 / Real.pi) *
              (∫ theta in 0..Real.pi, F theta * reflectedKernel theta) -
            (1 / Real.pi) *
              (∫ theta in 0..Real.pi,
                F Real.pi * reflectedKernel theta) :=
        congrArg
          (fun z : ℝ ↦ (1 / Real.pi) *
            (∫ theta in 0..Real.pi, F theta * reflectedKernel theta) - z)
          hconstantConvolution.symm
      _ = (1 / Real.pi) *
          ((∫ theta in 0..Real.pi, F theta * reflectedKernel theta) -
            ∫ theta in 0..Real.pi,
              F Real.pi * reflectedKernel theta) := by ring
      _ = (1 / Real.pi) *
          ∫ theta in 0..Real.pi,
            (F theta - F Real.pi) * reflectedKernel theta := by
        congr 1
        rw [← intervalIntegral.integral_sub
          hFProductInt hconstantProductInt]
        apply intervalIntegral.integral_congr
        intro theta _htheta
        ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((herrorInt.mono_set (by
      rw [uIcc_of_le hcut0, uIcc_of_le Real.pi_pos.le]
      exact Icc_subset_Icc le_rfl hcutPiLe)).mul_continuousOn
        hreflectedContinuous.continuousOn)
    hnearProductInt
  have htotalSmall :
      |∫ theta in 0..Real.pi,
          (F theta - F Real.pi) * reflectedKernel theta| <
        2 * eta * Real.pi := by
    rw [← hsplit]
    calc
      |(∫ theta in 0..cut,
          (F theta - F Real.pi) * reflectedKernel theta) +
          ∫ theta in cut..Real.pi,
            (F theta - F Real.pi) * reflectedKernel theta| ≤
          |∫ theta in 0..cut,
            (F theta - F Real.pi) * reflectedKernel theta| +
          |∫ theta in cut..Real.pi,
            (F theta - F Real.pi) * reflectedKernel theta| := abs_add_le _ _
      _ < eta * Real.pi + eta * Real.pi :=
        add_lt_add_of_lt_of_le hfarSmallN hnearAbs
      _ = 2 * eta * Real.pi := by ring
  rw [Real.dist_eq, hconvolutionError]
  rw [abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  calc
    1 / Real.pi *
        |∫ theta in 0..Real.pi,
          (F theta - F Real.pi) * reflectedKernel theta| <
        (1 / Real.pi) * (2 * eta * Real.pi) :=
      mul_lt_mul_of_pos_left htotalSmall (one_div_pos.mpr Real.pi_pos)
    _ = epsilon / 2 := by
      dsimp only [eta]
      field_simp [Real.pi_ne_zero]
      ring
    _ < epsilon := half_lt_self hepsilon

end

end Erdos1038
