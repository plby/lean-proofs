import ErdosProblems.Erdos1038.PlatformResidualMaterialFourier
import ErdosProblems.Erdos1038.PlatformPoissonFourierSeries
import ErdosProblems.Erdos1038.PlatformPoissonEndpointLimit
import ErdosProblems.Erdos1038.PlatformAdjointAbelEndpointLimit

/-!
# Poisson representation of the residual endpoint Abel series

For a fixed interior Abel parameter, the signed endpoint cosine series of
the concrete material field is exactly convolution with the Poisson kernel
centered at `pi`.  This is the bridge from the abstract endpoint series to
the one-sided material value at the top platform endpoint.
-/

set_option warningAsError false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private def residualEndpointPoissonTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho : ℝ) (n : ℕ) (theta : ℝ) : ℝ :=
  platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
    (2 * rho ^ (n + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)))

private def residualEndpointPoissonBound
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho : ℝ) (n : ℕ) (theta : ℝ) : ℝ :=
  2 * |rho| ^ (n + 1) *
    |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|

private theorem hasSum_integral_residualEndpointPoissonTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) :
    HasSum
      (fun n ↦ ∫ theta in 0..Real.pi,
        residualEndpointPoissonTerm C k a hk ha ha2 hthreshold
          rho n theta)
      (∫ theta in 0..Real.pi,
        platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
          (platformPoissonKernel rho (Real.pi - theta) - 1)) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let term := residualEndpointPoissonTerm C k a hk ha ha2 hthreshold rho
  let bound := residualEndpointPoissonBound C k a hk ha ha2 hthreshold rho
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hFmeas : Measurable F :=
    measurable_platformResidualMaterialField C k a hk ha ha2 hthreshold
  have htermMeas (n : ℕ) : AEStronglyMeasurable (term n)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun theta ↦
      F theta *
        (2 * rho ^ (n + 1) *
          Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta))))
    exact hFmeas.mul (by fun_prop)
  have hboundPoint (n : ℕ) : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi →
        ‖term n theta‖ ≤ bound n theta := by
    filter_upwards with theta
    intro _htheta
    dsimp only [term, bound, residualEndpointPoissonTerm,
      residualEndpointPoissonBound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| *
          (2 * |rho| ^ (n + 1) *
            |Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta))|) ≤
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| *
            (2 * |rho| ^ (n + 1) * 1) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (Real.abs_cos_le_one
                    (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)))
                  (mul_nonneg (by norm_num)
                    (pow_nonneg (abs_nonneg rho) (n + 1))))
                (abs_nonneg _)
      _ = 2 * |rho| ^ (n + 1) *
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta| := by
            ring
  have hgeom : Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) := by
    exact (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (abs_nonneg rho) hrho)
  have hboundSummable : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi → Summable (fun n ↦ bound n theta) := by
    filter_upwards with theta
    intro _htheta
    dsimp only [bound, residualEndpointPoissonBound]
    have hs := hgeom.mul_right
      (2 * |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|)
    exact hs.congr (fun n ↦ by ring)
  have hboundTsum : (fun theta ↦ ∑' n, bound n theta) =
      fun theta ↦
        (2 * ∑' n : ℕ, |rho| ^ (n + 1)) * |F theta| := by
    funext theta
    dsimp only [bound, residualEndpointPoissonBound, F]
    rw [show (∑' n : ℕ,
        2 * |rho| ^ (n + 1) *
          |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|) =
        (∑' n : ℕ, |rho| ^ (n + 1)) *
          (2 * |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|) by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      ring]
    ring
  have hboundIntegrable : IntervalIntegrable
      (fun theta ↦ ∑' n, bound n theta) volume 0 Real.pi := by
    rw [hboundTsum]
    exact hF.abs.const_mul (2 * ∑' n : ℕ, |rho| ^ (n + 1))
  have htermHasSum : ∀ᵐ theta ∂volume,
      theta ∈ uIoc (0 : ℝ) Real.pi →
        HasSum (fun n ↦ term n theta)
          (F theta * (platformPoissonKernel rho (Real.pi - theta) - 1)) := by
    filter_upwards with theta
    intro _htheta
    let base : ℕ → ℝ := fun n ↦
      2 * rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta))
    have hbase : Summable base := by
      apply Summable.of_norm_bounded (hgeom.mul_left 2)
      intro n
      calc
        ‖base n‖ = 2 * |rho| ^ (n + 1) *
            |Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta))| := by
              simp only [base, Real.norm_eq_abs, abs_mul, abs_pow,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * |rho| ^ (n + 1) := by
              exact mul_le_of_le_one_right
                (mul_nonneg (by norm_num)
                  (pow_nonneg (abs_nonneg rho) (n + 1)))
                (Real.abs_cos_le_one
                  (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)))
    have hkernel := platformPoissonKernel_eq_one_add_two_tsum
      hrho (Real.pi - theta)
    have hbaseTsum : ∑' n, base n =
        platformPoissonKernel rho (Real.pi - theta) - 1 := by
      dsimp only [base]
      rw [show (∑' n : ℕ,
          2 * rho ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta))) =
          2 * ∑' n : ℕ,
            rho ^ (n + 1) *
              Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        ring]
      linarith
    have hscaled := hbase.hasSum.mul_left (F theta)
    rw [hbaseTsum] at hscaled
    exact HasSum.congr_fun hscaled (fun _n ↦ rfl)
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    bound htermMeas hboundPoint hboundSummable hboundIntegrable htermHasSum

/-- For every interior parameter, the concrete endpoint Abel series is
exactly its Poisson convolution at the top endpoint. -/
theorem platformResidualMaterialAbelEndpoint_eq_poissonIntegral
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    platformAbelEndpointSeriesValue
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) rho =
      (1 / Real.pi) *
        ∫ theta in 0..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
            platformPoissonKernel rho (Real.pi - theta) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let coefficient := platformResidualMaterialCosineCoefficient
    C k a hk ha ha2 hthreshold
  let f0 := platformResidualMaterialMean C k a hk ha ha2 hthreshold
  let seq : ℕ → ℝ := fun n ↦
    platformAbelEndpointSequence coefficient n * rho ^ n
  have hrhoAbs : |rho| < 1 := by
    rw [abs_of_nonneg hrho0]
    exact hrho1
  have hbound := platformResidualMaterialCosineCoefficient_bounded
    C k a hk ha ha2 hthreshold
  have hseries := hasSum_integral_residualEndpointPoissonTerm
    C k a hk ha ha2 hthreshold hrhoAbs
  have hseriesScaled := hseries.mul_left (1 / Real.pi)
  have hterm (n : ℕ) :
      (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            residualEndpointPoissonTerm C k a hk ha ha2 hthreshold
              rho n theta) = seq (n + 1) := by
    have hcos (theta : ℝ) :
        Real.cos (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)) =
          (-1 : ℝ) ^ (n + 1) *
            Real.cos (((n + 1 : ℕ) : ℝ) * theta) := by
      rw [show (((n + 1 : ℕ) : ℝ) * (Real.pi - theta)) =
          ((n + 1 : ℕ) : ℝ) * Real.pi -
            (((n + 1 : ℕ) : ℝ) * theta) by ring,
        Real.cos_nat_mul_pi_sub]
    have hintegrand :
        (fun theta ↦
          residualEndpointPoissonTerm C k a hk ha ha2 hthreshold
            rho n theta) =
        fun theta ↦
          (2 * rho ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
            (F theta * Real.cos (((n + 1 : ℕ) : ℝ) * theta)) := by
      funext theta
      dsimp only [residualEndpointPoissonTerm, F]
      rw [hcos]
      ring
    rw [hintegrand, intervalIntegral.integral_const_mul]
    dsimp only [seq]
    rw [platformAbelEndpointSequence_of_pos coefficient (by omega)]
    dsimp only [coefficient, platformResidualMaterialCosineCoefficient]
    ring
  have hshift : HasSum (fun n ↦ seq (n + 1))
      ((1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho (Real.pi - theta) - 1))) := by
    exact HasSum.congr_fun hseriesScaled (fun n ↦ (hterm n).symm)
  have hseqSummable : Summable seq := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_comm] using! hshift.summable
  have hseqTsum : ∑' n, seq n =
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho (Real.pi - theta) - 1)) := by
    rw [hseqSummable.tsum_eq_zero_add]
    have hzero : seq 0 = 0 := by
      simp [seq]
    rw [hzero, zero_add]
    simpa only [Nat.add_comm] using! hshift.tsum_eq
  have hendpoint := platformAbelEndpointSeriesValue_eq_tsum_endpointSequence
    hrhoAbs hbound f0
  change platformAbelEndpointSeriesValue f0 coefficient rho = _
  rw [hendpoint]
  change f0 + ∑' n, seq n = _
  rw [hseqTsum]
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hP : Continuous
      (fun theta ↦ platformPoissonKernel rho (Real.pi - theta)) := by
    unfold platformPoissonKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro theta
      exact (platformPoissonKernel_den_pos hrho0 hrho1).ne'
  have hdiff : IntervalIntegrable
      (fun theta ↦ F theta *
        (platformPoissonKernel rho (Real.pi - theta) - 1))
      volume 0 Real.pi :=
    hF.mul_continuousOn (hP.sub continuous_const).continuousOn
  have hsumIntegral :
      (∫ theta in 0..Real.pi,
        F theta * platformPoissonKernel rho (Real.pi - theta)) =
      (∫ theta in 0..Real.pi, F theta) +
        ∫ theta in 0..Real.pi,
          F theta * (platformPoissonKernel rho (Real.pi - theta) - 1) := by
    rw [← intervalIntegral.integral_add hF hdiff]
    apply intervalIntegral.integral_congr
    intro theta _htheta
    ring
  dsimp only [f0, platformResidualMaterialMean]
  rw [hsumIntegral]
  ring

/-- Along any nonnegative interior Abel approach, the concrete endpoint
series converges to the one-sided material value at `pi`. -/
theorem tendsto_platformResidualMaterialAbelEndpoint
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {lambda : ℕ → ℝ} (hlambda : InteriorAbelApproach lambda)
    (hlambda0 : ∀ n, 0 ≤ lambda n) :
    Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) (lambda n))
      atTop
      (nhds (platformResidualMaterialField
        C k a hk ha ha2 hthreshold Real.pi)) := by
  have hlambda1 (n : ℕ) : lambda n < 1 := by
    exact (le_abs_self (lambda n)).trans_lt (hlambda.1 n)
  have hpoisson := tendsto_platformPoissonEndpointIntegral
    (measurable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold)
    (intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold)
    (continuousWithinAt_platformResidualMaterialField_pi
      C k a hk ha ha2 hthreshold)
    hlambda0 hlambda1 hlambda.2
  apply hpoisson.congr'
  filter_upwards with n
  exact (platformResidualMaterialAbelEndpoint_eq_poissonIntegral
    C k a hk ha ha2 hthreshold (hlambda0 n) (hlambda1 n)).symm

/-- The canonical radii `n / (n + 1)` give a completely assumption-free
endpoint limit for every residual configuration. -/
theorem tendsto_platformResidualMaterialAbelEndpoint_canonical
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Tendsto
      (fun n ↦ platformAbelEndpointSeriesValue
        (platformResidualMaterialMean C k a hk ha ha2 hthreshold)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) (canonicalAbelParameter n))
      atTop
      (nhds (platformResidualMaterialField
        C k a hk ha ha2 hthreshold Real.pi)) := by
  apply tendsto_platformResidualMaterialAbelEndpoint
    C k a hk ha ha2 hthreshold canonicalAbelParameter_isInteriorApproach
  intro n
  unfold canonicalAbelParameter
  positivity

end

end Erdos1038
