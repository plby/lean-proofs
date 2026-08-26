import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryKernel

/-!
# Explicit majorant for the residual material boundary pairing

The endpoint logarithms are controlled by the integrable adjoint boundary
kernels, while every smooth derivative integral contributes only a constant
multiple of the continuous adjoint density.
-/

set_option warningAsError false

open MeasureTheory Set

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- The explicit configuration-dependent, but Abel-parameter-independent,
majorant naturally produced by the blockwise boundary-log representation. -/
def platformResidualMaterialBoundaryPairingMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus theta : ℝ) : ℝ :=
  (1 / (platformRadius a * Real.pi)) *
    ∑ i, (
      |platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
          platformAdjointBoundaryEndpointKernel
            a xMinus xPlus sigmaMinus sigmaPlus
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i) theta +
        |platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
          platformAdjointBoundaryEndpointKernel
            a xMinus xPlus sigmaMinus sigmaPlus
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) theta +
        (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.pi) *
          platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta)

/-- The explicit boundary-pairing majorant is integrable on the complete
half-circle. -/
theorem intervalIntegrable_platformResidualMaterialBoundaryPairingMajorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus) :
    IntervalIntegrable
      (platformResidualMaterialBoundaryPairingMajorant C k a
        hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus)
      volume 0 Real.pi := by
  have hB : IntervalIntegrable
      (platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus)
      volume 0 Real.pi :=
    (continuous_platformAngularAdjointDensity
      hxMinus hxPlus ha2).intervalIntegrable _ _
  have hterm (i : iota) : IntervalIntegrable
      (fun theta : ℝ ↦
        |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
            platformAdjointBoundaryEndpointKernel
              a xMinus xPlus sigmaMinus sigmaPlus
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i)
              theta +
          |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
            platformAdjointBoundaryEndpointKernel
              a xMinus xPlus sigmaMinus sigmaPlus
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
              theta +
          (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
              Real.pi) *
            platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta)
      volume 0 Real.pi := by
    have hright :=
      intervalIntegrable_platformAdjointBoundaryEndpointKernel
        hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
          (platformResidualBlockRight_mem_Icc
            C k a hk ha ha2 hthreshold i)
    have hleft :=
      intervalIntegrable_platformAdjointBoundaryEndpointKernel
        hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
          (platformResidualBlockLeft_mem_Icc
            C k a hk ha ha2 hthreshold i)
    exact ((hright.const_mul
      |platformResidualMaterialSmoothBlock C k a i
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)|).add
      (hleft.const_mul
        |platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)|)).add
      (hB.const_mul
        (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
          Real.pi))
  have hsum : IntervalIntegrable
      (fun theta : ℝ ↦ ∑ i, (
        |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
            platformAdjointBoundaryEndpointKernel
              a xMinus xPlus sigmaMinus sigmaPlus
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i)
              theta +
          |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
            platformAdjointBoundaryEndpointKernel
              a xMinus xPlus sigmaMinus sigmaPlus
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
              theta +
          (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
              Real.pi) *
            platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta))
      volume 0 Real.pi :=
    by
      have ht := IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hterm i)
      convert! ht using 1
      funext theta
      simp only [Finset.sum_apply]
  unfold platformResidualMaterialBoundaryPairingMajorant
  exact hsum.const_mul (1 / (platformRadius a * Real.pi))

private theorem norm_platformResidualMaterialAbelLogRepresentation_canonical_le
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hleftNe : ∀ i, theta ≠
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
    (hrightNe : ∀ i, theta ≠
      platformResidualBlockRight C k a hk ha ha2 hthreshold i)
    {n : ℕ} (hn : 0 < n) :
    ‖platformResidualMaterialAbelLogRepresentation C k a
        hk ha ha2 hthreshold (canonicalAbelParameter n) theta‖ ≤
      (1 / 2 : ℝ) * ∑ i,
        (|platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) +
          |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) +
          platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.pi * Real.sin theta) := by
  classical
  have hrho0 : 0 < canonicalAbelParameter n := by
    unfold canonicalAbelParameter
    positivity
  have hrho1 : canonicalAbelParameter n < 1 := by
    have habs := canonicalAbelParameter_isInteriorApproach.1 n
    rw [abs_of_pos hrho0] at habs
    exact habs
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hterm (i : iota) :
      ‖(1 / 2 : ℝ) *
        (platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
          platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
          ∫ phi in
              platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
              platformResidualBlockRight C k a hk ha ha2 hthreshold i,
            deriv (platformResidualMaterialSmoothBlock C k a i) phi *
              platformHalfCircleAbelLogDifference
                (canonicalAbelParameter n) theta phi)‖ ≤
        (1 / 2 : ℝ) *
          (|platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
              platformHalfCircleBoundaryLogDifference theta
                (platformResidualBlockRight C k a hk ha ha2 hthreshold i) +
            |platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
              platformHalfCircleBoundaryLogDifference theta
                (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) +
            platformResidualMaterialSmoothBlockDerivativeBound C k a i *
              Real.pi * Real.sin theta) := by
    let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
    let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
    let G := platformResidualMaterialSmoothBlock C k a i
    let KA := platformHalfCircleAbelLogDifference
      (canonicalAbelParameter n) theta
    let KB := platformHalfCircleBoundaryLogDifference theta
    let J := ∫ phi in left..right,
      deriv G phi * KA phi
    have hleftMem := platformResidualBlockLeft_mem_Icc
      C k a hk ha ha2 hthreshold i
    have hrightMem := platformResidualBlockRight_mem_Icc
      C k a hk ha ha2 hthreshold i
    have hKAleft :=
      platformHalfCircleAbelLogDifference_nonneg_le_boundary
        hrho0 hrho1 hthetaIcc hleftMem (hleftNe i)
    have hKAright :=
      platformHalfCircleAbelLogDifference_nonneg_le_boundary
        hrho0 hrho1 hthetaIcc hrightMem (hrightNe i)
    have hnormLeft : ‖G left * KA left‖ ≤ |G left| * KB left := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKAleft.1]
      exact mul_le_mul_of_nonneg_left hKAleft.2 (abs_nonneg _)
    have hnormRight : ‖G right * KA right‖ ≤ |G right| * KB right := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKAright.1]
      exact mul_le_mul_of_nonneg_left hKAright.2 (abs_nonneg _)
    have hnormJ : ‖J‖ ≤
        platformResidualMaterialSmoothBlockDerivativeBound C k a i *
          Real.pi * Real.sin theta := by
      dsimp only [J, G, KA, left, right]
      exact norm_integral_deriv_mul_platformHalfCircleAbelLogDifference_le
        C k ha ha2 hrho0 hrho1 i htheta hleftMem.1
          (platformResidualBlockLeft_lt_right
            C k a hk ha ha2 hthreshold i).le hrightMem.2
    have htri : ‖G right * KA right - G left * KA left - J‖ ≤
        |G right| * KB right + |G left| * KB left +
          platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.pi * Real.sin theta := by
      calc
        ‖G right * KA right - G left * KA left - J‖ ≤
            ‖G right * KA right - G left * KA left‖ + ‖J‖ :=
          norm_sub_le _ _
        _ ≤ (‖G right * KA right‖ + ‖G left * KA left‖) + ‖J‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ |G right| * KB right + |G left| * KB left +
            platformResidualMaterialSmoothBlockDerivativeBound C k a i *
              Real.pi * Real.sin theta :=
          add_le_add (add_le_add hnormRight hnormLeft) hnormJ
    dsimp only [G, KA, KB, J, left, right] at htri ⊢
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num :
      (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left htri (by norm_num)
  unfold platformResidualMaterialAbelLogRepresentation
  calc
    ‖∑ i, (1 / 2 : ℝ) *
        (platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
          platformResidualMaterialSmoothBlock C k a i
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) *
            platformHalfCircleAbelLogDifference
              (canonicalAbelParameter n) theta
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
          ∫ phi in
              platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
              platformResidualBlockRight C k a hk ha ha2 hthreshold i,
            deriv (platformResidualMaterialSmoothBlock C k a i) phi *
              platformHalfCircleAbelLogDifference
                (canonicalAbelParameter n) theta phi)‖ ≤
        ∑ i, ‖(1 / 2 : ℝ) *
          (platformResidualMaterialSmoothBlock C k a i
                (platformResidualBlockRight C k a hk ha ha2 hthreshold i) *
              platformHalfCircleAbelLogDifference
                (canonicalAbelParameter n) theta
                (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
            platformResidualMaterialSmoothBlock C k a i
                (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) *
              platformHalfCircleAbelLogDifference
                (canonicalAbelParameter n) theta
                (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
            ∫ phi in
                platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
                platformResidualBlockRight C k a hk ha ha2 hthreshold i,
              deriv (platformResidualMaterialSmoothBlock C k a i) phi *
                platformHalfCircleAbelLogDifference
                  (canonicalAbelParameter n) theta phi)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1 / 2 : ℝ) *
        (|platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) +
          |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) +
          platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.pi * Real.sin theta) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hterm i
    _ = (1 / 2 : ℝ) * ∑ i,
        (|platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockRight C k a hk ha ha2 hthreshold i) +
          |platformResidualMaterialSmoothBlock C k a i
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
            platformHalfCircleBoundaryLogDifference theta
              (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) +
          platformResidualMaterialSmoothBlockDerivativeBound C k a i *
            Real.pi * Real.sin theta) := by
      rw [Finset.mul_sum]

/-- Every canonical Abel-Hilbert pairing integrand is pointwise dominated,
away from the finitely many material jumps, by the explicit integrable
boundary majorant. -/
theorem norm_platformResidualMaterialAbelHilbertPairing_canonical_le_majorant
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hleftNe : ∀ i, theta ≠
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
    (hrightNe : ∀ i, theta ≠
      platformResidualBlockRight C k a hk ha ha2 hthreshold i) :
    ∀ n,
      ‖platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta‖ ≤
        platformResidualMaterialBoundaryPairingMajorant C k a
          hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus theta := by
  classical
  intro n
  let B := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus theta
  let H := platformAbelHilbertSeries (platformRadius a)
    (platformResidualMaterialCosineCoefficient
      C k a hk ha ha2 hthreshold)
    (canonicalAbelParameter n) theta
  let A := platformResidualMaterialAbelLogRepresentation C k a
    hk ha ha2 hthreshold (canonicalAbelParameter n) theta
  let T : iota → ℝ := fun i ↦
    |platformResidualMaterialSmoothBlock C k a i
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
        platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) +
      |platformResidualMaterialSmoothBlock C k a i
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
        platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) +
      platformResidualMaterialSmoothBlockDerivativeBound C k a i *
        Real.pi * Real.sin theta
  let U : iota → ℝ := fun i ↦
    |platformResidualMaterialSmoothBlock C k a i
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)| *
        platformAdjointBoundaryEndpointKernel
          a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) theta +
      |platformResidualMaterialSmoothBlock C k a i
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)| *
        platformAdjointBoundaryEndpointKernel
          a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) theta +
      (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
          Real.pi) * B
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hr : 0 < platformRadius a := platformRadius_pos ha2
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact platformAngularAdjointDensity_nonneg
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hthetaIcc
  have hT0 (i : iota) : 0 ≤ T i := by
    have hleftMem := platformResidualBlockLeft_mem_Icc
      C k a hk ha ha2 hthreshold i
    have hrightMem := platformResidualBlockRight_mem_Icc
      C k a hk ha ha2 hthreshold i
    have hKleft := platformHalfCircleBoundaryLogDifference_nonneg
      hthetaIcc hleftMem (hleftNe i)
    have hKright := platformHalfCircleBoundaryLogDifference_nonneg
      hthetaIcc hrightMem (hrightNe i)
    have hD := platformResidualMaterialSmoothBlockDerivativeBound_nonneg
      C k ha ha2 i
    dsimp only [T]
    positivity
  have hUTerm (i : iota) : U i = (B / Real.sin theta) * T i := by
    dsimp only [U, T, B, platformAdjointBoundaryEndpointKernel]
    field_simp [hsin.ne']
  have hUSum : (∑ i, U i) =
      (B / Real.sin theta) * ∑ i, T i := by
    calc
      (∑ i, U i) = ∑ i, (B / Real.sin theta) * T i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hUTerm i
      _ = (B / Real.sin theta) * ∑ i, T i := by
        rw [Finset.mul_sum]
  have hU0 (i : iota) : 0 ≤ U i := by
    rw [hUTerm]
    exact mul_nonneg (div_nonneg hB0 hsin.le) (hT0 i)
  have hmajorant0 : 0 ≤
      platformResidualMaterialBoundaryPairingMajorant C k a
        hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus theta := by
    unfold platformResidualMaterialBoundaryPairingMajorant
    change 0 ≤ (1 / (platformRadius a * Real.pi)) * ∑ i, U i
    exact mul_nonneg (one_div_nonneg.mpr (mul_nonneg hr.le Real.pi_pos.le))
      (Finset.sum_nonneg fun i _hi ↦ hU0 i)
  have hrho := canonicalAbelParameter_isInteriorApproach.1 n
  have hseriesSin :=
    platformResidualMaterialAbelHilbertSeries_mul_sin_eq_conjugatePoisson
      C k a hk ha ha2 hthreshold hrho theta
  rw [integral_platformResidualMaterial_mul_conjugatePoisson_eq_abelLogRepresentation
    C k a hk ha ha2 hthreshold hrho theta] at hseriesSin
  by_cases hn : n = 0
  · subst n
    have hA0 : platformResidualMaterialAbelLogRepresentation C k a
        hk ha ha2 hthreshold (canonicalAbelParameter 0) theta = 0 := by
      unfold platformResidualMaterialAbelLogRepresentation
        canonicalAbelParameter
      simp only [Nat.cast_zero, zero_add, zero_div,
        platformHalfCircleAbelLogDifference_rho_zero, mul_zero,
        intervalIntegral.integral_zero, sub_zero,
        Finset.sum_const_zero]
    rw [hA0] at hseriesSin
    simp only [mul_zero] at hseriesSin
    have hH0 : platformAbelHilbertSeries (platformRadius a)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold)
        (canonicalAbelParameter 0) theta = 0 :=
      (mul_eq_zero.mp hseriesSin).resolve_right hsin.ne'
    rw [hH0, mul_zero, norm_zero]
    exact hmajorant0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hAbound : ‖A‖ ≤ (1 / 2 : ℝ) * ∑ i, T i := by
      dsimp only [A, T]
      exact norm_platformResidualMaterialAbelLogRepresentation_canonical_le
        C k a hk ha ha2 hthreshold htheta hleftNe hrightNe hnpos
    have hH : H =
        -(2 / (platformRadius a * Real.pi * Real.sin theta)) * A := by
      dsimp only [H, A]
      calc
        platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta =
            (-(2 / platformRadius a) * (1 / Real.pi) *
              platformResidualMaterialAbelLogRepresentation C k a
                hk ha ha2 hthreshold (canonicalAbelParameter n) theta) /
              Real.sin theta :=
          (eq_div_iff hsin.ne').2 hseriesSin
        _ = -(2 / (platformRadius a * Real.pi * Real.sin theta)) *
            platformResidualMaterialAbelLogRepresentation C k a
              hk ha ha2 hthreshold (canonicalAbelParameter n) theta := by
          field_simp [hr.ne', Real.pi_ne_zero, hsin.ne']
    let c : ℝ := 2 /
      (platformRadius a * Real.pi * Real.sin theta)
    have hc : 0 ≤ c := by
      dsimp only [c]
      positivity
    calc
      ‖platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformAbelHilbertSeries (platformRadius a)
            (platformResidualMaterialCosineCoefficient
              C k a hk ha ha2 hthreshold)
            (canonicalAbelParameter n) theta‖ =
          B * (c * ‖A‖) := by
        change ‖B * H‖ = _
        rw [hH, norm_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg hB0, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg hc]
      _ ≤ B * (c * ((1 / 2 : ℝ) * ∑ i, T i)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hAbound hc) hB0
      _ = (1 / (platformRadius a * Real.pi)) * ∑ i, U i := by
        rw [hUSum]
        dsimp only [c]
        field_simp [hr.ne', Real.pi_ne_zero, hsin.ne']
      _ = platformResidualMaterialBoundaryPairingMajorant C k a
          hk ha ha2 hthreshold xMinus xPlus sigmaMinus sigmaPlus theta := by
        unfold platformResidualMaterialBoundaryPairingMajorant
        rfl

end

end Erdos1038
