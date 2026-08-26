import ErdosProblems.Erdos1038.PlatformAdjointFinitePolynomial

/-!
# Spatial form of the finite endpoint-adjoint calculation

This file identifies the Poisson-coordinate exterior coefficients with the
actual spatial crossing integrals on the constant platform.  Together with
`PlatformAdjointFinitePolynomial`, it gives the complete finite-polynomial
case of the endpoint correction in the manuscript's spatial variables.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- Harmonic evaluation of a finite cosine polynomial at a Poisson radius. -/
def finiteEndpointPoissonValue
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (rho f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) : ℝ :=
  f0 +
    2 * ∑ i, evenCoefficient i * rho ^ (2 * (evenMode i + 1)) +
    2 * ∑ i, oddCoefficient i * rho ^ (2 * oddMode i + 1)

private theorem one_div_pi_mul_integral_poisson_cosineTerm
    {rho coefficient : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (n : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta *
            (2 * coefficient * Real.cos ((n : ℝ) * theta))) =
      2 * coefficient * rho ^ n := by
  have hpoint :
      (fun theta : ℝ ↦ platformPoissonKernel rho theta *
        (2 * coefficient * Real.cos ((n : ℝ) * theta))) =
      fun theta ↦ (2 * coefficient) *
        (platformPoissonKernel rho theta *
          Real.cos ((n : ℝ) * theta)) := by
    funext theta
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  calc
    (1 / Real.pi) * ((2 * coefficient) *
          (∫ theta in 0..Real.pi,
            platformPoissonKernel rho theta *
              Real.cos ((n : ℝ) * theta))) =
        2 * coefficient *
          ((1 / Real.pi) * platformPoissonCosMoment rho n) := by
      unfold platformPoissonCosMoment
      ring
    _ = _ := by
      rw [one_div_pi_mul_platformPoissonCosMoment hrho0 hrho1]

/-- Poisson orthogonality for an arbitrary finite cosine polynomial. -/
theorem one_div_pi_mul_integral_platformPoisson_finiteEndpointCosinePolynomial
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta *
            finiteEndpointCosinePolynomial f0 evenMode oddMode
              evenCoefficient oddCoefficient theta) =
      finiteEndpointPoissonValue rho f0 evenMode oddMode
        evenCoefficient oddCoefficient := by
  classical
  let evenIntegrand : ℝ → ℝ :=
    ∑ i, fun theta ↦ platformPoissonKernel rho theta *
      (2 * evenCoefficient i *
        Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta))
  let oddIntegrand : ℝ → ℝ :=
    ∑ i, fun theta ↦ platformPoissonKernel rho theta *
      (2 * oddCoefficient i *
        Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta))
  have hConstant : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rho theta * f0)
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
      continuousOn_const
  have hEvenTerm (i : alpha) : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rho theta *
        (2 * evenCoefficient i *
          Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta)))
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
      (continuous_const.mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).continuousOn
  have hOddTerm (i : beta) : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rho theta *
        (2 * oddCoefficient i *
          Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta)))
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
      (continuous_const.mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).continuousOn
  have hEvenSum : IntervalIntegrable evenIntegrand volume 0 Real.pi := by
    dsimp [evenIntegrand]
    exact IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hEvenTerm i)
  have hOddSum : IntervalIntegrable oddIntegrand volume 0 Real.pi := by
    dsimp [oddIntegrand]
    exact IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hOddTerm i)
  have hEvenIntegral :
      (∫ theta in 0..Real.pi, evenIntegrand theta) =
        ∑ i, ∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta *
            (2 * evenCoefficient i *
              Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta)) := by
    dsimp [evenIntegrand]
    simpa only [Finset.sum_apply] using!
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (fun i _hi ↦ hEvenTerm i)
  have hOddIntegral :
      (∫ theta in 0..Real.pi, oddIntegrand theta) =
        ∑ i, ∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta *
            (2 * oddCoefficient i *
              Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta)) := by
    dsimp [oddIntegrand]
    simpa only [Finset.sum_apply] using!
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (fun i _hi ↦ hOddTerm i)
  have hpoint :
      (fun theta : ℝ ↦ platformPoissonKernel rho theta *
        finiteEndpointCosinePolynomial f0 evenMode oddMode
          evenCoefficient oddCoefficient theta) =
      fun theta ↦
        platformPoissonKernel rho theta * f0 +
          evenIntegrand theta + oddIntegrand theta := by
    funext theta
    unfold finiteEndpointCosinePolynomial evenIntegrand oddIntegrand
    simp only [Finset.sum_apply]
    have heven :
        platformPoissonKernel rho theta *
            (2 * ∑ i, evenCoefficient i *
              Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta)) =
          ∑ i, platformPoissonKernel rho theta *
            (2 * evenCoefficient i *
              Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta)) := by
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    have hodd :
        platformPoissonKernel rho theta *
            (2 * ∑ i, oddCoefficient i *
              Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta)) =
          ∑ i, platformPoissonKernel rho theta *
            (2 * oddCoefficient i *
              Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta)) := by
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [mul_add, mul_add, heven, hodd]
  have hmass := integral_platformPoissonKernel hrho0 hrho1
  have hConstantNorm : (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        platformPoissonKernel rho theta * f0) = f0 := by
    rw [show (fun theta : ℝ ↦ platformPoissonKernel rho theta * f0) =
        fun theta ↦ f0 * platformPoissonKernel rho theta by
        funext theta
        ring,
      intervalIntegral.integral_const_mul, hmass]
    field_simp [Real.pi_ne_zero]
  have hEvenNorm : (1 / Real.pi) *
      (∫ theta in 0..Real.pi, evenIntegrand theta) =
        ∑ i, 2 * evenCoefficient i *
          rho ^ (2 * (evenMode i + 1)) := by
    rw [hEvenIntegral, Finset.mul_sum]
    simp_rw [one_div_pi_mul_integral_poisson_cosineTerm
      hrho0 hrho1]
  have hOddNorm : (1 / Real.pi) *
      (∫ theta in 0..Real.pi, oddIntegrand theta) =
        ∑ i, 2 * oddCoefficient i *
          rho ^ (2 * oddMode i + 1) := by
    rw [hOddIntegral, Finset.mul_sum]
    simp_rw [one_div_pi_mul_integral_poisson_cosineTerm
      hrho0 hrho1]
  calc
    (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            platformPoissonKernel rho theta *
              finiteEndpointCosinePolynomial f0 evenMode oddMode
                evenCoefficient oddCoefficient theta) =
        (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            platformPoissonKernel rho theta * f0 +
              evenIntegrand theta + oddIntegrand theta) := by rw [hpoint]
    _ = (1 / Real.pi) *
          ((∫ theta in 0..Real.pi,
              platformPoissonKernel rho theta * f0) +
            (∫ theta in 0..Real.pi, evenIntegrand theta) +
            ∫ theta in 0..Real.pi, oddIntegrand theta) := by
      rw [intervalIntegral.integral_add (hConstant.add hEvenSum) hOddSum,
        intervalIntegral.integral_add hConstant hEvenSum]
    _ = f0 +
          (∑ i, 2 * evenCoefficient i *
            rho ^ (2 * (evenMode i + 1))) +
          ∑ i, 2 * oddCoefficient i *
            rho ^ (2 * oddMode i + 1) := by
      rw [show (1 / Real.pi) *
          ((∫ theta in 0..Real.pi,
              platformPoissonKernel rho theta * f0) +
            (∫ theta in 0..Real.pi, evenIntegrand theta) +
            ∫ theta in 0..Real.pi, oddIntegrand theta) =
          (1 / Real.pi) *
              (∫ theta in 0..Real.pi,
                platformPoissonKernel rho theta * f0) +
            (1 / Real.pi) *
              (∫ theta in 0..Real.pi, evenIntegrand theta) +
            (1 / Real.pi) *
              (∫ theta in 0..Real.pi, oddIntegrand theta) by ring,
        hConstantNorm, hEvenNorm, hOddNorm]
    _ = finiteEndpointPoissonValue rho f0 evenMode oddMode
          evenCoefficient oddCoefficient := by
      unfold finiteEndpointPoissonValue
      rw [Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc]

/-- The actual exterior first variation written as the two spatial
crossing integrals from the manuscript. -/
def finitePlatformExteriorVariation
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ)
    (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) : ℝ :=
  -sigmaMinus * (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        finiteEndpointCosinePolynomial f0 evenMode oddMode
            evenCoefficient oddCoefficient theta /
          (platformAngularDistance a theta - xMinus)) -
    sigmaPlus * (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        finiteEndpointCosinePolynomial f0 evenMode oddMode
            evenCoefficient oddCoefficient theta /
          (platformAngularDistance a theta - xPlus))

theorem one_div_pi_mul_integral_finiteEndpointCosinePolynomial_div_distance
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {a x : ℝ} (hx : x < a) (ha2 : a < 2)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          finiteEndpointCosinePolynomial f0 evenMode oddMode
              evenCoefficient oddCoefficient theta /
            (platformAngularDistance a theta - x)) =
      (1 / platformCrossingScale a x) *
        finiteEndpointPoissonValue (platformRho a x) f0
          evenMode oddMode evenCoefficient oddCoefficient := by
  have hK : 0 < platformCrossingScale a x :=
    platformCrossingScale_pos hx ha2
  have hIntegral :
      (∫ theta in 0..Real.pi,
        finiteEndpointCosinePolynomial f0 evenMode oddMode
            evenCoefficient oddCoefficient theta /
          (platformAngularDistance a theta - x)) =
        ∫ theta in 0..Real.pi,
          (1 / platformCrossingScale a x) *
            (platformPoissonKernel (platformRho a x) theta *
              finiteEndpointCosinePolynomial f0 evenMode oddMode
                evenCoefficient oddCoefficient theta) := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    have hd : 0 < platformAngularDistance a theta - x := by
      have hdmem := platformAngularDistance_mem_Icc ha2.le htheta
      exact sub_pos.mpr (hx.trans_le hdmem.1)
    have hpoisson := platformCrossingScale_div_distance_eq_poisson
      hx ha2 htheta
    change finiteEndpointCosinePolynomial f0 evenMode oddMode
          evenCoefficient oddCoefficient theta /
        (platformAngularDistance a theta - x) =
      (1 / platformCrossingScale a x) *
        (platformPoissonKernel (platformRho a x) theta *
          finiteEndpointCosinePolynomial f0 evenMode oddMode
            evenCoefficient oddCoefficient theta)
    rw [← hpoisson]
    field_simp [hK.ne', hd.ne']
  rw [hIntegral, intervalIntegral.integral_const_mul]
  have hrho := platformRho_mem_Ioo hx ha2
  have hPoisson :=
    one_div_pi_mul_integral_platformPoisson_finiteEndpointCosinePolynomial
      hrho.1.le hrho.2 f0 evenMode oddMode
        evenCoefficient oddCoefficient
  calc
    (1 / Real.pi) *
          ((1 / platformCrossingScale a x) *
            (∫ theta in 0..Real.pi,
              platformPoissonKernel (platformRho a x) theta *
                finiteEndpointCosinePolynomial f0 evenMode oddMode
                  evenCoefficient oddCoefficient theta)) =
        (1 / platformCrossingScale a x) *
          ((1 / Real.pi) *
            (∫ theta in 0..Real.pi,
              platformPoissonKernel (platformRho a x) theta *
                finiteEndpointCosinePolynomial f0 evenMode oddMode
                  evenCoefficient oddCoefficient theta)) := by ring
    _ = _ := by rw [hPoisson]

theorem endpointExteriorCosCoefficient_eq_crossingScales
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (n : ℕ) :
    endpointExteriorCosCoefficient (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) n =
      -2 *
        (sigmaMinus / platformCrossingScale a xMinus *
            platformRho a xMinus ^ n +
          sigmaPlus / platformCrossingScale a xPlus *
            platformRho a xPlus ^ n) := by
  have hminus := endpointGamma_crossingTerm
    (sigma := sigmaMinus) hxMinus ha2
  have hplus := endpointGamma_crossingTerm
    (sigma := sigmaPlus) hxPlus ha2
  unfold endpointExteriorCosCoefficient
  rw [← hminus, ← hplus, pow_succ]
  ring

private theorem sum_crossing_split
    {gamma : Type*} [Fintype gamma]
    (aMinus aPlus : ℝ) (coefficient : gamma → ℝ)
    (powerMinus powerPlus : gamma → ℝ) :
    (∑ i, coefficient i *
        (-2 * (aMinus * powerMinus i + aPlus * powerPlus i))) =
      -2 * aMinus * ∑ i, coefficient i * powerMinus i +
        -2 * aPlus * ∑ i, coefficient i * powerPlus i := by
  classical
  calc
    (∑ i, coefficient i *
        (-2 * (aMinus * powerMinus i + aPlus * powerPlus i))) =
      ∑ i, ((-2 * aMinus) * (coefficient i * powerMinus i) +
        (-2 * aPlus) * (coefficient i * powerPlus i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The Poisson-coordinate exterior variation is exactly the spatial
crossing-integral variation. -/
theorem finitePlatformExteriorVariation_eq_finiteEndpointExteriorVariation
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    finitePlatformExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 evenMode oddMode
          evenCoefficient oddCoefficient =
      finiteEndpointExteriorVariation (platformRadius a)
        sigmaMinus sigmaPlus (platformRho a xMinus)
          (platformRho a xPlus) f0 evenMode oddMode
            evenCoefficient oddCoefficient := by
  classical
  have hrewrite : finitePlatformExteriorVariation a xMinus xPlus
      sigmaMinus sigmaPlus f0 evenMode oddMode
        evenCoefficient oddCoefficient =
      -sigmaMinus * ((1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            finiteEndpointCosinePolynomial f0 evenMode oddMode
                evenCoefficient oddCoefficient theta /
              (platformAngularDistance a theta - xMinus))) -
        sigmaPlus * ((1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            finiteEndpointCosinePolynomial f0 evenMode oddMode
                evenCoefficient oddCoefficient theta /
              (platformAngularDistance a theta - xPlus))) := by
    unfold finitePlatformExteriorVariation
    ring
  rw [hrewrite,
    one_div_pi_mul_integral_finiteEndpointCosinePolynomial_div_distance
      hxMinus ha2,
    one_div_pi_mul_integral_finiteEndpointCosinePolynomial_div_distance
      hxPlus ha2]
  have hGamma := endpointAdjointGamma_eq_crossingScales
    (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hxMinus hxPlus ha2
  have hEven := sum_crossing_split
    (sigmaMinus / platformCrossingScale a xMinus)
    (sigmaPlus / platformCrossingScale a xPlus)
    evenCoefficient
    (fun i ↦ platformRho a xMinus ^ (2 * (evenMode i + 1)))
    (fun i ↦ platformRho a xPlus ^ (2 * (evenMode i + 1)))
  have hOdd := sum_crossing_split
    (sigmaMinus / platformCrossingScale a xMinus)
    (sigmaPlus / platformCrossingScale a xPlus)
    oddCoefficient
    (fun i ↦ platformRho a xMinus ^ (2 * oddMode i + 1))
    (fun i ↦ platformRho a xPlus ^ (2 * oddMode i + 1))
  unfold finiteEndpointExteriorVariation finiteEndpointPoissonValue
  rw [hGamma]
  simp_rw [endpointExteriorCosCoefficient_eq_crossingScales
    hxMinus hxPlus ha2]
  rw [hEven, hOdd]
  ring

/-- Complete spatial finite-polynomial endpoint correction. -/
theorem finitePlatformExteriorVariation_sub_adjointPairing
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    finitePlatformExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 evenMode oddMode
          evenCoefficient oddCoefficient -
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              (platformRho a xMinus) (platformRho a xPlus) theta *
            finiteEndpointHilbertTransform (platformRadius a)
              evenMode oddMode evenCoefficient oddCoefficient theta) =
      -endpointAdjointGamma (platformRadius a) sigmaMinus sigmaPlus
          (platformRho a xMinus) (platformRho a xPlus) *
        finiteEndpointCosinePolynomial f0 evenMode oddMode
          evenCoefficient oddCoefficient Real.pi := by
  rw [finitePlatformExteriorVariation_eq_finiteEndpointExteriorVariation
    hxMinus hxPlus ha2]
  have hrhoMinus := platformRho_mem_Ioo hxMinus ha2
  have hrhoPlus := platformRho_mem_Ioo hxPlus ha2
  apply finiteEndpointExteriorVariation_sub_adjointPairing
  · exact (platformRadius_pos ha2).ne'
  · have hsquare : platformRho a xMinus ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hrhoMinus.1.le (by norm_num)).2 hrhoMinus.2
    exact (sub_pos.mpr (by simpa using! hsquare)).ne'
  · have hsquare : platformRho a xPlus ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hrhoPlus.1.le (by norm_num)).2 hrhoPlus.2
    exact (sub_pos.mpr (by simpa using! hsquare)).ne'
  · exact hrhoMinus.1.le
  · exact hrhoMinus.2
  · exact hrhoPlus.1.le
  · exact hrhoPlus.2

/-- On the platform interval, the Poisson-coordinate density used in the
finite calculation is the actual angular adjoint density. -/
theorem endpointAdjointAngularDensity_platformRho_eq
    {a xMinus xPlus sigmaMinus sigmaPlus theta : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (htheta : theta ∈ Icc 0 Real.pi) :
    endpointAdjointAngularDensity sigmaMinus sigmaPlus
        (platformRho a xMinus) (platformRho a xPlus) theta =
      platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta := by
  have hrhoMinus := platformRho_mem_Ioo hxMinus ha2
  have hrhoPlus := platformRho_mem_Ioo hxPlus ha2
  rw [platformAngularAdjointDensity_eq_poisson
    hxMinus hxPlus ha2 htheta]
  unfold endpointAdjointAngularDensity endpointAdjointD
  rw [endpointPoissonZero_eq_kernel_zero
      (ne_of_lt hrhoMinus.2) (by linarith [hrhoMinus.1]),
    endpointPoissonZero_eq_kernel_zero
      (ne_of_lt hrhoPlus.2) (by linarith [hrhoPlus.1])]
  ring

/-- Complete finite-polynomial endpoint correction with the actual platform
adjoint density in the pairing integral. -/
theorem finitePlatformExteriorVariation_sub_platformAdjointPairing
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    finitePlatformExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 evenMode oddMode
          evenCoefficient oddCoefficient -
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            finiteEndpointHilbertTransform (platformRadius a)
              evenMode oddMode evenCoefficient oddCoefficient theta) =
      -endpointAdjointGamma (platformRadius a) sigmaMinus sigmaPlus
          (platformRho a xMinus) (platformRho a xPlus) *
        finiteEndpointCosinePolynomial f0 evenMode oddMode
          evenCoefficient oddCoefficient Real.pi := by
  have hIntegral :
      (∫ theta in 0..Real.pi,
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          finiteEndpointHilbertTransform (platformRadius a)
            evenMode oddMode evenCoefficient oddCoefficient theta) =
        ∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity sigmaMinus sigmaPlus
              (platformRho a xMinus) (platformRho a xPlus) theta *
            finiteEndpointHilbertTransform (platformRadius a)
              evenMode oddMode evenCoefficient oddCoefficient theta := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    change platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        finiteEndpointHilbertTransform (platformRadius a)
          evenMode oddMode evenCoefficient oddCoefficient theta =
      endpointAdjointAngularDensity sigmaMinus sigmaPlus
          (platformRho a xMinus) (platformRho a xPlus) theta *
        finiteEndpointHilbertTransform (platformRadius a)
          evenMode oddMode evenCoefficient oddCoefficient theta
    rw [endpointAdjointAngularDensity_platformRho_eq
      hxMinus hxPlus ha2 htheta]
  rw [hIntegral]
  exact finitePlatformExteriorVariation_sub_adjointPairing
    hxMinus hxPlus ha2 f0 evenMode oddMode
      evenCoefficient oddCoefficient

end

end Erdos1038
