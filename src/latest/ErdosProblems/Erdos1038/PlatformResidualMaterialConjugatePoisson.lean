import ErdosProblems.Erdos1038.PlatformResidualMaterialFourier
import ErdosProblems.Erdos1038.PlatformResidualBlockTangent
import ErdosProblems.Erdos1038.PlatformAdjointAbelHilbert
import ErdosProblems.Erdos1038.PlatformPoissonFourierSeries
import ErdosProblems.Erdos1038.CircleAbelKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conjugate-Poisson representation of the residual material Abel series

This file turns the parity-split second-kind Hilbert series into the
ordinary conjugate Poisson integral of the concrete material field.  It is
the exact kernel representation used in the finite-jump boundary passage.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The real Abel log kernel is half the logarithm of the usual Poisson
denominator. -/
theorem circleAbelLogKernel_eq_half_log_poissonDen
    {rho : ℝ} (hrho : |rho| < 1) (u : ℝ) :
    circleAbelLogKernel rho u =
      (1 / 2 : ℝ) *
        Real.log (1 - 2 * rho * Real.cos u + rho ^ 2) := by
  let z : ℂ := (1 : ℂ) -
    (rho : ℂ) * Complex.exp ((u : ℂ) * Complex.I)
  have hnormExp : ‖Complex.exp ((u : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.exp_mul_I]
    exact Complex.norm_cos_add_sin_mul_I u
  have hzpos : 0 < ‖z‖ := by
    have hreverse := abs_norm_sub_norm_le
      (1 : ℂ) ((rho : ℂ) * Complex.exp ((u : ℂ) * Complex.I))
    have hproduct : ‖(rho : ℂ) * Complex.exp ((u : ℂ) * Complex.I)‖ =
        |rho| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormExp, mul_one]
    have hlower : 1 - |rho| ≤ ‖z‖ := by
      dsimp only [z]
      rw [norm_one, hproduct] at hreverse
      exact (le_abs_self (1 - |rho|)).trans hreverse
    linarith
  have hsquare : ‖z‖ ^ 2 =
      1 - 2 * rho * Real.cos u + rho ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [z]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im,
      zero_mul, sub_zero, zero_sub, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq u]
  unfold circleAbelLogKernel
  change Real.log ‖z‖ = _
  rw [← hsquare, Real.log_pow]
  ring

/-- The conjugate Poisson kernel is twice the angular derivative of the
Abel logarithmic kernel. -/
theorem hasDerivAt_circleAbelLogKernel
    {rho : ℝ} (hrho : |rho| < 1) (u : ℝ) :
    HasDerivAt (circleAbelLogKernel rho)
      (platformConjugatePoissonKernel rho u / 2) u := by
  have hden : 0 < 1 - 2 * rho * Real.cos u + rho ^ 2 := by
    have habsCos := Real.abs_cos_le_one u
    have hrcos : rho * Real.cos u ≤ |rho| := by
      calc
        rho * Real.cos u ≤ |rho * Real.cos u| := le_abs_self _
        _ = |rho| * |Real.cos u| := abs_mul _ _
        _ ≤ |rho| := mul_le_of_le_one_right (abs_nonneg rho) habsCos
    have hsquare : 0 < (1 - |rho|) ^ 2 :=
      sq_pos_of_pos (sub_pos.mpr hrho)
    nlinarith [sq_abs rho]
  have hcos : HasDerivAt (fun x : ℝ ↦
      1 - 2 * rho * Real.cos x + rho ^ 2)
      (2 * rho * Real.sin u) u := by
    convert! ((hasDerivAt_const u (1 : ℝ)).sub
      ((Real.hasDerivAt_cos u).const_mul (2 * rho))).add_const
        (rho ^ 2) using 1
    ring
  have hlog := hcos.log hden.ne'
  convert! hlog.const_mul (1 / 2 : ℝ) using 1
  · ext x
    rw [circleAbelLogKernel_eq_half_log_poissonDen hrho x]
  · unfold platformConjugatePoissonKernel
    ring

/-- The antisymmetric Abel log difference whose `phi` derivative is the
half-circle conjugate-Poisson kernel. -/
def platformHalfCircleAbelLogDifference
    (rho theta phi : ℝ) : ℝ :=
  circleAbelLogKernel rho (theta + phi) -
    circleAbelLogKernel rho (theta - phi)

theorem hasDerivAt_platformHalfCircleAbelLogDifference_phi
    {rho : ℝ} (hrho : |rho| < 1) (theta phi : ℝ) :
    HasDerivAt (platformHalfCircleAbelLogDifference rho theta)
      ((platformConjugatePoissonKernel rho (theta + phi) +
        platformConjugatePoissonKernel rho (theta - phi)) / 2) phi := by
  unfold platformHalfCircleAbelLogDifference
  have hplus := (hasDerivAt_circleAbelLogKernel hrho (theta + phi)).comp
    phi ((hasDerivAt_const phi theta).add (hasDerivAt_id phi))
  have hminus := (hasDerivAt_circleAbelLogKernel hrho (theta - phi)).comp
    phi ((hasDerivAt_const phi theta).sub (hasDerivAt_id phi))
  convert! hplus.sub hminus using 1
  ring

private lemma norm_one_sub_rho_exp_sq
    (rho u : ℝ) :
    ‖(1 : ℂ) - (rho : ℂ) * Complex.exp ((u : ℂ) * Complex.I)‖ ^ 2 =
      (1 - rho) ^ 2 +
        rho * ‖(1 : ℂ) - Complex.exp ((u : ℂ) * Complex.I)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.one_im, zero_mul, sub_zero, zero_sub,
    Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  have htrig := Real.sin_sq_add_cos_sq u
  have htrig' : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    nlinarith
  have hboundary :
      (1 - Real.cos u) * (1 - Real.cos u) +
          -Real.sin u * -Real.sin u = 2 - 2 * Real.cos u := by
    nlinarith
  calc
    (1 - rho * Real.cos u) * (1 - rho * Real.cos u) +
          -(rho * Real.sin u + 0) * -(rho * Real.sin u + 0) =
        1 - 2 * rho * Real.cos u +
          rho ^ 2 * (Real.cos u ^ 2 + Real.sin u ^ 2) := by ring
    _ = 1 - 2 * rho * Real.cos u + rho ^ 2 := by rw [htrig']; ring
    _ = (1 - rho) ^ 2 +
        rho * ((1 - Real.cos u) * (1 - Real.cos u) +
          -Real.sin u * -Real.sin u) := by rw [hboundary]; ring

/-- Uniform logarithmic domination of the real Abel kernel throughout the
final half of the radial approach. -/
theorem abs_circleAbelLogKernel_le_log_two_add_abs_log_sin
    {rho : ℝ} (hrhoLower : (1 / 2 : ℝ) ≤ rho)
    (hrhoUpper : rho ≤ 1) {u : ℝ} (hsin : Real.sin (u / 2) ≠ 0) :
    |circleAbelLogKernel rho u| ≤
      Real.log 2 + |Real.log (|Real.sin (u / 2)|)| := by
  let z : ℂ := Complex.exp ((u : ℂ) * Complex.I)
  let abelNorm : ℝ := ‖(1 : ℂ) - (rho : ℂ) * z‖
  have hrho0 : 0 ≤ rho := by
    exact (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans hrhoLower
  have hboundaryNorm : ‖(1 : ℂ) - z‖ =
      2 * |Real.sin (u / 2)| := by
    dsimp only [z]
    rw [norm_sub_rev]
    have h := Complex.norm_exp_I_mul_ofReal_sub_one u
    calc
      ‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ =
          ‖Complex.exp (Complex.I * (u : ℂ)) - 1‖ := by
        congr 3
        ring
      _ = ‖(2 : ℝ) * Real.sin (u / 2)‖ := h
      _ = 2 * |Real.sin (u / 2)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have habsSinPos : 0 < |Real.sin (u / 2)| := abs_pos.mpr hsin
  have habelPos : 0 < abelNorm := by
    have hidentity := norm_one_sub_rho_exp_sq rho u
    dsimp only [abelNorm, z]
    rw [hboundaryNorm] at hidentity
    have hsquare : 0 < (1 / 2 * (2 * |Real.sin (u / 2)|)) ^ 2 := by
      positivity
    have hsqle :
        (1 / 2 * (2 * |Real.sin (u / 2)|)) ^ 2 ≤
          ‖(1 : ℂ) - (rho : ℂ) *
            Complex.exp ((u : ℂ) * Complex.I)‖ ^ 2 := by
      rw [hidentity]
      nlinarith [sq_nonneg (1 - rho),
        sq_nonneg (2 * |Real.sin (u / 2)|)]
    nlinarith [norm_nonneg ((1 : ℂ) - (rho : ℂ) *
      Complex.exp ((u : ℂ) * Complex.I))]
  have hlowerNorm : |Real.sin (u / 2)| ≤ abelNorm := by
    have hidentity := norm_one_sub_rho_exp_sq rho u
    dsimp only [abelNorm, z]
    rw [hboundaryNorm] at hidentity
    have hsqle : |Real.sin (u / 2)| ^ 2 ≤
        ‖(1 : ℂ) - (rho : ℂ) *
          Complex.exp ((u : ℂ) * Complex.I)‖ ^ 2 := by
      rw [hidentity]
      nlinarith [sq_nonneg (1 - rho),
        sq_nonneg (2 * |Real.sin (u / 2)|)]
    nlinarith [abs_nonneg (Real.sin (u / 2)),
      norm_nonneg ((1 : ℂ) - (rho : ℂ) *
        Complex.exp ((u : ℂ) * Complex.I))]
  have hupperNorm : abelNorm ≤ 2 := by
    have hnormExp : ‖Complex.exp ((u : ℂ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I u
    calc
      abelNorm ≤ ‖(1 : ℂ)‖ + ‖(rho : ℂ) * z‖ := norm_sub_le _ _
      _ = 1 + |rho| * 1 := by
        dsimp only [z]
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          hnormExp]
      _ = 1 + rho := by rw [abs_of_nonneg hrho0, mul_one]
      _ ≤ 2 := by linarith
  have hsinLeOne : |Real.sin (u / 2)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hsinLogNonpos : Real.log |Real.sin (u / 2)| ≤ 0 :=
    Real.log_nonpos habsSinPos.le hsinLeOne
  have hlowerLog : Real.log |Real.sin (u / 2)| ≤
      circleAbelLogKernel rho u := by
    unfold circleAbelLogKernel
    change Real.log |Real.sin (u / 2)| ≤ Real.log abelNorm
    exact Real.strictMonoOn_log.monotoneOn habsSinPos habelPos hlowerNorm
  have hupperLog : circleAbelLogKernel rho u ≤ Real.log 2 := by
    unfold circleAbelLogKernel
    change Real.log abelNorm ≤ Real.log 2
    exact Real.strictMonoOn_log.monotoneOn habelPos (by norm_num) hupperNorm
  rw [abs_le]
  constructor
  · rw [abs_of_nonpos hsinLogNonpos]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · exact hupperLog.trans (le_add_of_nonneg_right (abs_nonneg _))

/-- The smooth material profile used inside one residual block. -/
def platformResidualMaterialSmoothBlock
    (C : ResidualConfiguration ι) (k a : ℝ) (i : ι) (theta : ℝ) : ℝ :=
  platformAngularDensity k a theta *
    (C.location i - platformAngularDistance a theta)

omit [LinearOrder ι] in
theorem contDiff_platformResidualMaterialSmoothBlock
    (C : ResidualConfiguration ι) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : ι) :
    ContDiff ℝ 1 (platformResidualMaterialSmoothBlock C k a i) := by
  have hd : ContDiff ℝ 1 (platformAngularDistance a) := by
    unfold platformAngularDistance platformCenter platformRadius
    fun_prop
  have hdpos (theta : ℝ) : 0 < platformAngularDistance a theta := by
    have hr : 0 ≤ platformRadius a := by
      unfold platformRadius
      linarith
    have hcos := Real.cos_le_one theta
    have hmul : platformRadius a * Real.cos theta ≤ platformRadius a :=
      by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hcos hr
    have hge : a ≤ platformAngularDistance a theta := by
      unfold platformAngularDistance
      linarith [platformCenter_sub_radius a]
    exact ha.trans_le hge
  have hA : ContDiff ℝ 1 (platformAngularDensity k a) := by
    unfold platformAngularDensity platformDensityCoefficient
    exact contDiff_const.sub
      (contDiff_const.div hd fun theta ↦ (hdpos theta).ne')
  unfold platformResidualMaterialSmoothBlock
  exact hA.mul (contDiff_const.sub hd)

omit [LinearOrder ι] in
theorem hasDerivAt_platformResidualMaterialSmoothBlock
    (C : ResidualConfiguration ι) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : ι) (theta : ℝ) :
    HasDerivAt (platformResidualMaterialSmoothBlock C k a i)
      (deriv (platformResidualMaterialSmoothBlock C k a i) theta) theta :=
  ((contDiff_platformResidualMaterialSmoothBlock C k ha ha2 i).differentiable
    (by norm_num)).differentiableAt.hasDerivAt

omit [LinearOrder ι] in
theorem intervalIntegrable_deriv_platformResidualMaterialSmoothBlock
    (C : ResidualConfiguration ι) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : ι) (left right : ℝ) :
    IntervalIntegrable
      (deriv (platformResidualMaterialSmoothBlock C k a i))
      volume left right :=
  ((contDiff_platformResidualMaterialSmoothBlock C k ha ha2 i).continuous_deriv
    (by norm_num)).intervalIntegrable _ _

omit [LinearOrder ι] in
/-- Integration by parts converts one smooth block's conjugate-Poisson
integral into endpoint Abel logs and an ordinary log-kernel integral. -/
theorem integral_platformResidualMaterialSmoothBlock_mul_conjugatePoisson
    (C : ResidualConfiguration ι) (k : ℝ) {a rho : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (hrho : |rho| < 1)
    (i : ι) (theta left right : ℝ) :
    (∫ phi in left..right,
      platformResidualMaterialSmoothBlock C k a i phi *
        ((platformConjugatePoissonKernel rho (theta + phi) +
          platformConjugatePoissonKernel rho (theta - phi)) / 4)) =
      (1 / 2 : ℝ) *
        (platformResidualMaterialSmoothBlock C k a i right *
            platformHalfCircleAbelLogDifference rho theta right -
          platformResidualMaterialSmoothBlock C k a i left *
            platformHalfCircleAbelLogDifference rho theta left -
          ∫ phi in left..right,
            deriv (platformResidualMaterialSmoothBlock C k a i) phi *
              platformHalfCircleAbelLogDifference rho theta phi) := by
  let G := platformResidualMaterialSmoothBlock C k a i
  let G' := deriv G
  let K := platformHalfCircleAbelLogDifference rho theta
  let K' : ℝ → ℝ := fun phi ↦
    (platformConjugatePoissonKernel rho (theta + phi) +
      platformConjugatePoissonKernel rho (theta - phi)) / 2
  have hG (phi : ℝ) : HasDerivAt G (G' phi) phi := by
    dsimp only [G, G']
    exact hasDerivAt_platformResidualMaterialSmoothBlock
      C k ha ha2 i phi
  have hK (phi : ℝ) : HasDerivAt K (K' phi) phi := by
    dsimp only [K, K']
    exact hasDerivAt_platformHalfCircleAbelLogDifference_phi
      hrho theta phi
  have hG'int : IntervalIntegrable G' volume left right :=
    intervalIntegrable_deriv_platformResidualMaterialSmoothBlock
      C k ha ha2 i left right
  have hK'int : IntervalIntegrable K' volume left right := by
    apply Continuous.intervalIntegrable
    dsimp only [K']
    have hden (x : ℝ) : 0 < 1 - 2 * rho * Real.cos x + rho ^ 2 := by
      have habsCos := Real.abs_cos_le_one x
      have hrcos : rho * Real.cos x ≤ |rho| := by
        calc
          rho * Real.cos x ≤ |rho * Real.cos x| := le_abs_self _
          _ = |rho| * |Real.cos x| := abs_mul _ _
          _ ≤ |rho| := mul_le_of_le_one_right (abs_nonneg rho) habsCos
      have hsquare : 0 < (1 - |rho|) ^ 2 :=
        sq_pos_of_pos (sub_pos.mpr hrho)
      nlinarith [sq_abs rho]
    have hQ : Continuous (platformConjugatePoissonKernel rho) := by
      unfold platformConjugatePoissonKernel
      apply Continuous.div
      · fun_prop
      · fun_prop
      · exact fun x ↦ (hden x).ne'
    exact ((hQ.comp (by fun_prop)).add
      (hQ.comp (by fun_prop))).div_const 2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun phi _hphi ↦ hG phi) (fun phi _hphi ↦ hK phi) hG'int hK'int
  dsimp only [G, G', K, K'] at hibp ⊢
  calc
    (∫ phi in left..right,
        platformResidualMaterialSmoothBlock C k a i phi *
          ((platformConjugatePoissonKernel rho (theta + phi) +
            platformConjugatePoissonKernel rho (theta - phi)) / 4)) =
      (1 / 2 : ℝ) *
        ∫ phi in left..right,
          platformResidualMaterialSmoothBlock C k a i phi *
            ((platformConjugatePoissonKernel rho (theta + phi) +
              platformConjugatePoissonKernel rho (theta - phi)) / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro phi _hphi
        ring
    _ = _ := by rw [hibp]

/-- The finite sum of Abel-log boundary terms and smooth derivative
integrals obtained after integrating every material block by parts. -/
def platformResidualMaterialAbelLogRepresentation
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho theta : ℝ) : ℝ :=
  ∑ i, (1 / 2 : ℝ) *
    (platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) *
        platformHalfCircleAbelLogDifference rho theta
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
      platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) *
        platformHalfCircleAbelLogDifference rho theta
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
      ∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleAbelLogDifference rho theta phi)

/-- Exact blockwise Abel-log representation of the concrete conjugate
Poisson integral. -/
theorem integral_platformResidualMaterial_mul_conjugatePoisson_eq_abelLogRepresentation
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∫ phi in 0..Real.pi,
      platformResidualMaterialField C k a hk ha ha2 hthreshold phi *
        ((platformConjugatePoissonKernel rho (theta + phi) +
          platformConjugatePoissonKernel rho (theta - phi)) / 4)) =
      platformResidualMaterialAbelLogRepresentation C k a
        hk ha ha2 hthreshold rho theta := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let kernel : ℝ → ℝ := fun phi ↦
    (platformConjugatePoissonKernel rho (theta + phi) +
      platformConjugatePoissonKernel rho (theta - phi)) / 4
  have hden (x : ℝ) : 0 < 1 - 2 * rho * Real.cos x + rho ^ 2 := by
    have habsCos := Real.abs_cos_le_one x
    have hrcos : rho * Real.cos x ≤ |rho| := by
      calc
        rho * Real.cos x ≤ |rho * Real.cos x| := le_abs_self _
        _ = |rho| * |Real.cos x| := abs_mul _ _
        _ ≤ |rho| := mul_le_of_le_one_right (abs_nonneg rho) habsCos
    have hsquare : 0 < (1 - |rho|) ^ 2 :=
      sq_pos_of_pos (sub_pos.mpr hrho)
    nlinarith [sq_abs rho]
  have hQ : Continuous (platformConjugatePoissonKernel rho) := by
    unfold platformConjugatePoissonKernel
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact fun x ↦ (hden x).ne'
  have hkernel : Continuous kernel := by
    dsimp only [kernel]
    exact ((hQ.comp (by fun_prop)).add
      (hQ.comp (by fun_prop))).div_const 4
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hprod : IntervalIntegrable (fun phi ↦ F phi * kernel phi)
      volume 0 Real.pi := hF.mul_continuousOn hkernel.continuousOn
  have hpartition := sum_intervalIntegral_platformResidualBlocks
    C k a hk ha ha2 hthreshold hprod
  have hblock (i : ι) :
      (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        F phi * kernel phi) =
        ∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          platformResidualMaterialSmoothBlock C k a i phi * kernel phi := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with phi hphi
    rw [uIoc_of_le (platformResidualBlockLeft_lt_right
      C k a hk ha ha2 hthreshold i).le] at hphi
    dsimp only [F]
    rw [platformResidualMaterialField_eq_on_block
      C k a hk ha ha2 hthreshold i hphi]
    rfl
  change (∫ phi in 0..Real.pi, F phi * kernel phi) = _
  rw [← hpartition]
  unfold platformResidualMaterialAbelLogRepresentation
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hblock i]
  exact integral_platformResidualMaterialSmoothBlock_mul_conjugatePoisson
    C k ha ha2 hrho i theta
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)

def platformResidualMaterialConjugatePoissonTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho theta : ℝ) (n : ℕ) (phi : ℝ) : ℝ :=
  platformResidualMaterialField C k a hk ha ha2 hthreshold phi *
    (rho ^ (n + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
      Real.cos (((n + 1 : ℕ) : ℝ) * phi))

private def platformResidualMaterialConjugatePoissonBound
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (rho : ℝ) (n : ℕ) (phi : ℝ) : ℝ :=
  |rho| ^ (n + 1) *
    |platformResidualMaterialField C k a hk ha ha2 hthreshold phi|

private theorem hasSum_integral_platformResidualMaterialConjugatePoissonTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    HasSum
      (fun n ↦ ∫ phi in 0..Real.pi,
        platformResidualMaterialConjugatePoissonTerm
          C k a hk ha ha2 hthreshold rho theta n phi)
      (∫ phi in 0..Real.pi,
        platformResidualMaterialField C k a hk ha ha2 hthreshold phi *
          ((platformConjugatePoissonKernel rho (theta + phi) +
            platformConjugatePoissonKernel rho (theta - phi)) / 4)) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let term := platformResidualMaterialConjugatePoissonTerm
    C k a hk ha ha2 hthreshold rho theta
  let bound := platformResidualMaterialConjugatePoissonBound
    C k a hk ha ha2 hthreshold rho
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  have hFmeas : Measurable F :=
    measurable_platformResidualMaterialField C k a hk ha ha2 hthreshold
  have htermMeas (n : ℕ) : AEStronglyMeasurable (term n)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun phi ↦
      F phi *
        (rho ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
          Real.cos (((n + 1 : ℕ) : ℝ) * phi)))
    exact hFmeas.mul (by fun_prop)
  have hboundPoint (n : ℕ) : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        ‖term n phi‖ ≤ bound n phi := by
    filter_upwards with phi
    intro _hphi
    dsimp only [term, bound,
      platformResidualMaterialConjugatePoissonTerm,
      platformResidualMaterialConjugatePoissonBound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
    have hsine := Real.abs_sin_le_one
      (((n + 1 : ℕ) : ℝ) * theta)
    have hcosine := Real.abs_cos_le_one
      (((n + 1 : ℕ) : ℝ) * phi)
    calc
      |platformResidualMaterialField C k a hk ha ha2 hthreshold phi| *
          (|rho| ^ (n + 1) *
            |Real.sin (((n + 1 : ℕ) : ℝ) * theta)| *
            |Real.cos (((n + 1 : ℕ) : ℝ) * phi)|) ≤
        |platformResidualMaterialField C k a hk ha ha2 hthreshold phi| *
          (|rho| ^ (n + 1) * 1 * 1) := by
        gcongr
      _ = |rho| ^ (n + 1) *
          |platformResidualMaterialField C k a hk ha ha2 hthreshold phi| := by
        ring
  have hgeom : Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg rho) hrho).comp_injective
      Nat.succ_injective
  have hboundSummable : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        Summable (fun n ↦ bound n phi) := by
    filter_upwards with phi
    intro _hphi
    dsimp only [bound, platformResidualMaterialConjugatePoissonBound]
    exact hgeom.mul_right
      |platformResidualMaterialField C k a hk ha ha2 hthreshold phi|
  have hboundTsum : (fun phi ↦ ∑' n, bound n phi) =
      fun phi ↦ (∑' n : ℕ, |rho| ^ (n + 1)) * |F phi| := by
    funext phi
    dsimp only [bound, platformResidualMaterialConjugatePoissonBound, F]
    rw [hgeom.tsum_mul_right]
  have hboundIntegrable : IntervalIntegrable
      (fun phi ↦ ∑' n, bound n phi) volume 0 Real.pi := by
    rw [hboundTsum]
    exact hF.abs.const_mul (∑' n : ℕ, |rho| ^ (n + 1))
  have htermHasSum : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        HasSum (fun n ↦ term n phi)
          (F phi *
            ((platformConjugatePoissonKernel rho (theta + phi) +
              platformConjugatePoissonKernel rho (theta - phi)) / 4)) := by
    filter_upwards with phi
    intro _hphi
    let base : ℕ → ℝ := fun n ↦
      rho ^ (n + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
        Real.cos (((n + 1 : ℕ) : ℝ) * phi)
    have hbase : Summable base := by
      apply Summable.of_norm_bounded hgeom
      intro n
      rw [Real.norm_eq_abs]
      dsimp only [base]
      rw [abs_mul, abs_mul, abs_pow]
      have hsine := Real.abs_sin_le_one
        (((n + 1 : ℕ) : ℝ) * theta)
      have hcosine := Real.abs_cos_le_one
        (((n + 1 : ℕ) : ℝ) * phi)
      calc
        |rho| ^ (n + 1) *
            |Real.sin (((n + 1 : ℕ) : ℝ) * theta)| *
            |Real.cos (((n + 1 : ℕ) : ℝ) * phi)| ≤
          |rho| ^ (n + 1) * 1 * 1 := by gcongr
        _ = |rho| ^ (n + 1) := by ring
    have hbaseTsum : ∑' n, base n =
        (platformConjugatePoissonKernel rho (theta + phi) +
          platformConjugatePoissonKernel rho (theta - phi)) / 4 := by
      dsimp only [base]
      exact tsum_rho_pow_mul_sin_mul_cos hrho theta phi
    have hscaled := hbase.hasSum.mul_left (F phi)
    rw [hbaseTsum] at hscaled
    exact HasSum.congr_fun hscaled (fun _n ↦ rfl)
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    bound htermMeas hboundPoint hboundSummable hboundIntegrable htermHasSum

/-- Exact conjugate-Poisson representation of the concrete positive
frequency sine Abel series. -/
theorem tsum_platformResidualMaterialAbelSineTerm_eq_conjugatePoissonIntegral
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∑' n : ℕ,
      platformAbelSineTerm
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) rho n theta) =
      (1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold phi *
            ((platformConjugatePoissonKernel rho (theta + phi) +
              platformConjugatePoissonKernel rho (theta - phi)) / 4)) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  let coefficient := platformResidualMaterialCosineCoefficient
    C k a hk ha ha2 hthreshold
  have hseries :=
    hasSum_integral_platformResidualMaterialConjugatePoissonTerm
      C k a hk ha ha2 hthreshold hrho theta
  have hseriesScaled := hseries.mul_left (1 / Real.pi)
  have hterm (n : ℕ) :
      (1 / Real.pi) *
          (∫ phi in 0..Real.pi,
            platformResidualMaterialConjugatePoissonTerm
              C k a hk ha ha2 hthreshold rho theta n phi) =
        platformAbelSineTerm coefficient rho n theta := by
    have hintegrand :
        (fun phi ↦ platformResidualMaterialConjugatePoissonTerm
          C k a hk ha ha2 hthreshold rho theta n phi) =
        fun phi ↦
          (rho ^ (n + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * theta)) *
            (F phi * Real.cos (((n + 1 : ℕ) : ℝ) * phi)) := by
      funext phi
      dsimp only [platformResidualMaterialConjugatePoissonTerm, F]
      ring
    rw [hintegrand, intervalIntegral.integral_const_mul]
    dsimp only [coefficient, platformResidualMaterialCosineCoefficient,
      platformAbelSineTerm]
    ring
  exact HasSum.congr_fun hseriesScaled (fun n ↦ (hterm n).symm) |>.tsum_eq

/-- Exact conjugate-Poisson kernel formula for the concrete Abel Hilbert
series, after the harmless `sin theta` factor removes the second-kind
endpoint denominator. -/
theorem platformResidualMaterialAbelHilbertSeries_mul_sin_eq_conjugatePoisson
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    platformAbelHilbertSeries (platformRadius a)
        (platformResidualMaterialCosineCoefficient
          C k a hk ha ha2 hthreshold) rho theta * Real.sin theta =
      -(2 / platformRadius a) * (1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          platformResidualMaterialField C k a hk ha ha2 hthreshold phi *
            ((platformConjugatePoissonKernel rho (theta + phi) +
              platformConjugatePoissonKernel rho (theta - phi)) / 4)) := by
  rw [platformAbelHilbertSeries_mul_sin_eq_tsum_sine hrho
    (platformResidualMaterialCosineCoefficient_bounded
      C k a hk ha ha2 hthreshold)
    (platformRadius a) theta,
    tsum_platformResidualMaterialAbelSineTerm_eq_conjugatePoissonIntegral
      C k a hk ha ha2 hthreshold hrho theta]
  ring

end

end Erdos1038
