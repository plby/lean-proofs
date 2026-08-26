import ErdosProblems.Erdos1038.PlatformResidualMaterialConjugatePoisson
import ErdosProblems.Erdos1038.PlatformAdjointAbelBoundary
import ErdosProblems.Erdos1038.PlatformPoissonMoments

/-!
# Boundary logarithmic kernel for the residual finite-jump passage

This file records the positive half-circle boundary kernel and the monotone
domination of its Abel regularizations.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- The squared chordal denominator at the circle boundary. -/
def platformBoundaryPoissonDenominator (u : ℝ) : ℝ :=
  2 - 2 * Real.cos u

/-- The half-circle boundary logarithmic difference.  At the diagonal its
value is immaterial (Lean's real logarithm assigns `log 0 = 0`). -/
def platformHalfCircleBoundaryLogDifference (theta phi : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.log (platformBoundaryPoissonDenominator (theta + phi)) -
      Real.log (platformBoundaryPoissonDenominator (theta - phi)))

theorem platformHalfCircleBoundaryLogDifference_comm (theta phi : ℝ) :
    platformHalfCircleBoundaryLogDifference theta phi =
      platformHalfCircleBoundaryLogDifference phi theta := by
  have hminus : platformBoundaryPoissonDenominator (theta - phi) =
      platformBoundaryPoissonDenominator (phi - theta) := by
    unfold platformBoundaryPoissonDenominator
    rw [show phi - theta = -(theta - phi) by ring, Real.cos_neg]
  unfold platformHalfCircleBoundaryLogDifference
  rw [add_comm theta phi, hminus]

/-- The finite boundary-log expression obtained after integrating every
smooth residual block by parts. -/
def platformResidualMaterialBoundaryLogRepresentation
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (theta : ℝ) : ℝ :=
  ∑ i, (1 / 2 : ℝ) *
    (platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) *
        platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
      platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) *
        platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
      ∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleBoundaryLogDifference theta phi)

/-- Continuous formula for `B(theta) / sin theta` at the left endpoint. -/
def platformAngularAdjointDensityDivSinLeftExtension
    (a xMinus xPlus sigmaMinus sigmaPlus theta : ℝ) : ℝ :=
  platformRadius a * (Real.sin theta / (1 + Real.cos theta)) *
    (sigmaMinus * platformCrossingScale a xMinus /
        ((a - xMinus) * (platformAngularDistance a theta - xMinus)) +
      sigmaPlus * platformCrossingScale a xPlus /
        ((a - xPlus) * (platformAngularDistance a theta - xPlus)))

/-- The adjoint density has exactly one more half-angle zero than the
Hilbert endpoint denominator at `theta = 0`. -/
theorem platformAngularAdjointDensity_div_sin_eq_leftExtension
    {a xMinus xPlus sigmaMinus sigmaPlus theta : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (ha2 : a < 2) (htheta : theta ∈ Ico 0 Real.pi) :
    platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta / Real.sin theta =
      platformAngularAdjointDensityDivSinLeftExtension
        a xMinus xPlus sigmaMinus sigmaPlus theta := by
  by_cases htheta0 : theta = 0
  · subst theta
    simp [platformAngularAdjointDensity,
      platformAngularAdjointDensityDivSinLeftExtension,
      adjointNumerator_at_left hxMinus hxPlus]
  · have hthetaPos : 0 < theta := lt_of_le_of_ne htheta.1
      (Ne.symm htheta0)
    have hsin : 0 < Real.sin theta :=
      Real.sin_pos_of_pos_of_lt_pi hthetaPos htheta.2
    have hcos : -1 < Real.cos theta := by
      have hanti := Real.strictAntiOn_cos
        ⟨htheta.1, htheta.2.le⟩
        (⟨Real.pi_pos.le, le_rfl⟩ : Real.pi ∈ Icc 0 Real.pi)
        htheta.2
      simpa only [Real.cos_pi] using! hanti
    have hdm : 0 < platformAngularDistance a theta - xMinus := by
      have hd := platformAngularDistance_ge_all ha2.le theta
      linarith
    have hdp : 0 < platformAngularDistance a theta - xPlus := by
      have hd := platformAngularDistance_ge_all ha2.le theta
      linarith
    let d := platformAngularDistance a theta
    let S :=
      sigmaMinus * platformCrossingScale a xMinus /
          ((a - xMinus) * (d - xMinus)) +
        sigmaPlus * platformCrossingScale a xPlus /
          ((a - xPlus) * (d - xPlus))
    have hBfactor :
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta =
          (d - a) * S := by
      dsimp only [d, S]
      unfold platformAngularAdjointDensity adjointNumerator
        adjointNormalization
      field_simp [(sub_pos.mpr hxMinus).ne',
        (sub_pos.mpr hxPlus).ne', hdm.ne', hdp.ne']
      ring
    have hdsub : d - a = platformRadius a *
        (1 - Real.cos theta) := by
      dsimp only [d]
      unfold platformAngularDistance
      linarith [platformCenter_sub_radius a]
    have hhalf : (1 - Real.cos theta) / Real.sin theta =
        Real.sin theta / (1 + Real.cos theta) := by
      field_simp [hsin.ne', (by linarith : 1 + Real.cos theta ≠ 0)]
      nlinarith [Real.sin_sq_add_cos_sq theta]
    rw [hBfactor]
    change ((d - a) * S) / Real.sin theta = _
    unfold platformAngularAdjointDensityDivSinLeftExtension
    change ((d - a) * S) / Real.sin theta =
      platformRadius a * (Real.sin theta / (1 + Real.cos theta)) * S
    rw [hdsub]
    calc
      (platformRadius a * (1 - Real.cos theta) * S) /
          Real.sin theta =
        platformRadius a *
          ((1 - Real.cos theta) / Real.sin theta) * S := by ring
      _ = _ := by rw [hhalf]

lemma platformBoundaryPoissonDenominator_nonneg (u : ℝ) :
    0 ≤ platformBoundaryPoissonDenominator u := by
  unfold platformBoundaryPoissonDenominator
  nlinarith [Real.cos_le_one u]

lemma platformBoundaryPoissonDenominator_sub (theta phi : ℝ) :
    platformBoundaryPoissonDenominator (theta + phi) -
        platformBoundaryPoissonDenominator (theta - phi) =
      4 * Real.sin theta * Real.sin phi := by
  unfold platformBoundaryPoissonDenominator
  rw [Real.cos_add, Real.cos_sub]
  ring

lemma platformBoundaryPoissonDenominator_sub_pos
    {theta phi : ℝ} (htheta : theta ∈ Ioo 0 Real.pi)
    (hphi : phi ∈ Ioo 0 Real.pi) :
    0 < platformBoundaryPoissonDenominator (theta + phi) -
      platformBoundaryPoissonDenominator (theta - phi) := by
  rw [platformBoundaryPoissonDenominator_sub]
  exact mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
    htheta.1 htheta.2)) (Real.sin_pos_of_pos_of_lt_pi hphi.1 hphi.2)

lemma platformBoundaryPoissonDenominator_sub_ne_zero
    {theta phi : ℝ} (htheta : theta ∈ Icc 0 Real.pi)
    (hphi : phi ∈ Icc 0 Real.pi) (hne : theta ≠ phi) :
    platformBoundaryPoissonDenominator (theta - phi) ≠ 0 := by
  have hdiffLower : -Real.pi ≤ theta - phi := by
    linarith [htheta.1, hphi.2]
  have hdiffUpper : theta - phi ≤ Real.pi := by
    linarith [htheta.2, hphi.1]
  intro hzero
  have hcos : Real.cos (theta - phi) = 1 := by
    unfold platformBoundaryPoissonDenominator at hzero
    linarith
  have hdiff : theta - phi = 0 := by
    rw [Real.cos_eq_one_iff_of_lt_of_lt] at hcos
    · exact hcos
    · exact lt_of_lt_of_le (by linarith [Real.pi_pos] :
        -(2 * Real.pi) < -Real.pi) hdiffLower
    · exact lt_of_le_of_lt hdiffUpper
        (by linarith [Real.pi_pos] : Real.pi < 2 * Real.pi)
  exact hne (sub_eq_zero.mp hdiff)

lemma platformBoundaryPoissonDenominator_sub_pos_of_ne
    {theta phi : ℝ} (htheta : theta ∈ Icc 0 Real.pi)
    (hphi : phi ∈ Icc 0 Real.pi) (hne : theta ≠ phi) :
    0 < platformBoundaryPoissonDenominator (theta - phi) :=
  lt_of_le_of_ne (platformBoundaryPoissonDenominator_nonneg _)
    (Ne.symm (platformBoundaryPoissonDenominator_sub_ne_zero
      htheta hphi hne))

lemma abelPoissonDenominator_eq
    (rho u : ℝ) :
    1 - 2 * rho * Real.cos u + rho ^ 2 =
      (1 - rho) ^ 2 + rho * platformBoundaryPoissonDenominator u := by
  unfold platformBoundaryPoissonDenominator
  ring

lemma platformHalfCircleAbelLogDifference_eq_denominator
    {rho : ℝ} (hrho : |rho| < 1) (theta phi : ℝ) :
    platformHalfCircleAbelLogDifference rho theta phi =
      (1 / 2 : ℝ) *
        (Real.log ((1 - rho) ^ 2 +
            rho * platformBoundaryPoissonDenominator (theta + phi)) -
          Real.log ((1 - rho) ^ 2 +
            rho * platformBoundaryPoissonDenominator (theta - phi))) := by
  unfold platformHalfCircleAbelLogDifference
  rw [circleAbelLogKernel_eq_half_log_poissonDen hrho,
    circleAbelLogKernel_eq_half_log_poissonDen hrho,
    abelPoissonDenominator_eq, abelPoissonDenominator_eq]
  ring

lemma platformHalfCircleBoundaryLogDifference_nonneg
    {theta phi : ℝ} (htheta : theta ∈ Icc 0 Real.pi)
    (hphi : phi ∈ Icc 0 Real.pi) (hne : theta ≠ phi) :
    0 ≤ platformHalfCircleBoundaryLogDifference theta phi := by
  have hminus := platformBoundaryPoissonDenominator_sub_pos_of_ne
    htheta hphi hne
  have horder : platformBoundaryPoissonDenominator (theta - phi) ≤
      platformBoundaryPoissonDenominator (theta + phi) := by
    rw [← sub_nonneg]
    rw [platformBoundaryPoissonDenominator_sub]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2))
      (Real.sin_nonneg_of_nonneg_of_le_pi hphi.1 hphi.2)
  unfold platformHalfCircleBoundaryLogDifference
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hminus
      (hminus.trans_le horder) horder))

/-- On the positive radial approach the regularized half-circle kernel is
nonnegative and is pointwise bounded by its boundary value. -/
theorem platformHalfCircleAbelLogDifference_nonneg_le_boundary
    {rho theta phi : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (htheta : theta ∈ Icc 0 Real.pi) (hphi : phi ∈ Icc 0 Real.pi)
    (hne : theta ≠ phi) :
    0 ≤ platformHalfCircleAbelLogDifference rho theta phi ∧
      platformHalfCircleAbelLogDifference rho theta phi ≤
        platformHalfCircleBoundaryLogDifference theta phi := by
  let A := platformBoundaryPoissonDenominator (theta + phi)
  let B := platformBoundaryPoissonDenominator (theta - phi)
  let c := (1 - rho) ^ 2
  let X := c + rho * A
  let Y := c + rho * B
  have hrhoAbs : |rho| < 1 := by
    rw [abs_of_pos hrho0]
    exact hrho1
  have hB : 0 < B := by
    dsimp only [B]
    exact platformBoundaryPoissonDenominator_sub_pos_of_ne
      htheta hphi hne
  have hAB : B ≤ A := by
    dsimp only [A, B]
    rw [← sub_nonneg]
    rw [platformBoundaryPoissonDenominator_sub]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2))
      (Real.sin_nonneg_of_nonneg_of_le_pi hphi.1 hphi.2)
  have hA : 0 < A := hB.trans_le hAB
  have hc : 0 < c := by
    dsimp only [c]
    exact sq_pos_of_pos (sub_pos.mpr hrho1)
  have hY : 0 < Y := by
    dsimp only [Y]
    exact add_pos_of_pos_of_nonneg hc (mul_nonneg hrho0.le hB.le)
  have hXY : Y ≤ X := by
    dsimp only [X, Y]
    linarith [mul_le_mul_of_nonneg_left hAB hrho0.le]
  have hX : 0 < X := hY.trans_le hXY
  have hratio : X / Y ≤ A / B := by
    rw [div_le_div_iff₀ hY hB]
    dsimp only [X, Y]
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hAB)]
  have hlogXY : Real.log Y ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn hY hX hXY
  have hlogRatio : Real.log (X / Y) ≤ Real.log (A / B) := by
    exact Real.strictMonoOn_log.monotoneOn (div_pos hX hY)
      (div_pos hA hB) hratio
  rw [platformHalfCircleAbelLogDifference_eq_denominator hrhoAbs]
  change 0 ≤ (1 / 2 : ℝ) * (Real.log X - Real.log Y) ∧
    (1 / 2 : ℝ) * (Real.log X - Real.log Y) ≤
      (1 / 2 : ℝ) * (Real.log A - Real.log B)
  constructor
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hlogXY)
  · rw [← Real.log_div hX.ne' hY.ne',
      ← Real.log_div hA.ne' hB.ne']
    exact mul_le_mul_of_nonneg_left hlogRatio (by norm_num)

/-- Away from the diagonal the canonical Abel logarithmic difference tends
to the explicit boundary kernel. -/
theorem tendsto_platformHalfCircleAbelLogDifference_canonical
    {theta phi : ℝ} (htheta : theta ∈ Icc 0 Real.pi)
    (hphi : phi ∈ Icc 0 Real.pi) (hne : theta ≠ phi) :
    Tendsto
      (fun n ↦ platformHalfCircleAbelLogDifference
        (canonicalAbelParameter n) theta phi)
      atTop (nhds (platformHalfCircleBoundaryLogDifference theta phi)) := by
  let A := platformBoundaryPoissonDenominator (theta + phi)
  let B := platformBoundaryPoissonDenominator (theta - phi)
  let X : ℝ → ℝ := fun rho ↦ (1 - rho) ^ 2 + rho * A
  let Y : ℝ → ℝ := fun rho ↦ (1 - rho) ^ 2 + rho * B
  let K : ℝ → ℝ := fun rho ↦ (1 / 2 : ℝ) *
    (Real.log (X rho) - Real.log (Y rho))
  have hB : 0 < B := by
    dsimp only [B]
    exact platformBoundaryPoissonDenominator_sub_pos_of_ne
      htheta hphi hne
  have hAB : B ≤ A := by
    dsimp only [A, B]
    rw [← sub_nonneg, platformBoundaryPoissonDenominator_sub]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2))
      (Real.sin_nonneg_of_nonneg_of_le_pi hphi.1 hphi.2)
  have hA : 0 < A := hB.trans_le hAB
  have hXcont : ContinuousAt X 1 := by
    dsimp only [X]
    fun_prop
  have hYcont : ContinuousAt Y 1 := by
    dsimp only [Y]
    fun_prop
  have hXone : X 1 = A := by simp [X]
  have hYone : Y 1 = B := by simp [Y]
  have hKcont : ContinuousAt K 1 := by
    dsimp only [K]
    exact ((hXcont.log (by simpa only [hXone] using! hA.ne')).sub
      (hYcont.log (by simpa only [hYone] using! hB.ne'))).const_mul (1 / 2)
  have hlimit : Tendsto (fun n ↦ K (canonicalAbelParameter n))
      atTop (nhds (K 1)) :=
    hKcont.tendsto.comp canonicalAbelParameter_isInteriorApproach.2
  have hboundary : K 1 =
      platformHalfCircleBoundaryLogDifference theta phi := by
    simp only [K, hXone, hYone]
    rfl
  rw [hboundary] at hlimit
  apply hlimit.congr'
  filter_upwards with n
  rw [platformHalfCircleAbelLogDifference_eq_denominator
    (canonicalAbelParameter_isInteriorApproach.1 n)]

omit [LinearOrder iota] in
/-- The derivative of a smooth material block has the endpoint-cancelling
factor `sin theta` explicitly. -/
theorem deriv_platformResidualMaterialSmoothBlock_eq_sin_mul
    (C : ResidualConfiguration iota) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : iota) (theta : ℝ) :
    deriv (platformResidualMaterialSmoothBlock C k a i) theta =
      platformRadius a * Real.sin theta *
        (k * Real.sqrt (2 * a) * C.location i /
            platformAngularDistance a theta ^ 2 - (k + 1)) := by
  have hr : 0 ≤ platformRadius a := (platformRadius_pos ha2).le
  have hdpos : 0 < platformAngularDistance a theta := by
    have hcos := Real.cos_le_one theta
    have hmul : platformRadius a * Real.cos theta ≤ platformRadius a :=
      by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hcos hr
    have hge : a ≤ platformAngularDistance a theta := by
      unfold platformAngularDistance
      linarith [platformCenter_sub_radius a]
    exact ha.trans_le hge
  have hd : HasDerivAt (platformAngularDistance a)
      (platformRadius a * Real.sin theta) theta := by
    unfold platformAngularDistance
    convert! (hasDerivAt_const theta (platformCenter a)).sub
      ((Real.hasDerivAt_cos theta).const_mul (platformRadius a)) using 1
    ring
  have hA : HasDerivAt (platformAngularDensity k a)
      (k * Real.sqrt (2 * a) *
          (platformRadius a * Real.sin theta) /
            platformAngularDistance a theta ^ 2) theta := by
    unfold platformAngularDensity platformDensityCoefficient
    convert! (hasDerivAt_const theta (k + 1)).sub
      ((hasDerivAt_const theta (k * Real.sqrt (2 * a))).div hd
        hdpos.ne') using 1
    ring
  have hvelocity : HasDerivAt
      (fun x : ℝ ↦ C.location i - platformAngularDistance a x)
      (-(platformRadius a * Real.sin theta)) theta := by
    convert! (hasDerivAt_const theta (C.location i)).sub hd using 1
    ring
  have hproduct := hA.mul hvelocity
  have hproductDeriv :
      deriv (platformResidualMaterialSmoothBlock C k a i) theta =
        k * Real.sqrt (2 * a) *
            (platformRadius a * Real.sin theta) /
              platformAngularDistance a theta ^ 2 *
            (C.location i - platformAngularDistance a theta) +
          platformAngularDensity k a theta *
            (-(platformRadius a * Real.sin theta)) := by
    exact hproduct.deriv
  rw [hproductDeriv]
  unfold platformAngularDensity platformDensityCoefficient
  field_simp [hdpos.ne']
  ring

/-- An explicit constant controlling the smooth-block derivative after its
`sin theta` factor is removed. -/
def platformResidualMaterialSmoothBlockDerivativeBound
    (C : ResidualConfiguration iota) (k a : ℝ) (i : iota) : ℝ :=
  platformRadius a *
    (|k * Real.sqrt (2 * a) * C.location i| / a ^ 2 + |k + 1|)

omit [LinearOrder iota] in
theorem platformResidualMaterialSmoothBlockDerivativeBound_nonneg
    (C : ResidualConfiguration iota) (k : ℝ) {a : ℝ}
    (_ha : 0 < a) (ha2 : a < 2) (i : iota) :
    0 ≤ platformResidualMaterialSmoothBlockDerivativeBound C k a i := by
  unfold platformResidualMaterialSmoothBlockDerivativeBound
  exact mul_nonneg (platformRadius_pos ha2).le
    (add_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _)) (abs_nonneg _))

omit [LinearOrder iota] in
/-- Uniform endpoint-cancelling derivative bound on the platform angle. -/
theorem abs_deriv_platformResidualMaterialSmoothBlock_le_sin
    (C : ResidualConfiguration iota) (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : iota) {theta : ℝ}
    (htheta : theta ∈ Icc 0 Real.pi) :
    |deriv (platformResidualMaterialSmoothBlock C k a i) theta| ≤
      platformResidualMaterialSmoothBlockDerivativeBound C k a i *
        Real.sin theta := by
  let d := platformAngularDistance a theta
  let q := k * Real.sqrt (2 * a) * C.location i
  have hd : a ≤ d := by
    dsimp only [d]
    exact (platformAngularDistance_mem_Icc ha2.le htheta).1
  have hdpos : 0 < d := ha.trans_le hd
  have hdsq : a ^ 2 ≤ d ^ 2 := by nlinarith
  have hquot : |q / d ^ 2| ≤ |q| / a ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg d)]
    exact div_le_div_of_nonneg_left (abs_nonneg q) (sq_pos_of_pos ha) hdsq
  have hfactor : |q / d ^ 2 - (k + 1)| ≤
      |q| / a ^ 2 + |k + 1| :=
    (abs_sub _ _).trans (add_le_add hquot le_rfl)
  rw [deriv_platformResidualMaterialSmoothBlock_eq_sin_mul
    C k ha ha2 i theta]
  rw [abs_mul, abs_mul, abs_of_nonneg (platformRadius_pos ha2).le,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      htheta.1 htheta.2)]
  dsimp only [q, d] at hfactor
  unfold platformResidualMaterialSmoothBlockDerivativeBound
  nlinarith [mul_nonneg (platformRadius_pos ha2).le
    (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2),
    mul_le_mul_of_nonneg_left hfactor (platformRadius_pos ha2).le,
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor (platformRadius_pos ha2).le)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2)]

private lemma integral_cos_succ_mul_mul_cos_zero_pi (n : ℕ) :
    (∫ phi in 0..Real.pi,
      Real.cos (((n + 1 : ℕ) : ℝ) * phi) * Real.cos phi) =
      if n = 0 then Real.pi / 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    calc
      (∫ phi in 0..Real.pi,
          Real.cos ((((0 + 1 : ℕ) : ℝ)) * phi) * Real.cos phi) =
          ∫ phi in 0..Real.pi, Real.cos phi ^ 2 := by
            apply intervalIntegral.integral_congr
            intro phi _hphi
            norm_num
            ring
      _ = Real.pi / 2 := by simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hn2pos : 0 < n + 2 := by omega
    have hpoint (phi : ℝ) :
        Real.cos ((((n + 1 : ℕ) : ℝ)) * phi) * Real.cos phi =
          (Real.cos (((n + 2 : ℕ) : ℝ) * phi) +
            Real.cos ((n : ℝ) * phi)) / 2 := by
      have htrig := Real.two_mul_cos_mul_cos
        ((((n + 1 : ℕ) : ℝ)) * phi) phi
      rw [show ((((n + 1 : ℕ) : ℝ)) * phi + phi) =
          ((n + 2 : ℕ) : ℝ) * phi by push_cast; ring,
        show ((((n + 1 : ℕ) : ℝ)) * phi - phi) =
          (n : ℝ) * phi by push_cast; ring] at htrig
      linarith
    calc
      (∫ phi in 0..Real.pi,
          Real.cos (((n + 1 : ℕ) : ℝ) * phi) * Real.cos phi) =
          ∫ phi in 0..Real.pi,
            (Real.cos (((n + 2 : ℕ) : ℝ) * phi) +
              Real.cos ((n : ℝ) * phi)) / 2 := by
            apply intervalIntegral.integral_congr
            intro phi _hphi
            exact hpoint phi
      _ = (1 / 2 : ℝ) *
          ((∫ phi in 0..Real.pi,
              Real.cos (((n + 2 : ℕ) : ℝ) * phi)) +
            ∫ phi in 0..Real.pi,
              Real.cos ((n : ℝ) * phi)) := by
            rw [show (fun phi : ℝ ↦
                (Real.cos (((n + 2 : ℕ) : ℝ) * phi) +
                  Real.cos ((n : ℝ) * phi)) / 2) =
              fun phi ↦ (1 / 2 : ℝ) *
                (Real.cos (((n + 2 : ℕ) : ℝ) * phi) +
                  Real.cos ((n : ℝ) * phi)) by funext phi; ring,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add
                (intervalIntegrable_cos_nat_mul (n + 2))
                (intervalIntegrable_cos_nat_mul n)]
      _ = 0 := by
        rw [integral_cos_nat_mul_zero_pi hn2pos,
          integral_cos_nat_mul_zero_pi hnpos]
        ring
      _ = if n = 0 then Real.pi / 2 else 0 := by simp [hn]

/-- The first cosine moment of the half-circle conjugate-Poisson kernel. -/
theorem integral_cos_mul_halfCircleConjugatePoisson
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∫ phi in 0..Real.pi,
      Real.cos phi *
        ((platformConjugatePoissonKernel rho (theta + phi) +
          platformConjugatePoissonKernel rho (theta - phi)) / 4)) =
      Real.pi / 2 * rho * Real.sin theta := by
  let term : ℕ → ℝ → ℝ := fun n phi ↦
    rho ^ (n + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
      Real.cos (((n + 1 : ℕ) : ℝ) * phi) * Real.cos phi
  let bound : ℕ → ℝ → ℝ := fun n _phi ↦ |rho| ^ (n + 1)
  have hgeom : Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg rho) hrho).comp_injective
      Nat.succ_injective
  have hmeas (n : ℕ) : AEStronglyMeasurable (term n)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [term]
    fun_prop
  have hbound (n : ℕ) : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi → ‖term n phi‖ ≤ bound n phi := by
    filter_upwards with phi
    intro _hphi
    dsimp only [term, bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
    calc
      |rho| ^ (n + 1) *
          |Real.sin (((n + 1 : ℕ) : ℝ) * theta)| *
          |Real.cos (((n + 1 : ℕ) : ℝ) * phi)| *
          |Real.cos phi| ≤
        |rho| ^ (n + 1) * 1 * 1 * 1 := by
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = |rho| ^ (n + 1) := by ring
  have hboundSummable : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        Summable (fun n ↦ bound n phi) := by
    filter_upwards with phi
    intro _hphi
    simpa only [bound] using! hgeom
  have hboundIntegrable : IntervalIntegrable
      (fun phi ↦ ∑' n, bound n phi) volume 0 Real.pi := by
    have heq : (fun phi ↦ ∑' n, bound n phi) =
        fun _phi : ℝ ↦ ∑' n : ℕ, |rho| ^ (n + 1) := by
      funext phi
      rfl
    rw [heq]
    exact intervalIntegrable_const
  have hlimit : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        HasSum (fun n ↦ term n phi)
          (Real.cos phi *
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
      calc
        |rho| ^ (n + 1) *
            |Real.sin (((n + 1 : ℕ) : ℝ) * theta)| *
            |Real.cos (((n + 1 : ℕ) : ℝ) * phi)| ≤
          |rho| ^ (n + 1) * 1 * 1 := by
            gcongr
            · exact Real.abs_sin_le_one _
            · exact Real.abs_cos_le_one _
        _ = |rho| ^ (n + 1) := by ring
    have hsum := hbase.hasSum.mul_left (Real.cos phi)
    rw [tsum_rho_pow_mul_sin_mul_cos hrho theta phi] at hsum
    apply HasSum.congr_fun hsum
    intro n
    dsimp only [base, term]
    ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    bound hmeas hbound hboundSummable hboundIntegrable hlimit
  have htermIntegral (n : ℕ) :
      (∫ phi in 0..Real.pi, term n phi) =
        if n = 0 then
          rho * Real.sin theta * (Real.pi / 2)
        else 0 := by
    dsimp only [term]
    rw [show (fun phi : ℝ ↦
        rho ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
          Real.cos (((n + 1 : ℕ) : ℝ) * phi) * Real.cos phi) =
      fun phi ↦
        (rho ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * theta)) *
          (Real.cos (((n + 1 : ℕ) : ℝ) * phi) * Real.cos phi) by
            funext phi; ring,
      intervalIntegral.integral_const_mul,
      integral_cos_succ_mul_mul_cos_zero_pi]
    by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]
  have hsparse : HasSum
      (fun n : ℕ ↦ if n = 0 then
        rho * Real.sin theta * (Real.pi / 2) else 0)
      (∫ phi in 0..Real.pi,
        Real.cos phi *
          ((platformConjugatePoissonKernel rho (theta + phi) +
            platformConjugatePoissonKernel rho (theta - phi)) / 4)) :=
    HasSum.congr_fun hsum fun n ↦ (htermIntegral n).symm
  have hone : HasSum
      (fun n : ℕ ↦ if n = 0 then
        rho * Real.sin theta * (Real.pi / 2) else 0)
      (rho * Real.sin theta * (Real.pi / 2)) :=
    hasSum_ite_eq 0 _
  have heq := hsparse.unique hone
  linarith

@[simp] lemma platformHalfCircleAbelLogDifference_zero
    (rho theta : ℝ) :
    platformHalfCircleAbelLogDifference rho theta 0 = 0 := by
  unfold platformHalfCircleAbelLogDifference
  ring_nf

lemma platformHalfCircleAbelLogDifference_pi
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    platformHalfCircleAbelLogDifference rho theta Real.pi = 0 := by
  unfold platformHalfCircleAbelLogDifference
  rw [circleAbelLogKernel_eq_half_log_poissonDen hrho,
    circleAbelLogKernel_eq_half_log_poissonDen hrho]
  have hcos : Real.cos (theta + Real.pi) =
      Real.cos (theta - Real.pi) := by
    rw [Real.cos_add, Real.cos_sub]
    simp
  rw [hcos]
  ring

@[simp] lemma platformHalfCircleBoundaryLogDifference_pi_left (t : ℝ) :
    platformHalfCircleBoundaryLogDifference Real.pi t = 0 := by
  unfold platformHalfCircleBoundaryLogDifference
    platformBoundaryPoissonDenominator
  have hcos : Real.cos (Real.pi + t) =
      Real.cos (Real.pi - t) := by
    rw [Real.cos_add, Real.cos_sub]
    simp
  rw [hcos]
  ring

/-- The Abel half-circle log kernel has exact sine mass. -/
theorem integral_sin_mul_platformHalfCircleAbelLogDifference
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∫ phi in 0..Real.pi,
      Real.sin phi * platformHalfCircleAbelLogDifference rho theta phi) =
      Real.pi * rho * Real.sin theta := by
  let G : ℝ → ℝ := fun phi ↦ -Real.cos phi
  let G' : ℝ → ℝ := Real.sin
  let K := platformHalfCircleAbelLogDifference rho theta
  let K' : ℝ → ℝ := fun phi ↦
    (platformConjugatePoissonKernel rho (theta + phi) +
      platformConjugatePoissonKernel rho (theta - phi)) / 2
  have hG (phi : ℝ) : HasDerivAt G (G' phi) phi := by
    dsimp only [G, G']
    convert! (Real.hasDerivAt_cos phi).neg using 1
    ring
  have hK (phi : ℝ) : HasDerivAt K (K' phi) phi := by
    dsimp only [K, K']
    exact hasDerivAt_platformHalfCircleAbelLogDifference_phi hrho theta phi
  have hG'int : IntervalIntegrable G' volume 0 Real.pi := by
    dsimp only [G']
    exact Real.continuous_sin.intervalIntegrable _ _
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
  have hK'int : IntervalIntegrable K' volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp only [K']
    exact ((hQ.comp (by fun_prop)).add
      (hQ.comp (by fun_prop))).div_const 2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun phi _hphi ↦ hG phi) (fun phi _hphi ↦ hK phi)
      hG'int hK'int
  have hmoment := integral_cos_mul_halfCircleConjugatePoisson hrho theta
  have hKprimeIntegral :
      (∫ phi in 0..Real.pi, Real.cos phi * K' phi) =
        Real.pi * rho * Real.sin theta := by
    dsimp only [K']
    calc
      (∫ phi in 0..Real.pi,
          Real.cos phi *
            ((platformConjugatePoissonKernel rho (theta + phi) +
              platformConjugatePoissonKernel rho (theta - phi)) / 2)) =
          2 * ∫ phi in 0..Real.pi,
            Real.cos phi *
              ((platformConjugatePoissonKernel rho (theta + phi) +
                platformConjugatePoissonKernel rho (theta - phi)) / 4) := by
            rw [show (fun phi : ℝ ↦
                Real.cos phi *
                  ((platformConjugatePoissonKernel rho (theta + phi) +
                    platformConjugatePoissonKernel rho (theta - phi)) / 2)) =
              fun phi ↦ 2 *
                (Real.cos phi *
                  ((platformConjugatePoissonKernel rho (theta + phi) +
                    platformConjugatePoissonKernel rho (theta - phi)) / 4)) by
                  funext phi; ring,
              intervalIntegral.integral_const_mul]
      _ = Real.pi * rho * Real.sin theta := by rw [hmoment]; ring
  dsimp only [G, G', K, K'] at hibp
  rw [platformHalfCircleAbelLogDifference_zero,
    platformHalfCircleAbelLogDifference_pi hrho] at hibp
  simp only [Real.cos_pi, neg_neg, Real.cos_zero, neg_one_mul,
    one_mul, zero_sub] at hibp
  have hleft :
      (∫ x in 0..Real.pi,
        -Real.cos x *
          ((platformConjugatePoissonKernel rho (theta + x) +
            platformConjugatePoissonKernel rho (theta - x)) / 2)) =
        -∫ x in 0..Real.pi,
          Real.cos x *
            ((platformConjugatePoissonKernel rho (theta + x) +
              platformConjugatePoissonKernel rho (theta - x)) / 2) := by
    rw [show (fun x : ℝ ↦
        -Real.cos x *
          ((platformConjugatePoissonKernel rho (theta + x) +
            platformConjugatePoissonKernel rho (theta - x)) / 2)) =
      fun x ↦ -(Real.cos x *
        ((platformConjugatePoissonKernel rho (theta + x) +
          platformConjugatePoissonKernel rho (theta - x)) / 2)) by
            funext x; ring,
      intervalIntegral.integral_neg]
  rw [hleft] at hibp
  rw [← hKprimeIntegral]
  linarith

private lemma intervalIntegrable_log_platformBoundaryPoissonDenominator_add
    (theta left right : ℝ) :
    IntervalIntegrable
      (fun phi : ℝ ↦ Real.log
        (platformBoundaryPoissonDenominator (theta + phi)))
      volume left right := by
  have han : AnalyticOnNhd ℝ
      (fun phi : ℝ ↦
        platformBoundaryPoissonDenominator (theta + phi)) Set.univ :=
    fun _ _ ↦ by
      unfold platformBoundaryPoissonDenominator
      fun_prop
  have hmer : MeromorphicOn
      (fun phi : ℝ ↦
        platformBoundaryPoissonDenominator (theta + phi))
      (Set.uIcc left right) :=
    fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
  have hlog := MeromorphicOn.intervalIntegrable_log_norm hmer
  apply hlog.congr
  intro phi _hphi
  change Real.log ‖platformBoundaryPoissonDenominator (theta + phi)‖ =
    Real.log (platformBoundaryPoissonDenominator (theta + phi))
  rw [Real.norm_eq_abs,
    abs_of_nonneg (platformBoundaryPoissonDenominator_nonneg _)]

private lemma intervalIntegrable_log_platformBoundaryPoissonDenominator_sub
    (theta left right : ℝ) :
    IntervalIntegrable
      (fun phi : ℝ ↦ Real.log
        (platformBoundaryPoissonDenominator (theta - phi)))
      volume left right := by
  have han : AnalyticOnNhd ℝ
      (fun phi : ℝ ↦
        platformBoundaryPoissonDenominator (theta - phi)) Set.univ :=
    fun _ _ ↦ by
      unfold platformBoundaryPoissonDenominator
      fun_prop
  have hmer : MeromorphicOn
      (fun phi : ℝ ↦
        platformBoundaryPoissonDenominator (theta - phi))
      (Set.uIcc left right) :=
    fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
  have hlog := MeromorphicOn.intervalIntegrable_log_norm hmer
  apply hlog.congr
  intro phi _hphi
  change Real.log ‖platformBoundaryPoissonDenominator (theta - phi)‖ =
    Real.log (platformBoundaryPoissonDenominator (theta - phi))
  rw [Real.norm_eq_abs,
    abs_of_nonneg (platformBoundaryPoissonDenominator_nonneg _)]

/-- The boundary half-circle kernel is integrable on every bounded interval,
including when its diagonal logarithmic pole lies inside. -/
theorem intervalIntegrable_platformHalfCircleBoundaryLogDifference
    (theta left right : ℝ) :
    IntervalIntegrable
      (platformHalfCircleBoundaryLogDifference theta)
      volume left right := by
  unfold platformHalfCircleBoundaryLogDifference
  exact ((intervalIntegrable_log_platformBoundaryPoissonDenominator_add
      theta left right).sub
    (intervalIntegrable_log_platformBoundaryPoissonDenominator_sub
      theta left right)).const_mul (1 / 2)

theorem intervalIntegrable_sin_mul_platformHalfCircleBoundaryLogDifference
    (theta left right : ℝ) :
    IntervalIntegrable
      (fun phi ↦ Real.sin phi *
        platformHalfCircleBoundaryLogDifference theta phi)
      volume left right :=
  (intervalIntegrable_platformHalfCircleBoundaryLogDifference
    theta left right).continuousOn_mul Real.continuous_sin.continuousOn

theorem continuous_platformHalfCircleAbelLogDifference
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    Continuous (platformHalfCircleAbelLogDifference rho theta) := by
  rw [continuous_iff_continuousAt]
  intro phi
  exact (hasDerivAt_platformHalfCircleAbelLogDifference_phi
    hrho theta phi).continuousAt

@[simp] lemma platformHalfCircleAbelLogDifference_rho_zero
    (theta phi : ℝ) :
    platformHalfCircleAbelLogDifference 0 theta phi = 0 := by
  unfold platformHalfCircleAbelLogDifference circleAbelLogKernel
  simp

private lemma canonicalAbelParameter_pos {n : ℕ} (hn : 0 < n) :
    0 < canonicalAbelParameter n := by
  unfold canonicalAbelParameter
  positivity

/-- The boundary half-circle kernel inherits the exact sine mass from its
Abel regularizations. -/
theorem integral_sin_mul_platformHalfCircleBoundaryLogDifference
    {theta : ℝ} (htheta : theta ∈ Ioo 0 Real.pi) :
    (∫ phi in 0..Real.pi,
      Real.sin phi * platformHalfCircleBoundaryLogDifference theta phi) =
      Real.pi * Real.sin theta := by
  let F : ℕ → ℝ → ℝ := fun n phi ↦
    Real.sin phi * platformHalfCircleAbelLogDifference
      (canonicalAbelParameter n) theta phi
  let f : ℝ → ℝ := fun phi ↦
    Real.sin phi * platformHalfCircleBoundaryLogDifference theta phi
  let bound : ℝ → ℝ := fun phi ↦
    Real.sin phi * platformHalfCircleBoundaryLogDifference theta phi
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n)
      (volume.restrict (uIoc (0 : ℝ) Real.pi)) := by
    apply Filter.Eventually.of_forall
    intro n
    apply Continuous.aestronglyMeasurable
    dsimp only [F]
    exact Real.continuous_sin.mul
      (continuous_platformHalfCircleAbelLogDifference
        (canonicalAbelParameter_isInteriorApproach.1 n) theta)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi → ‖F n phi‖ ≤ bound phi := by
    apply Filter.Eventually.of_forall
    intro n
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hne
    intro hphi
    rw [uIoc_of_le Real.pi_pos.le] at hphi
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hphi.1.le, hphi.2⟩
    have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨htheta.1.le, htheta.2.le⟩
    have hsin : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphiIcc.1 hphiIcc.2
    have hboundaryNonneg :=
      platformHalfCircleBoundaryLogDifference_nonneg
        hthetaIcc hphiIcc hne.symm
    by_cases hn : n = 0
    · subst n
      dsimp only [F, bound]
      simp only [canonicalAbelParameter, Nat.cast_zero, zero_add, zero_div,
        platformHalfCircleAbelLogDifference_rho_zero, mul_zero,
        norm_zero]
      exact mul_nonneg hsin hboundaryNonneg
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hrhopos : 0 < canonicalAbelParameter n :=
        canonicalAbelParameter_pos hnpos
      have hrholt : canonicalAbelParameter n < 1 := by
        have habs := canonicalAbelParameter_isInteriorApproach.1 n
        rw [abs_of_pos hrhopos] at habs
        exact habs
      have hdom :=
        platformHalfCircleAbelLogDifference_nonneg_le_boundary
          hrhopos hrholt hthetaIcc hphiIcc hne.symm
      dsimp only [F, bound]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsin,
        abs_of_nonneg hdom.1]
      exact mul_le_mul_of_nonneg_left hdom.2 hsin
  have hboundIntegrable : IntervalIntegrable bound volume 0 Real.pi := by
    dsimp only [bound]
    exact intervalIntegrable_sin_mul_platformHalfCircleBoundaryLogDifference
      theta 0 Real.pi
  have hlimit : ∀ᵐ phi ∂volume,
      phi ∈ uIoc (0 : ℝ) Real.pi →
        Tendsto (fun n ↦ F n phi) atTop (nhds (f phi)) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hne
    intro hphi
    rw [uIoc_of_le Real.pi_pos.le] at hphi
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hphi.1.le, hphi.2⟩
    have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨htheta.1.le, htheta.2.le⟩
    dsimp only [F, f]
    exact tendsto_const_nhds.mul
      (tendsto_platformHalfCircleAbelLogDifference_canonical
        hthetaIcc hphiIcc hne.symm)
  have hDCT : Tendsto
      (fun n ↦ ∫ phi in 0..Real.pi, F n phi)
      atTop (nhds (∫ phi in 0..Real.pi, f phi)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hmeas hbound hboundIntegrable hlimit
  have hexact (n : ℕ) :
      (∫ phi in 0..Real.pi, F n phi) =
        Real.pi * canonicalAbelParameter n * Real.sin theta := by
    dsimp only [F]
    exact integral_sin_mul_platformHalfCircleAbelLogDifference
      (canonicalAbelParameter_isInteriorApproach.1 n) theta
  have hDCT' : Tendsto
      (fun n ↦ Real.pi * canonicalAbelParameter n * Real.sin theta)
      atTop (nhds (∫ phi in 0..Real.pi, f phi)) := by
    apply hDCT.congr'
    filter_upwards with n
    exact hexact n
  have hformula : Tendsto
      (fun n ↦ Real.pi * canonicalAbelParameter n * Real.sin theta)
      atTop (nhds (Real.pi * Real.sin theta)) := by
    simpa only [mul_one] using! (tendsto_const_nhds.mul
      canonicalAbelParameter_isInteriorApproach.2).mul
        tendsto_const_nhds
  have heq := tendsto_nhds_unique hDCT' hformula
  dsimp only [f] at heq
  exact heq

private lemma platformBoundaryPoissonDenominator_add_pos
    {theta phi : ℝ} (htheta : theta ∈ Ioo 0 Real.pi)
    (hphi : phi ∈ Ioo 0 Real.pi) :
    0 < platformBoundaryPoissonDenominator (theta + phi) := by
  have hsum0 : 0 < theta + phi := by linarith [htheta.1, hphi.1]
  have hsum2pi : theta + phi < 2 * Real.pi := by
    linarith [htheta.2, hphi.2]
  have hne : platformBoundaryPoissonDenominator (theta + phi) ≠ 0 := by
    intro hzero
    have hcos : Real.cos (theta + phi) = 1 := by
      unfold platformBoundaryPoissonDenominator at hzero
      linarith
    have hsum : theta + phi = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [Real.pi_pos, hsum0] :
          -(2 * Real.pi) < theta + phi) hsum2pi).mp hcos
    linarith
  exact lt_of_le_of_ne (platformBoundaryPoissonDenominator_nonneg _)
    (Ne.symm hne)

/-- Off the diagonal, the angular derivative of the boundary log kernel is
the half-circle Cauchy kernel. -/
theorem hasDerivAt_platformHalfCircleBoundaryLogDifference_phi
    {theta phi : ℝ} (htheta : theta ∈ Ioo 0 Real.pi)
    (hphi : phi ∈ Ioo 0 Real.pi) (hne : theta ≠ phi) :
    HasDerivAt (platformHalfCircleBoundaryLogDifference theta)
      (Real.sin theta / (Real.cos phi - Real.cos theta)) phi := by
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
    ⟨hphi.1.le, hphi.2.le⟩
  have hplus : 0 < platformBoundaryPoissonDenominator (theta + phi) :=
    platformBoundaryPoissonDenominator_add_pos htheta hphi
  have hminus : 0 < platformBoundaryPoissonDenominator (theta - phi) :=
    platformBoundaryPoissonDenominator_sub_pos_of_ne
      hthetaIcc hphiIcc hne
  have hcosne : Real.cos phi - Real.cos theta ≠ 0 := by
    rw [sub_ne_zero]
    intro hcos
    apply hne
    exact Real.strictAntiOn_cos.injOn hthetaIcc hphiIcc hcos.symm
  have hargPlus : HasDerivAt (fun x : ℝ ↦ theta + x) 1 phi :=
    by simpa using! (hasDerivAt_const phi theta).add (hasDerivAt_id phi)
  have hargMinus : HasDerivAt (fun x : ℝ ↦ theta - x) (-1) phi :=
    by simpa using! (hasDerivAt_const phi theta).sub (hasDerivAt_id phi)
  have hDplus : HasDerivAt
      (fun x : ℝ ↦ platformBoundaryPoissonDenominator (theta + x))
      (2 * Real.sin (theta + phi)) phi := by
    unfold platformBoundaryPoissonDenominator
    convert! (hasDerivAt_const phi (2 : ℝ)).sub
      ((Real.hasDerivAt_cos (theta + phi)).comp phi hargPlus |>.const_mul 2)
      using 1
    ring
  have hDminus : HasDerivAt
      (fun x : ℝ ↦ platformBoundaryPoissonDenominator (theta - x))
      (-2 * Real.sin (theta - phi)) phi := by
    unfold platformBoundaryPoissonDenominator
    convert! (hasDerivAt_const phi (2 : ℝ)).sub
      ((Real.hasDerivAt_cos (theta - phi)).comp phi hargMinus |>.const_mul 2)
      using 1
    ring
  have hderiv := ((hDplus.log hplus.ne').sub
    (hDminus.log hminus.ne')).const_mul (1 / 2 : ℝ)
  unfold platformHalfCircleBoundaryLogDifference
  convert! hderiv using 1
  field_simp [hplus.ne', hminus.ne', hcosne]
  rw [platformBoundaryPoissonDenominator, platformBoundaryPoissonDenominator,
    Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
  linear_combination
    (4 * Real.sin theta * (Real.cos theta * Real.cos phi - 1)) *
        (Real.sin_sq_add_cos_sq phi) -
      (4 * Real.sin theta * Real.sin phi ^ 2) *
        (Real.sin_sq_add_cos_sq theta)

omit [LinearOrder iota] in
/-- The smooth derivative part of every Abel-log block is uniformly bounded
after the endpoint `sin theta` factor is restored. -/
theorem norm_integral_deriv_mul_platformHalfCircleAbelLogDifference_le
    (C : ResidualConfiguration iota) (k : ℝ) {a rho : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (i : iota) {theta left right : ℝ}
    (htheta : theta ∈ Ioo 0 Real.pi)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    ‖∫ phi in left..right,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleAbelLogDifference rho theta phi‖ ≤
      platformResidualMaterialSmoothBlockDerivativeBound C k a i *
        Real.pi * Real.sin theta := by
  let D := platformResidualMaterialSmoothBlockDerivativeBound C k a i
  let g : ℝ → ℝ := fun phi ↦
    D * (Real.sin phi *
      platformHalfCircleBoundaryLogDifference theta phi)
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact platformResidualMaterialSmoothBlockDerivativeBound_nonneg
      C k ha ha2 i
  have hgFull : IntervalIntegrable g volume 0 Real.pi := by
    dsimp only [g]
    exact (intervalIntegrable_sin_mul_platformHalfCircleBoundaryLogDifference
      theta 0 Real.pi).const_mul D
  have hgBlock : IntervalIntegrable g volume left right := by
    apply hgFull.mono_set
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hpoint : ∀ᵐ phi ∂volume,
      phi ∈ Ioc left right →
        ‖deriv (platformResidualMaterialSmoothBlock C k a i) phi *
            platformHalfCircleAbelLogDifference rho theta phi‖ ≤
          g phi := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hne
    intro hphi
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hphi.1.le, hphi.2.trans hright⟩
    have hsin : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphiIcc.1 hphiIcc.2
    have hderiv := abs_deriv_platformResidualMaterialSmoothBlock_le_sin
      C k ha ha2 i hphiIcc
    have hkernel :=
      platformHalfCircleAbelLogDifference_nonneg_le_boundary
        hrho0 hrho1 hthetaIcc hphiIcc hne.symm
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel.1]
    dsimp only [g, D]
    calc
      |deriv (platformResidualMaterialSmoothBlock C k a i) phi| *
          platformHalfCircleAbelLogDifference rho theta phi ≤
        (platformResidualMaterialSmoothBlockDerivativeBound C k a i *
          Real.sin phi) *
          platformHalfCircleAbelLogDifference rho theta phi := by
            exact mul_le_mul_of_nonneg_right hderiv hkernel.1
      _ ≤ platformResidualMaterialSmoothBlockDerivativeBound C k a i *
          (Real.sin phi *
            platformHalfCircleBoundaryLogDifference theta phi) := by
            nlinarith [mul_le_mul_of_nonneg_left hkernel.2 hsin,
              mul_nonneg hD hsin]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hle
    hpoint hgBlock
  have hgNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) Real.pi)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) theta)]
      with phi hphi hne
    have hphiIcc : phi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hphi.1.le, hphi.2⟩
    have hsin : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphiIcc.1 hphiIcc.2
    have hK := platformHalfCircleBoundaryLogDifference_nonneg
      hthetaIcc hphiIcc hne.symm
    exact mul_nonneg hD (mul_nonneg hsin hK)
  have hmono : (∫ phi in left..right, g phi) ≤
      ∫ phi in 0..Real.pi, g phi :=
    intervalIntegral.integral_mono_interval hleft hle hright
      hgNonneg hgFull
  calc
    ‖∫ phi in left..right,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleAbelLogDifference rho theta phi‖ ≤
      ∫ phi in left..right, g phi := hnorm
    _ ≤ ∫ phi in 0..Real.pi, g phi := hmono
    _ = D * ∫ phi in 0..Real.pi,
        Real.sin phi *
          platformHalfCircleBoundaryLogDifference theta phi := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
    _ = platformResidualMaterialSmoothBlockDerivativeBound C k a i *
        Real.pi * Real.sin theta := by
      rw [integral_sin_mul_platformHalfCircleBoundaryLogDifference htheta]
      dsimp only [D]
      ring

/-- To the right of a fixed interior jump, the endpoint cancellation in the
boundary log kernel gives a uniform bound after division by `sin theta`. -/
theorem platformHalfCircleBoundaryLogDifference_div_sin_le_right
    {t theta : ℝ} (ht : t ∈ Ioo 0 Real.pi)
    (htheta : theta ∈ Ioc ((t + Real.pi) / 2) Real.pi) :
    0 ≤ platformHalfCircleBoundaryLogDifference theta t / Real.sin theta ∧
      platformHalfCircleBoundaryLogDifference theta t / Real.sin theta ≤
        2 * Real.sin t /
          platformBoundaryPoissonDenominator ((Real.pi - t) / 2) := by
  let A := platformBoundaryPoissonDenominator (theta + t)
  let B := platformBoundaryPoissonDenominator (theta - t)
  let delta := (Real.pi - t) / 2
  by_cases hthetaPiEq : theta = Real.pi
  · subst theta
    simp only [platformHalfCircleBoundaryLogDifference_pi_left,
      Real.sin_pi, div_zero, le_refl, true_and]
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2.le))
      (platformBoundaryPoissonDenominator_nonneg _)
  have htheta0 : 0 < theta := by
    have hmid0 : 0 < (t + Real.pi) / 2 := by
      linarith [ht.1, Real.pi_pos]
    exact hmid0.trans htheta.1
  have hthetaPi : theta < Real.pi := lt_of_le_of_ne htheta.2 hthetaPiEq
  have hsinTheta : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta0 hthetaPi
  have hsinT : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hthetaGt : t < theta := by
    have hmidGt : t < (t + Real.pi) / 2 := by linarith [ht.2]
    exact hmidGt.trans htheta.1
  have hdiff : theta - t ∈ Ioo 0 Real.pi :=
    ⟨sub_pos.mpr hthetaGt, by linarith [ht.1, hthetaPi]⟩
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta0.le, hthetaPi.le⟩
  have htIcc : t ∈ Icc (0 : ℝ) Real.pi :=
    ⟨ht.1.le, ht.2.le⟩
  have hB : 0 < B := by
    dsimp only [B]
    exact platformBoundaryPoissonDenominator_sub_pos_of_ne
      hthetaIcc htIcc (ne_of_gt hthetaGt)
  have hAB : B ≤ A := by
    dsimp only [A, B]
    rw [← sub_nonneg, platformBoundaryPoissonDenominator_sub]
    exact mul_nonneg (mul_nonneg (by norm_num) hsinTheta.le) hsinT.le
  have hA : 0 < A := hB.trans_le hAB
  have hKnonneg := platformHalfCircleBoundaryLogDifference_nonneg
    hthetaIcc htIcc (ne_of_gt hthetaGt)
  have hlog : Real.log (A / B) ≤ A / B - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hA hB)
  have hKlog : platformHalfCircleBoundaryLogDifference theta t =
      (1 / 2 : ℝ) * Real.log (A / B) := by
    unfold platformHalfCircleBoundaryLogDifference
    dsimp only [A, B]
    rw [Real.log_div hA.ne' hB.ne']
  have hratio : A / B - 1 =
      4 * Real.sin theta * Real.sin t / B := by
    apply (eq_div_iff hB.ne').2
    rw [sub_mul, div_mul_cancel₀ A hB.ne']
    dsimp only [A, B]
    rw [one_mul, platformBoundaryPoissonDenominator_sub]
  have hfirst :
      platformHalfCircleBoundaryLogDifference theta t / Real.sin theta ≤
        2 * Real.sin t / B := by
    rw [hKlog]
    have hscaled := mul_le_mul_of_nonneg_left hlog (by norm_num :
      (0 : ℝ) ≤ 1 / 2)
    rw [hratio] at hscaled
    apply (div_le_iff₀ hsinTheta).2
    calc
      (1 / 2 : ℝ) * Real.log (A / B) ≤ (1 / 2 : ℝ) *
          (4 * Real.sin theta * Real.sin t / B) := hscaled
      _ = 2 * Real.sin t / B * Real.sin theta := by ring
  have hdelta : delta ∈ Ioo 0 Real.pi := by
    dsimp only [delta]
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have hdeltale : delta ≤ theta - t := by
    dsimp only [delta]
    linarith [htheta.1]
  have hcosle : Real.cos (theta - t) ≤ Real.cos delta :=
    Real.antitoneOn_cos
      ⟨hdelta.1.le, hdelta.2.le⟩
      ⟨hdiff.1.le, hdiff.2.le⟩ hdeltale
  have hdenle : platformBoundaryPoissonDenominator delta ≤ B := by
    dsimp only [B]
    unfold platformBoundaryPoissonDenominator
    linarith
  have hdeltaDen : 0 < platformBoundaryPoissonDenominator delta := by
    have hne : delta ≠ 0 := ne_of_gt hdelta.1
    have hzeroIcc : (0 : ℝ) ∈ Icc 0 Real.pi :=
      ⟨le_rfl, Real.pi_pos.le⟩
    simpa only [sub_zero] using!
      platformBoundaryPoissonDenominator_sub_pos_of_ne
        ⟨hdelta.1.le, hdelta.2.le⟩ hzeroIcc hne
  constructor
  · exact div_nonneg hKnonneg hsinTheta.le
  · exact hfirst.trans (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) hsinT.le) hdeltaDen hdenle)

theorem continuous_platformAngularAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    Continuous (platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) := by
  have hd : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdm (theta : ℝ) :
      platformAngularDistance a theta - xMinus ≠ 0 := by
    have hge := platformAngularDistance_ge_all ha2.le theta
    exact (sub_pos.mpr (hxMinus.trans_le hge)).ne'
  have hdp (theta : ℝ) :
      platformAngularDistance a theta - xPlus ≠ 0 := by
    have hge := platformAngularDistance_ge_all ha2.le theta
    exact (sub_pos.mpr (hxPlus.trans_le hge)).ne'
  unfold platformAngularAdjointDensity adjointNumerator
  exact (continuous_const.sub
    (continuous_const.div (hd.sub continuous_const) hdm)).sub
      (continuous_const.div (hd.sub continuous_const) hdp)

theorem continuousOn_platformAngularAdjointDensityDivSinLeftExtension
    {a xMinus xPlus sigmaMinus sigmaPlus upper : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (ha2 : a < 2) (hupper : upper < Real.pi) :
    ContinuousOn
      (platformAngularAdjointDensityDivSinLeftExtension
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc 0 upper) := by
  let s := Icc (0 : ℝ) upper
  have hd : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdm (theta : ℝ) :
      platformAngularDistance a theta - xMinus ≠ 0 := by
    have hge := platformAngularDistance_ge_all ha2.le theta
    exact (sub_pos.mpr (hxMinus.trans_le hge)).ne'
  have hdp (theta : ℝ) :
      platformAngularDistance a theta - xPlus ≠ 0 := by
    have hge := platformAngularDistance_ge_all ha2.le theta
    exact (sub_pos.mpr (hxPlus.trans_le hge)).ne'
  have hcosDen : ∀ theta ∈ s, 1 + Real.cos theta ≠ 0 := by
    intro theta htheta
    have hthetaLt : theta < Real.pi := htheta.2.trans_lt hupper
    have hcosGt : -1 < Real.cos theta := by
      have hanti := Real.strictAntiOn_cos
        ⟨htheta.1, hthetaLt.le⟩
        (⟨Real.pi_pos.le, le_rfl⟩ : Real.pi ∈ Icc 0 Real.pi)
        hthetaLt
      simpa only [Real.cos_pi] using! hanti
    linarith
  have hhalf : ContinuousOn
      (fun theta : ℝ ↦ Real.sin theta / (1 + Real.cos theta)) s :=
    Real.continuous_sin.continuousOn.div
      (continuousOn_const.add Real.continuous_cos.continuousOn) hcosDen
  have hminus : Continuous
      (fun theta : ℝ ↦ sigmaMinus * platformCrossingScale a xMinus /
        ((a - xMinus) * (platformAngularDistance a theta - xMinus))) := by
    exact continuous_const.div
      (continuous_const.mul (hd.sub continuous_const)) fun theta ↦ by
        exact mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hxMinus)) (hdm theta)
  have hplus : Continuous
      (fun theta : ℝ ↦ sigmaPlus * platformCrossingScale a xPlus /
        ((a - xPlus) * (platformAngularDistance a theta - xPlus))) := by
    exact continuous_const.div
      (continuous_const.mul (hd.sub continuous_const)) fun theta ↦ by
        exact mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hxPlus)) (hdp theta)
  unfold platformAngularAdjointDensityDivSinLeftExtension
  exact (continuousOn_const.mul hhalf).mul
    (hminus.continuousOn.add hplus.continuousOn)

/-- The boundary denominator is a quadratic zero times a nonvanishing
`sinc` factor near the origin. -/
lemma platformBoundaryPoissonDenominator_eq_sq_mul_sinc_sq (u : ℝ) :
    platformBoundaryPoissonDenominator u =
      u ^ 2 * Real.sinc (u / 2) ^ 2 := by
  by_cases hu : u = 0
  · subst u
    simp [platformBoundaryPoissonDenominator]
  rw [Real.sinc_of_ne_zero (div_ne_zero hu (by norm_num))]
  have hcos : Real.cos u =
      Real.cos (u / 2) ^ 2 - Real.sin (u / 2) ^ 2 := by
    conv_lhs => rw [show u = 2 * (u / 2) by ring, Real.cos_two_mul']
  have htrig := Real.sin_sq_add_cos_sq (u / 2)
  unfold platformBoundaryPoissonDenominator
  rw [hcos]
  field_simp [hu]
  nlinarith

private lemma tendsto_mul_log_sq_zero :
    Tendsto (fun u : ℝ ↦ u * Real.log (u ^ 2)) (𝓝 0) (𝓝 0) := by
  have hcont : ContinuousAt
      (fun u : ℝ ↦ u * Real.log (u ^ 2)) 0 := by
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have h : Tendsto (fun u : ℝ ↦ 2 * (Real.log u * u))
          (𝓝[<] 0) (𝓝 0) := by
        simpa using! tendsto_log_mul_self_nhdsLT_zero.const_mul (2 : ℝ)
      have hh : Tendsto (fun u : ℝ ↦ u * Real.log (u ^ 2))
          (𝓝[<] 0) (𝓝 0) := by
        refine h.congr' ?_
        filter_upwards with u
        rw [Real.log_pow]
        norm_num
        ring
      change Tendsto (fun u : ℝ ↦ u * Real.log (u ^ 2))
        (𝓝[<] 0) (𝓝 ((0 : ℝ) * Real.log (0 ^ 2)))
      simpa only [zero_mul] using! hh
    · have hbase := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
      simp only [Real.rpow_one] at hbase
      have h : Tendsto (fun u : ℝ ↦ 2 * (Real.log u * u))
          (𝓝[>] 0) (𝓝 0) := by
        simpa using! hbase.const_mul (2 : ℝ)
      have hh : Tendsto (fun u : ℝ ↦ u * Real.log (u ^ 2))
          (𝓝[>] 0) (𝓝 0) := by
        refine h.congr' ?_
        filter_upwards with u
        rw [Real.log_pow]
        norm_num
        ring
      change Tendsto (fun u : ℝ ↦ u * Real.log (u ^ 2))
        (𝓝[>] 0) (𝓝 ((0 : ℝ) * Real.log (0 ^ 2)))
      simpa only [zero_mul] using! hh
  simpa using! hcont.tendsto

/-- A linear zero cancels the logarithmic singularity of the boundary
Poisson denominator. -/
lemma tendsto_mul_log_platformBoundaryPoissonDenominator_zero :
    Tendsto
      (fun u : ℝ ↦ u * Real.log (platformBoundaryPoissonDenominator u))
      (𝓝 0) (𝓝 0) := by
  have hsinc : ContinuousAt (fun u : ℝ ↦ Real.sinc (u / 2)) 0 := by
    exact Real.continuous_sinc.continuousAt.comp
      (continuousAt_id.div_const (2 : ℝ))
  have hsincSq : ContinuousAt (fun u : ℝ ↦ Real.sinc (u / 2) ^ 2) 0 :=
    hsinc.pow 2
  have hsincSqNe : (fun u : ℝ ↦ Real.sinc (u / 2) ^ 2) 0 ≠ 0 := by
    simp
  have hsecond : Tendsto
      (fun u : ℝ ↦ u * Real.log (Real.sinc (u / 2) ^ 2))
      (𝓝 0) (𝓝 0) := by
    simpa using! (continuousAt_id.mul (hsincSq.log hsincSqNe)).tendsto
  have hsum : Tendsto
      (fun u : ℝ ↦ u * Real.log (u ^ 2) +
        u * Real.log (Real.sinc (u / 2) ^ 2))
      (𝓝 0) (𝓝 0) := by
    simpa using! tendsto_mul_log_sq_zero.add hsecond
  refine hsum.congr' ?_
  filter_upwards [hsincSq.eventually_ne hsincSqNe] with u hu
  by_cases huzero : u = 0
  · subst u
    simp [platformBoundaryPoissonDenominator]
  rw [platformBoundaryPoissonDenominator_eq_sq_mul_sinc_sq,
    Real.log_mul (pow_ne_zero 2 huzero) hu]
  ring

private lemma platformBoundaryPoissonDenominator_two_mul_pos
    {theta : ℝ} (htheta : theta ∈ Ioo 0 Real.pi) :
    0 < platformBoundaryPoissonDenominator (theta + theta) := by
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  have htrig := Real.sin_sq_add_cos_sq theta
  unfold platformBoundaryPoissonDenominator
  rw [show theta + theta = 2 * theta by ring, Real.cos_two_mul']
  nlinarith

/-- At the diagonal, the boundary logarithmic kernel grows more slowly than
the reciprocal of the distance to the diagonal. -/
theorem tendsto_sub_mul_platformHalfCircleBoundaryLogDifference
    {theta : ℝ} (htheta : theta ∈ Ioo 0 Real.pi) :
    Tendsto
      (fun phi : ℝ ↦ (phi - theta) *
        platformHalfCircleBoundaryLogDifference theta phi)
      (𝓝 theta) (𝓝 0) := by
  have hdenCont : Continuous platformBoundaryPoissonDenominator := by
    unfold platformBoundaryPoissonDenominator
    fun_prop
  have hplusDen : ContinuousAt
      (fun phi : ℝ ↦
        platformBoundaryPoissonDenominator (theta + phi)) theta := by
    fun_prop
  have hplusNe :
      platformBoundaryPoissonDenominator (theta + theta) ≠ 0 :=
    (platformBoundaryPoissonDenominator_two_mul_pos htheta).ne'
  have hplusLog : ContinuousAt
      (fun phi : ℝ ↦ Real.log
        (platformBoundaryPoissonDenominator (theta + phi))) theta :=
    hplusDen.log hplusNe
  have hplus : Tendsto
      (fun phi : ℝ ↦ (phi - theta) * Real.log
        (platformBoundaryPoissonDenominator (theta + phi)))
      (𝓝 theta) (𝓝 0) := by
    simpa using! ((continuousAt_id.sub_const theta).mul hplusLog)
  have harg : Tendsto (fun phi : ℝ ↦ theta - phi)
      (𝓝 theta) (𝓝 0) := by
    have hc : ContinuousAt (fun _phi : ℝ ↦ theta) theta :=
      continuousAt_const
    have hh : Tendsto (fun phi : ℝ ↦ theta - phi)
        (𝓝 theta) (𝓝 (theta - theta)) := hc.sub continuousAt_id
    simpa using! hh
  have hminusRaw : Tendsto
      (fun phi : ℝ ↦ (theta - phi) * Real.log
        (platformBoundaryPoissonDenominator (theta - phi)))
      (𝓝 theta) (𝓝 0) :=
    tendsto_mul_log_platformBoundaryPoissonDenominator_zero.comp harg
  have hminus : Tendsto
      (fun phi : ℝ ↦ (phi - theta) * Real.log
        (platformBoundaryPoissonDenominator (theta - phi)))
      (𝓝 theta) (𝓝 0) := by
    have hneg : Tendsto
        (fun phi : ℝ ↦ -((theta - phi) * Real.log
          (platformBoundaryPoissonDenominator (theta - phi))))
        (𝓝 theta) (𝓝 0) := by
      simpa using! hminusRaw.neg
    refine hneg.congr' ?_
    filter_upwards with phi
    ring
  have hcombined := (hplus.sub hminus).const_mul (1 / 2 : ℝ)
  have hcombined' : Tendsto
      (fun phi : ℝ ↦ (1 / 2 : ℝ) *
        ((phi - theta) * Real.log
            (platformBoundaryPoissonDenominator (theta + phi)) -
          (phi - theta) * Real.log
            (platformBoundaryPoissonDenominator (theta - phi))))
      (𝓝 theta) (𝓝 0) := by
    simpa using! hcombined
  refine hcombined'.congr' ?_
  filter_upwards with phi
  unfold platformHalfCircleBoundaryLogDifference
  ring

theorem measurable_platformHalfCircleBoundaryLogDifference_left (t : ℝ) :
    Measurable (fun theta ↦
      platformHalfCircleBoundaryLogDifference theta t) := by
  unfold platformHalfCircleBoundaryLogDifference
    platformBoundaryPoissonDenominator
  fun_prop

@[simp] lemma platformHalfCircleBoundaryLogDifference_zero_right
    (theta : ℝ) :
    platformHalfCircleBoundaryLogDifference theta 0 = 0 := by
  unfold platformHalfCircleBoundaryLogDifference
  ring_nf

@[simp] lemma platformHalfCircleBoundaryLogDifference_pi_right
    (theta : ℝ) :
    platformHalfCircleBoundaryLogDifference theta Real.pi = 0 := by
  rw [platformHalfCircleBoundaryLogDifference_comm,
    platformHalfCircleBoundaryLogDifference_pi_left]

/-- The adjoint-weighted boundary kernel generated by one material jump. -/
def platformAdjointBoundaryEndpointKernel
    (a xMinus xPlus sigmaMinus sigmaPlus t theta : ℝ) : ℝ :=
  platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus theta *
    platformHalfCircleBoundaryLogDifference theta t / Real.sin theta

/-- Every fixed jump contributes an integrable logarithmic majorant after
the adjoint's endpoint cancellation is included. -/
theorem intervalIntegrable_platformAdjointBoundaryEndpointKernel
    {a xMinus xPlus sigmaMinus sigmaPlus t : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (ht : t ∈ Icc 0 Real.pi) :
    IntervalIntegrable
      (platformAdjointBoundaryEndpointKernel
        a xMinus xPlus sigmaMinus sigmaPlus t)
      volume 0 Real.pi := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · have hz : platformAdjointBoundaryEndpointKernel
        a xMinus xPlus sigmaMinus sigmaPlus 0 = fun _theta ↦ 0 := by
      funext theta
      simp [platformAdjointBoundaryEndpointKernel]
    rw [hz]
    exact IntervalIntegrable.zero
  rcases ht.2.eq_or_lt with rfl | htpi
  · have hz : platformAdjointBoundaryEndpointKernel
        a xMinus xPlus sigmaMinus sigmaPlus Real.pi = fun _theta ↦ 0 := by
      funext theta
      simp [platformAdjointBoundaryEndpointKernel]
    rw [hz]
    exact IntervalIntegrable.zero
  have htIoo : t ∈ Ioo 0 Real.pi := ⟨ht0, htpi⟩
  let leftMid := t / 2
  let rightMid := (t + Real.pi) / 2
  let B := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  let K : ℝ → ℝ := fun theta ↦
    platformHalfCircleBoundaryLogDifference theta t
  let Q := platformAdjointBoundaryEndpointKernel
    a xMinus xPlus sigmaMinus sigmaPlus t
  have hleftMid0 : 0 ≤ leftMid := by
    dsimp only [leftMid]
    linarith
  have hleftMidPi : leftMid < Real.pi := by
    dsimp only [leftMid]
    linarith [htpi, Real.pi_pos]
  have hleftRight : leftMid ≤ rightMid := by
    dsimp only [leftMid, rightMid]
    linarith [Real.pi_pos]
  have hrightMidPi : rightMid ≤ Real.pi := by
    dsimp only [rightMid]
    linarith
  have hKinterval (u v : ℝ) :
      IntervalIntegrable K volume u v := by
    have hbase := intervalIntegrable_platformHalfCircleBoundaryLogDifference
      t u v
    apply hbase.congr
    intro theta _htheta
    dsimp only [K]
    exact platformHalfCircleBoundaryLogDifference_comm t theta
  have hleftCandidate : IntervalIntegrable
      (fun theta ↦
        platformAngularAdjointDensityDivSinLeftExtension
            a xMinus xPlus sigmaMinus sigmaPlus theta * K theta)
      volume 0 leftMid := by
    have hExt :=
      continuousOn_platformAngularAdjointDensityDivSinLeftExtension
        (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hxMinus hxPlus ha2 hleftMidPi
    exact (hKinterval 0 leftMid).continuousOn_mul
      (by simpa only [uIcc_of_le hleftMid0] using! hExt)
  have hleft : IntervalIntegrable Q volume 0 leftMid := by
    apply hleftCandidate.congr
    intro theta htheta
    rw [uIoc_of_le hleftMid0] at htheta
    have hthetaIco : theta ∈ Ico 0 Real.pi :=
      ⟨htheta.1.le, htheta.2.trans_lt hleftMidPi⟩
    dsimp only [Q, K, platformAdjointBoundaryEndpointKernel]
    rw [show
        platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformHalfCircleBoundaryLogDifference theta t /
              Real.sin theta =
          (platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta /
                Real.sin theta) *
            platformHalfCircleBoundaryLogDifference theta t by ring,
      platformAngularAdjointDensity_div_sin_eq_leftExtension
        hxMinus hxPlus ha2 hthetaIco]
  have hBcont : Continuous B := by
    dsimp only [B]
    exact continuous_platformAngularAdjointDensity hxMinus hxPlus ha2
  have hsinNe : ∀ theta ∈ Icc leftMid rightMid,
      Real.sin theta ≠ 0 := by
    intro theta htheta
    have htheta0 : 0 < theta := by
      have : 0 < leftMid := by
        dsimp only [leftMid]
        linarith
      exact this.trans_le htheta.1
    have hthetaPi : theta < Real.pi := by
      have : rightMid < Real.pi := by
        dsimp only [rightMid]
        linarith
      exact htheta.2.trans_lt this
    exact (Real.sin_pos_of_pos_of_lt_pi htheta0 hthetaPi).ne'
  have hmidMultiplier : ContinuousOn
      (fun theta ↦ B theta / Real.sin theta)
      (Icc leftMid rightMid) :=
    hBcont.continuousOn.div Real.continuous_sin.continuousOn hsinNe
  have hmidCandidate : IntervalIntegrable
      (fun theta ↦ (B theta / Real.sin theta) * K theta)
      volume leftMid rightMid := by
    exact (hKinterval leftMid rightMid).continuousOn_mul
      (by simpa only [uIcc_of_le hleftRight] using! hmidMultiplier)
  have hmid : IntervalIntegrable Q volume leftMid rightMid := by
    apply hmidCandidate.congr
    intro theta _htheta
    dsimp only [Q, K, B, platformAdjointBoundaryEndpointKernel]
    ring
  let M := platformBPi a xMinus xPlus sigmaMinus sigmaPlus *
    (2 * Real.sin t /
      platformBoundaryPoissonDenominator ((Real.pi - t) / 2))
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg
      (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).le
      (div_nonneg (mul_nonneg (by norm_num)
        (Real.sin_nonneg_of_nonneg_of_le_pi ht0.le htpi.le))
        (platformBoundaryPoissonDenominator_nonneg _))
  have hQmeas : AEStronglyMeasurable Q
      (volume.restrict (uIoc rightMid Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [Q, platformAdjointBoundaryEndpointKernel]
    exact ((hBcont.measurable.mul
      (measurable_platformHalfCircleBoundaryLogDifference_left t)).div
        Real.continuous_sin.measurable)
  have hQbound : ∀ᵐ theta ∂volume.restrict (uIoc rightMid Real.pi),
      ‖Q theta‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with theta htheta
    rw [uIoc_of_le hrightMidPi] at htheta
    have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨by
        have hmid0 : 0 < rightMid := by
          dsimp only [rightMid]
          linarith [ht0, Real.pi_pos]
        exact hmid0.le.trans htheta.1.le,
       htheta.2⟩
    have hB0 : 0 ≤ B theta := by
      dsimp only [B]
      exact platformAngularAdjointDensity_nonneg hxMinus hxPlus
        hsigmaMinus hsigmaPlus ha2 hthetaIcc
    have hBle : B theta ≤
        platformBPi a xMinus xPlus sigmaMinus sigmaPlus := by
      dsimp only [B, platformBPi]
      exact (platformAngularAdjointDensity_strictMonoOn
        hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn
          hthetaIcc ⟨Real.pi_pos.le, le_rfl⟩ hthetaIcc.2
    have hKquot :=
      platformHalfCircleBoundaryLogDifference_div_sin_le_right
        htIoo htheta
    dsimp only [Q, K, B, platformAdjointBoundaryEndpointKernel]
    rw [show
        platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformHalfCircleBoundaryLogDifference theta t /
              Real.sin theta =
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            (platformHalfCircleBoundaryLogDifference theta t /
              Real.sin theta) by ring,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB0 hKquot.1)]
    dsimp only [M, platformBPi]
    exact mul_le_mul hBle hKquot.2 hKquot.1
      (platformAngularAdjointDensity_nonneg hxMinus hxPlus
        hsigmaMinus hsigmaPlus ha2 ⟨Real.pi_pos.le, le_rfl⟩)
  have hright : IntervalIntegrable Q volume rightMid Real.pi := by
    exact (show IntervalIntegrable (fun _theta : ℝ ↦ M)
        volume rightMid Real.pi from intervalIntegrable_const).mono_fun'
      hQmeas hQbound
  exact (hleft.trans hmid).trans hright

end

end Erdos1038
