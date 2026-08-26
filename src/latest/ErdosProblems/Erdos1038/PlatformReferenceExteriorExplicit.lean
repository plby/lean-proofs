import ErdosProblems.Erdos1038.PlatformReferenceDirectionalRootLimits
import ErdosProblems.Erdos1038.PlatformReferenceBlockObservableRecombination
import ErdosProblems.Erdos1038.PlatformExteriorPotentialIdentity
import ErdosProblems.Erdos1038.PlatformPoissonIntegral
import ErdosProblems.Erdos1038.PlatformAdjointAbelExterior

/-!
# Explicit form of the continuum platform exterior potential

The canonical-reference limit is normalized by total residual mass, whereas
the high-`k` checker uses the unnormalized exterior function `W`.  Here we
prove that multiplication by `k` identifies both the potential and its
spatial derivative with the checker's explicit formulas.  Consequently its
zeroes and reciprocal-slope adjoint weights are exactly those consumed by the
normalized residual assembly.
-/

set_option warningAsError false

open MeasureTheory Set

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Angular form of the two-sided normalized exterior potential, valid on
both sides of zero. -/
theorem platformReferenceExteriorPotentialLimit_eq_angularIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold x =
      Real.log |x| + (1 / k) * (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            Real.log (platformAngularDistance a theta - x)) := by
  unfold platformReferenceExteriorPotentialLimit
  rw [platformReferenceBlockObservableLimit_const_eq_angularIntegral]
  exact (continuousOn_id.sub continuousOn_const).log fun d hd ↦
    (sub_pos.mpr (hxa.trans_le hd.1)).ne'

/-- The checker's exterior function is `k` times the normalized continuum
reference potential. -/
theorem k_mul_platformReferenceExteriorPotentialLimit_eq_platformExteriorW
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) (hx0 : x ≠ 0) :
    k * platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold x =
      platformExteriorW k a x := by
  rw [platformReferenceExteriorPotentialLimit_eq_angularIntegral
    C k a hk ha ha2 hthreshold hxa,
    platformExteriorW_eq_angularPotential ha ha2 hxa hx0]
  have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
  ring_nf
  field_simp [hk0]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _htheta
  ring_nf

/-- The normalized Cauchy integral of one exterior point is the reciprocal
crossing scale. -/
theorem one_div_pi_mul_integral_one_div_platformDistance_sub
    {a x : ℝ} (hxa : x < a) (ha2 : a < 2) :
    (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          1 / (platformAngularDistance a theta - x)) =
      1 / platformCrossingScale a x := by
  have hK : 0 < platformCrossingScale a x :=
    platformCrossingScale_pos hxa ha2
  have hrho := platformRho_mem_Ioo hxa ha2
  have hIntegral :
      (∫ theta in (0 : ℝ)..Real.pi,
          1 / (platformAngularDistance a theta - x)) =
        (1 / platformCrossingScale a x) *
          (∫ theta in (0 : ℝ)..Real.pi,
            platformPoissonKernel (platformRho a x) theta) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    have hden : 0 < platformAngularDistance a theta - x :=
      sub_pos.mpr (hxa.trans_le
        (platformAngularDistance_mem_Icc ha2.le htheta).1)
    have hpoisson := platformCrossingScale_div_distance_eq_poisson
      hxa ha2 htheta
    change 1 / (platformAngularDistance a theta - x) =
      (1 / platformCrossingScale a x) *
        platformPoissonKernel (platformRho a x) theta
    rw [← hpoisson]
    field_simp [hK.ne', hden.ne']
  rw [hIntegral, integral_platformPoissonKernel hrho.1.le hrho.2]
  field_simp [Real.pi_ne_zero, hK.ne']

/-- Explicit normalized resolvent of the angular reference density. -/
theorem one_div_pi_mul_integral_platformAngularDensity_div_distance_sub
    {k a x : ℝ} (ha : 0 < a) (hxa : x < a) (ha2 : a < 2)
    (hx0 : x ≠ 0) :
    (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta /
            (platformAngularDistance a theta - x)) =
      (k + 1) / platformCrossingScale a x -
        k * Real.sqrt (2 * a) / x *
          (1 / platformCrossingScale a x - 1 / Real.sqrt (2 * a)) := by
  let D : ℝ → ℝ := platformAngularDistance a
  let K : ℝ := platformCrossingScale a x
  let S : ℝ := Real.sqrt (2 * a)
  have hK : 0 < K := platformCrossingScale_pos hxa ha2
  have hS : 0 < S := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hDpos : ∀ theta ∈ Set.uIcc (0 : ℝ) Real.pi, 0 < D theta := by
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    exact platformAngularDistance_pos ha ha2.le htheta
  have hDxpos : ∀ theta ∈ Set.uIcc (0 : ℝ) Real.pi,
      0 < D theta - x := by
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    exact sub_pos.mpr (hxa.trans_le
      (platformAngularDistance_mem_Icc ha2.le htheta).1)
  have hID : IntervalIntegrable (fun theta ↦ 1 / D theta)
      volume 0 Real.pi := by
    simpa only [D] using!
      intervalIntegrable_one_div_platformAngularDistance ha ha2.le
  have hIDx : IntervalIntegrable (fun theta ↦ 1 / (D theta - x))
      volume 0 Real.pi := by
    have hDcontinuous : Continuous D := by
      dsimp only [D]
      unfold platformAngularDistance
      fun_prop
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div
      (hDcontinuous.continuousOn.sub continuousOn_const)
      (fun theta htheta ↦ (hDxpos theta htheta).ne')
  have hfun :
      (fun theta ↦ platformAngularDensity k a theta /
          (platformAngularDistance a theta - x)) =
        fun theta ↦
          (k + 1) * (1 / (D theta - x)) -
            (k * S / x) * (1 / (D theta - x) - 1 / D theta) := by
    funext theta
    have hD0 : D theta ≠ 0 := by
      have hge := platformAngularDistance_ge_all ha2.le theta
      exact (ha.trans_le hge).ne'
    have hDx0 : D theta - x ≠ 0 := by
      have hge := platformAngularDistance_ge_all ha2.le theta
      exact (sub_pos.mpr (hxa.trans_le hge)).ne'
    dsimp only [D] at hD0 hDx0
    dsimp only [D, S]
    unfold platformAngularDensity platformDensityCoefficient
    field_simp [hx0, hD0, hDx0]
    ring
  rw [hfun, intervalIntegral.integral_sub
      (hIDx.const_mul (k + 1))
      ((hIDx.sub hID).const_mul (k * S / x)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hIDx hID]
  have hIx := one_div_pi_mul_integral_one_div_platformDistance_sub hxa ha2
  have hI0 := integral_one_div_platformAngularDistance ha ha2.le
  have hIxRaw :
      (∫ theta in (0 : ℝ)..Real.pi,
        1 / (platformAngularDistance a theta - x)) =
          Real.pi / platformCrossingScale a x := by
    calc
      (∫ theta in (0 : ℝ)..Real.pi,
          1 / (platformAngularDistance a theta - x)) =
          Real.pi * ((1 / Real.pi) *
            (∫ theta in (0 : ℝ)..Real.pi,
              1 / (platformAngularDistance a theta - x))) := by
            field_simp [Real.pi_ne_zero]
      _ = Real.pi * (1 / platformCrossingScale a x) := by rw [hIx]
      _ = Real.pi / platformCrossingScale a x := by ring
  dsimp only [K, S] at hK hS ⊢
  rw [hIxRaw, hI0]
  field_simp [Real.pi_ne_zero, hK.ne', hS.ne', hx0]

/-- Stable algebraic form of the explicit transverse derivative. -/
theorem platformExteriorWx_eq_simple
    {k a x : ℝ} (ha : 0 < a) (hxa : x < a) (ha2 : a < 2)
    (hx0 : x ≠ 0) :
    platformExteriorWx k a x =
      (k * Real.sqrt (2 * a) / x - (k + 1)) /
        platformCrossingScale a x := by
  let S : ℝ := Real.sqrt (2 * a)
  let K : ℝ := platformCrossingScale a x
  let Z : ℝ := platformCenter a - x + K
  let R : ℝ := ((Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)) * platformRho a x
  have hS : 0 < S := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hK : 0 < K := platformCrossingScale_pos hxa ha2
  have hCenter : a < platformCenter a := by
    unfold platformCenter
    linarith
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact add_pos (sub_pos.mpr (hxa.trans hCenter)) hK
  have hSa : a < S := by
    have hSsq : S ^ 2 = 2 * a := by
      dsimp only [S]
      exact Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
    nlinarith [sq_nonneg (S + a)]
  have hN : 0 < S + K - x := by linarith
  have hcorr : 1 - R = (S + K - x) / Z := by
    dsimp only [R, S, K, Z]
    exact platformExteriorCorrection_eq ha ha2 hxa
  have hR : R = 1 - (S + K - x) / Z := by linarith
  have hSsq : S ^ 2 = 2 * a := by
    dsimp only [S]
    exact Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
  have hKsq : K ^ 2 = (a - x) * (2 - x) := by
    dsimp only [K]
    exact platformCrossingScale_sq hxa ha2
  have hratio : 2 * R / (1 - R) = (S - K - x) / x := by
    rw [hR]
    field_simp [hx0, hZ.ne', hN.ne']
    dsimp only [Z]
    unfold platformCenter
    nlinarith [hSsq, hKsq]
  rw [platformExteriorWx_eq]
  have hnum :
      2 * k * ((Real.sqrt 2 - Real.sqrt a) /
          (Real.sqrt 2 + Real.sqrt a)) * platformRho a x = 2 * k * R := by
    dsimp only [R]
    ring
  have hdenR :
      1 - ((Real.sqrt 2 - Real.sqrt a) /
          (Real.sqrt 2 + Real.sqrt a)) * platformRho a x = 1 - R := rfl
  rw [hnum, hdenR]
  change k / x - 1 / K + (2 * k * R) / (K * (1 - R)) =
    (k * S / x - (k + 1)) / K
  have hOneR : 1 - R ≠ 0 := by
    rw [hcorr]
    exact div_ne_zero hN.ne' hZ.ne'
  rw [show (2 * k * R) / (K * (1 - R)) =
      k * ((S - K - x) / x) / K by
        rw [← hratio]
        field_simp [hK.ne', hOneR]]
  field_simp [hx0, hK.ne']
  ring

/-- Multiplication by `k` also identifies the continuum spatial derivative
with the checker's explicit `W_x`. -/
theorem k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) (hx0 : x ≠ 0) :
    k * platformReferenceExteriorPotentialXDerivativeLimit C k a
        hk ha ha2 hthreshold x =
      platformExteriorWx k a x := by
  unfold platformReferenceExteriorPotentialXDerivativeLimit
  rw [platformReferenceBlockObservableLimit_const_eq_angularIntegral]
  · have hresolvent :=
      one_div_pi_mul_integral_platformAngularDensity_div_distance_sub
        (k := k) ha hxa ha2 hx0
    let I : ℝ :=
      ∫ theta in (0 : ℝ)..Real.pi,
        platformAngularDensity k a theta *
          (1 / (platformAngularDistance a theta - x))
    have hresolvent' :
        (1 / Real.pi) * I =
          (k + 1) / platformCrossingScale a x -
            k * Real.sqrt (2 * a) / x *
              (1 / platformCrossingScale a x - 1 / Real.sqrt (2 * a)) := by
      dsimp only [I]
      rw [show (fun theta : ℝ ↦
          platformAngularDensity k a theta *
            (1 / (platformAngularDistance a theta - x))) =
        (fun theta ↦ platformAngularDensity k a theta /
          (platformAngularDistance a theta - x)) by
            funext theta
            ring]
      exact hresolvent
    change k * (1 / x - (1 / k) * (1 / Real.pi) * I) =
      platformExteriorWx k a x
    rw [show (1 / k) * (1 / Real.pi) * I =
        (1 / k) * ((1 / Real.pi) * I) by ring,
      hresolvent',
      platformExteriorWx_eq_simple ha hxa ha2 hx0]
    have hk0 : k ≠ 0 := (zero_lt_one.trans_le hk).ne'
    have hK : platformCrossingScale a x ≠ 0 :=
      (platformCrossingScale_pos hxa ha2).ne'
    have hS : Real.sqrt (2 * a) ≠ 0 :=
      (Real.sqrt_pos.2 (mul_pos (by norm_num) ha)).ne'
    field_simp [hk0, hx0, hK, hS]
    ring
  · exact continuousOn_const.div
      (continuousOn_id.sub continuousOn_const) fun d hd ↦
        (sub_pos.mpr (hxa.trans_le hd.1)).ne'

end

end Erdos1038
