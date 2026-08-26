import ErdosProblems.Erdos1038.PlatformPoisson

/-!
# Integral normalization of the platform Poisson kernel

The Poisson coordinate introduced for the constant-platform adjoint has
total mass `π` on `[0, π]`.  We derive this from the already verified
affine-cosine reciprocal integral, after an explicit rescaling of its
endpoints.
-/

open Set

namespace Erdos1038

noncomputable section

private def poissonRescaledLeft (rho : ℝ) : ℝ :=
  2 * ((1 - rho) / (1 + rho)) ^ 2

private lemma poissonRescaledLeft_pos {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    0 < poissonRescaledLeft rho := by
  have hnum : 0 < 1 - rho := sub_pos.mpr hrho1
  have hden : 0 < 1 + rho := by linarith
  unfold poissonRescaledLeft
  positivity

private lemma poissonRescaledLeft_le_two {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    poissonRescaledLeft rho ≤ 2 := by
  have hden : 0 < 1 + rho := by linarith
  have hquotNonneg : 0 ≤ (1 - rho) / (1 + rho) :=
    div_nonneg (sub_nonneg.mpr hrho1.le) hden.le
  have hquotLe : (1 - rho) / (1 + rho) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  unfold poissonRescaledLeft
  nlinarith [sq_nonneg ((1 - rho) / (1 + rho))]

private lemma platformAngularDistance_poissonRescaledLeft
    {rho θ : ℝ} (hrho : rho ≠ -1) :
    platformAngularDistance (poissonRescaledLeft rho) θ =
      (2 / (1 + rho) ^ 2) *
        (1 - 2 * rho * Real.cos θ + rho ^ 2) := by
  unfold platformAngularDistance platformCenter platformRadius
    poissonRescaledLeft
  field_simp [show 1 + rho ≠ 0 by
    intro h
    apply hrho
    linarith]
  ring

private lemma sqrt_two_mul_poissonRescaledLeft {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    Real.sqrt (2 * poissonRescaledLeft rho) =
      2 * (1 - rho) / (1 + rho) := by
  have hden : 0 < 1 + rho := by linarith
  have hquot : 0 ≤ 2 * (1 - rho) / (1 + rho) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hrho1.le)) hden.le
  rw [show 2 * poissonRescaledLeft rho =
      (2 * (1 - rho) / (1 + rho)) ^ 2 by
        unfold poissonRescaledLeft
        field_simp [hden.ne']]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hquot]

lemma intervalIntegrable_platformPoissonKernel {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    IntervalIntegrable (platformPoissonKernel rho)
      MeasureTheory.volume 0 Real.pi := by
  have hden : ∀ θ : ℝ,
      0 < 1 - 2 * rho * Real.cos θ + rho ^ 2 :=
    fun θ ↦ platformPoissonKernel_den_pos hrho0 hrho1
  apply ContinuousOn.intervalIntegrable
  unfold platformPoissonKernel
  exact continuousOn_const.div
    (continuousOn_const.sub
      ((continuousOn_const.mul continuousOn_const).mul
        Real.continuous_cos.continuousOn) |>.add continuousOn_const)
    (fun θ _hθ ↦ (hden θ).ne')

/-- The Poisson kernel has its standard half-circle mass. -/
theorem integral_platformPoissonKernel {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    (∫ θ in 0..Real.pi, platformPoissonKernel rho θ) = Real.pi := by
  let a := poissonRescaledLeft rho
  have ha : 0 < a := poissonRescaledLeft_pos hrho0 hrho1
  have ha2 : a ≤ 2 := poissonRescaledLeft_le_two hrho0 hrho1
  have hrhoNeg : rho ≠ -1 := by linarith
  have hscale : 0 < 2 / (1 + rho) ^ 2 := by positivity
  have hrecip := integral_one_div_platformAngularDistance ha ha2
  have hsqrt := sqrt_two_mul_poissonRescaledLeft hrho0 hrho1
  have hreciprocal :
      (∫ θ in 0..Real.pi,
          1 / (1 - 2 * rho * Real.cos θ + rho ^ 2)) =
        Real.pi / (1 - rho ^ 2) := by
    calc
      (∫ θ in 0..Real.pi,
          1 / (1 - 2 * rho * Real.cos θ + rho ^ 2)) =
          ∫ θ in 0..Real.pi,
            (2 / (1 + rho) ^ 2) /
              platformAngularDistance a θ := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        dsimp [a]
        rw [platformAngularDistance_poissonRescaledLeft hrhoNeg]
        field_simp [hscale.ne']
      _ = (2 / (1 + rho) ^ 2) *
          (∫ θ in 0..Real.pi, 1 / platformAngularDistance a θ) := by
        rw [show (fun θ : ℝ ↦
            (2 / (1 + rho) ^ 2) / platformAngularDistance a θ) =
            fun θ ↦ (2 / (1 + rho) ^ 2) *
              (1 / platformAngularDistance a θ) by
              funext θ
              ring,
          intervalIntegral.integral_const_mul]
      _ = Real.pi / (1 - rho ^ 2) := by
        rw [hrecip, hsqrt]
        have honePlus : 1 + rho ≠ 0 := by linarith
        have honeMinus : 1 - rho ≠ 0 := by linarith
        have hsquare : 1 - rho ^ 2 ≠ 0 := by nlinarith
        field_simp [honePlus, honeMinus, hsquare]
        ring
  unfold platformPoissonKernel
  rw [show (fun θ : ℝ ↦
      (1 - rho ^ 2) / (1 - 2 * rho * Real.cos θ + rho ^ 2)) =
      fun θ ↦ (1 - rho ^ 2) *
        (1 / (1 - 2 * rho * Real.cos θ + rho ^ 2)) by
        funext θ
        ring,
    intervalIntegral.integral_const_mul, hreciprocal]
  have hne : 1 - rho ^ 2 ≠ 0 := by nlinarith
  field_simp [hne]

lemma integral_poisson_zero_sub {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    (∫ θ in 0..Real.pi,
        (platformPoissonKernel rho 0 - platformPoissonKernel rho θ)) =
      Real.pi * (platformPoissonKernel rho 0 - 1) := by
  have hkernel := intervalIntegrable_platformPoissonKernel hrho0 hrho1
  rw [intervalIntegral.integral_sub intervalIntegrable_const hkernel,
    intervalIntegral.integral_const, integral_platformPoissonKernel hrho0 hrho1]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Total mass of the adjoint after including the conventional factor `1 / π`. -/
def platformAdjointMass
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  adjointNormalization a xMinus xPlus sigmaMinus sigmaPlus -
    sigmaMinus - sigmaPlus

theorem platformAdjointMass_pos
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    0 < platformAdjointMass
      a xMinus xPlus sigmaMinus sigmaPlus := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  have hPm : 1 < platformPoissonKernel (platformRho a xMinus) 0 := by
    rw [platformPoissonKernel_zero (ne_of_lt hrm.2)]
    rw [lt_div_iff₀ (sub_pos.mpr hrm.2)]
    linarith [hrm.1]
  have hPp : 1 < platformPoissonKernel (platformRho a xPlus) 0 := by
    rw [platformPoissonKernel_zero (ne_of_lt hrp.2)]
    rw [lt_div_iff₀ (sub_pos.mpr hrp.2)]
    linarith [hrp.1]
  have hm : 0 < sigmaMinus *
      (platformPoissonKernel (platformRho a xMinus) 0 - 1) :=
    mul_pos hsigmaMinus (sub_pos.mpr hPm)
  have hp : 0 < sigmaPlus *
      (platformPoissonKernel (platformRho a xPlus) 0 - 1) :=
    mul_pos hsigmaPlus (sub_pos.mpr hPp)
  unfold platformAdjointMass
  rw [adjointNormalization_eq_poisson_zero hxMinus hxPlus ha2]
  nlinarith

lemma intervalIntegrable_platformAngularAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    IntervalIntegrable
      (platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus)
      MeasureTheory.volume 0 Real.pi := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  have hcm : IntervalIntegrable
      (fun _θ : ℝ ↦ platformPoissonKernel (platformRho a xMinus) 0)
      MeasureTheory.volume 0 Real.pi := intervalIntegrable_const
  have hcp : IntervalIntegrable
      (fun _θ : ℝ ↦ platformPoissonKernel (platformRho a xPlus) 0)
      MeasureTheory.volume 0 Real.pi := intervalIntegrable_const
  have hm := (hcm.sub
    (intervalIntegrable_platformPoissonKernel hrm.1.le hrm.2)).const_mul
      sigmaMinus
  have hp := (hcp.sub
    (intervalIntegrable_platformPoissonKernel hrp.1.le hrp.2)).const_mul
      sigmaPlus
  apply (hm.add hp).congr
  intro θ hθ
  rw [uIoc_of_le Real.pi_pos.le] at hθ
  exact (platformAngularAdjointDensity_eq_poisson
    hxMinus hxPlus ha2 ⟨hθ.1.le, hθ.2⟩).symm

/-- The angular adjoint density integrates to `π` times its normalized mass. -/
theorem integral_platformAngularAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    (∫ θ in 0..Real.pi,
        platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus θ) =
      Real.pi * platformAdjointMass
        a xMinus xPlus sigmaMinus sigmaPlus := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  have hcm : IntervalIntegrable
      (fun _θ : ℝ ↦ platformPoissonKernel (platformRho a xMinus) 0)
      MeasureTheory.volume 0 Real.pi := intervalIntegrable_const
  have hcp : IntervalIntegrable
      (fun _θ : ℝ ↦ platformPoissonKernel (platformRho a xPlus) 0)
      MeasureTheory.volume 0 Real.pi := intervalIntegrable_const
  have hm := (hcm.sub
    (intervalIntegrable_platformPoissonKernel hrm.1.le hrm.2)).const_mul
      sigmaMinus
  have hp := (hcp.sub
    (intervalIntegrable_platformPoissonKernel hrp.1.le hrp.2)).const_mul
      sigmaPlus
  calc
    (∫ θ in 0..Real.pi,
        platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus θ) =
        ∫ θ in 0..Real.pi,
          (sigmaMinus *
              (platformPoissonKernel (platformRho a xMinus) 0 -
                platformPoissonKernel (platformRho a xMinus) θ) +
            sigmaPlus *
              (platformPoissonKernel (platformRho a xPlus) 0 -
                platformPoissonKernel (platformRho a xPlus) θ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      exact platformAngularAdjointDensity_eq_poisson
        hxMinus hxPlus ha2 hθ
    _ = Real.pi * platformAdjointMass
        a xMinus xPlus sigmaMinus sigmaPlus := by
      rw [intervalIntegral.integral_add hm hp,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_poisson_zero_sub hrm.1.le hrm.2,
        integral_poisson_zero_sub hrp.1.le hrp.2]
      unfold platformAdjointMass
      rw [adjointNormalization_eq_poisson_zero hxMinus hxPlus ha2]
      ring

theorem normalized_integral_platformAngularAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    (1 / Real.pi) *
        (∫ θ in 0..Real.pi,
          platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus θ) =
      platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus := by
  rw [integral_platformAngularAdjointDensity hxMinus hxPlus ha2]
  field_simp [Real.pi_ne_zero]

end

end Erdos1038
