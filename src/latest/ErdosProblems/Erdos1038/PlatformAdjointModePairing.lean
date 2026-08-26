import ErdosProblems.Erdos1038.PlatformFiniteHilbert
import ErdosProblems.Erdos1038.PlatformAdjointCoefficient

/-!
# Pairing the finite Hilbert modes with the platform adjoint density

This module connects the finite Hilbert-transform calculation to the exact
Poisson-coordinate adjoint coefficients.  It proves the outer `θ` integrals
for both parities, so the coefficient cancellation is now an identity of
actual interval integrals rather than only formal algebra.
-/

set_option warningAsError false

open MeasureTheory

namespace Erdos1038

noncomputable section

/-- The endpoint-normalized adjoint angular density in Poisson coordinates. -/
def endpointAdjointAngularDensity
    (sigmaMinus sigmaPlus rhoMinus rhoPlus theta : ℝ) : ℝ :=
  endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus -
    sigmaMinus * platformPoissonKernel rhoMinus theta -
    sigmaPlus * platformPoissonKernel rhoPlus theta

lemma continuous_endpointAdjointAngularDensity
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) :
    Continuous (endpointAdjointAngularDensity
      sigmaMinus sigmaPlus rhoMinus rhoPlus) := by
  have hminus : Continuous (platformPoissonKernel rhoMinus) := by
    unfold platformPoissonKernel
    apply Continuous.div continuous_const
    · fun_prop
    · intro theta
      exact (platformPoissonKernel_den_pos
        (θ := theta) hm0 hm1).ne'
  have hplus : Continuous (platformPoissonKernel rhoPlus) := by
    unfold platformPoissonKernel
    apply Continuous.div continuous_const
    · fun_prop
    · intro theta
      exact (platformPoissonKernel_den_pos
        (θ := theta) hp0 hp1).ne'
  unfold endpointAdjointAngularDensity
  exact (continuous_const.sub (continuous_const.mul hminus)).sub
    (continuous_const.mul hplus)

lemma intervalIntegrable_endpointAdjointAngularDensity_mul_evenMode
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    IntervalIntegrable
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
        sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          evenSecondKindAngularMode m theta)
      volume 0 Real.pi :=
  ((continuous_endpointAdjointAngularDensity hm0 hm1 hp0 hp1).mul
    (continuous_evenSecondKindAngularMode m)).intervalIntegrable _ _

lemma intervalIntegrable_endpointAdjointAngularDensity_mul_oddMode
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    IntervalIntegrable
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
        sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          oddSecondKindAngularMode m theta)
      volume 0 Real.pi :=
  ((continuous_endpointAdjointAngularDensity hm0 hm1 hp0 hp1).mul
    (continuous_oddSecondKindAngularMode m)).intervalIntegrable _ _

/-- Pairing with an even `U_(2m)` mode. -/
theorem one_div_pi_mul_integral_endpointAdjointDensity_evenMode
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            evenSecondKindAngularMode m theta) =
      endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus -
        (sigmaMinus *
            ((1 + rhoMinus ^ 2 - 2 * rhoMinus ^ (2 * m + 2)) /
              (1 - rhoMinus ^ 2)) +
          sigmaPlus *
            ((1 + rhoPlus ^ 2 - 2 * rhoPlus ^ (2 * m + 2)) /
              (1 - rhoPlus ^ 2))) := by
  let M : ℝ → ℝ := evenSecondKindAngularMode m
  have hM : IntervalIntegrable M volume (0 : ℝ) Real.pi :=
    (continuous_evenSecondKindAngularMode m).intervalIntegrable _ _
  have hPmM : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rhoMinus theta * M theta)
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hm0 hm1).mul_continuousOn
      (continuous_evenSecondKindAngularMode m).continuousOn
  have hPpM : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rhoPlus theta * M theta)
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hp0 hp1).mul_continuousOn
      (continuous_evenSecondKindAngularMode m).continuousOn
  have hpoint :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta * M theta) =
      fun theta ↦
        endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus * M theta -
          sigmaMinus *
            (platformPoissonKernel rhoMinus theta * M theta) -
          sigmaPlus *
            (platformPoissonKernel rhoPlus theta * M theta) := by
    funext theta
    unfold endpointAdjointAngularDensity
    ring
  rw [hpoint,
    intervalIntegral.integral_sub
      ((hM.const_mul _).sub (hPmM.const_mul _)) (hPpM.const_mul _),
    intervalIntegral.integral_sub (hM.const_mul _) (hPmM.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hmean := one_div_pi_mul_integral_evenSecondKind m
  have hm := one_div_pi_mul_integral_platformPoisson_evenSecondKind
    hm0 hm1 m
  have hp := one_div_pi_mul_integral_platformPoisson_evenSecondKind
    hp0 hp1 m
  field_simp [Real.pi_ne_zero] at hmean hm hp ⊢
  rw [hmean, hm, hp]
  ring

/-- Pairing with an odd `U_(2m-1)` mode. -/
theorem one_div_pi_mul_integral_endpointAdjointDensity_oddMode
    {sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            oddSecondKindAngularMode m theta) =
      -(sigmaMinus *
          (2 * rhoMinus * (1 - rhoMinus ^ (2 * m)) /
            (1 - rhoMinus ^ 2)) +
        sigmaPlus *
          (2 * rhoPlus * (1 - rhoPlus ^ (2 * m)) /
            (1 - rhoPlus ^ 2))) := by
  let M : ℝ → ℝ := oddSecondKindAngularMode m
  have hM : IntervalIntegrable M volume (0 : ℝ) Real.pi :=
    (continuous_oddSecondKindAngularMode m).intervalIntegrable _ _
  have hPmM : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rhoMinus theta * M theta)
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hm0 hm1).mul_continuousOn
      (continuous_oddSecondKindAngularMode m).continuousOn
  have hPpM : IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rhoPlus theta * M theta)
      volume 0 Real.pi :=
    (intervalIntegrable_platformPoissonKernel hp0 hp1).mul_continuousOn
      (continuous_oddSecondKindAngularMode m).continuousOn
  have hpoint :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta * M theta) =
      fun theta ↦
        endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus * M theta -
          sigmaMinus *
            (platformPoissonKernel rhoMinus theta * M theta) -
          sigmaPlus *
            (platformPoissonKernel rhoPlus theta * M theta) := by
    funext theta
    unfold endpointAdjointAngularDensity
    ring
  rw [hpoint,
    intervalIntegral.integral_sub
      ((hM.const_mul _).sub (hPmM.const_mul _)) (hPpM.const_mul _),
    intervalIntegral.integral_sub (hM.const_mul _) (hPmM.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hmean := one_div_pi_mul_integral_oddSecondKind m
  have hm := one_div_pi_mul_integral_platformPoisson_oddSecondKind
    hm0 hm1 m
  have hp := one_div_pi_mul_integral_platformPoisson_oddSecondKind
    hp0 hp1 m
  field_simp [Real.pi_ne_zero] at hmean hm hp ⊢
  rw [hmean, hm, hp]
  ring

/-- A unit even cosine coefficient, after the finite Hilbert transform and
outer adjoint pairing, gives the exact even pairing coefficient. -/
theorem finiteHilbert_evenMode_adjointPairing
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (2 / r) * (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (-oddSecondKindAngularMode (m + 1) theta)) =
      endpointAdjointEvenCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  have hneg :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (-oddSecondKindAngularMode (m + 1) theta)) =
      fun theta ↦ -(endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        oddSecondKindAngularMode (m + 1) theta) := by
    funext theta
    ring
  rw [hneg, intervalIntegral.integral_neg]
  have hpair : (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        endpointAdjointAngularDensity
            sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          oddSecondKindAngularMode (m + 1) theta) =
      -(sigmaMinus *
          (2 * rhoMinus * (1 - rhoMinus ^ (2 * (m + 1))) /
            (1 - rhoMinus ^ 2)) +
        sigmaPlus *
          (2 * rhoPlus * (1 - rhoPlus ^ (2 * (m + 1))) /
            (1 - rhoPlus ^ 2))) :=
    one_div_pi_mul_integral_endpointAdjointDensity_oddMode
      hm0 hm1 hp0 hp1 (m + 1)
  calc
    (2 / r) * (1 / Real.pi) *
          -(∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              oddSecondKindAngularMode (m + 1) theta) =
        -(2 / r) * ((1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              oddSecondKindAngularMode (m + 1) theta)) := by ring
    _ = endpointAdjointEvenCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
      rw [hpair]
      unfold endpointAdjointEvenCosCoefficient
      ring

/-- A unit odd cosine coefficient gives the exact odd pairing coefficient. -/
theorem finiteHilbert_oddMode_adjointPairing
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (2 / r) * (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (-evenSecondKindAngularMode m theta)) =
      endpointAdjointOddCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  have hneg :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (-evenSecondKindAngularMode m theta)) =
      fun theta ↦ -(endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        evenSecondKindAngularMode m theta) := by
    funext theta
    ring
  rw [hneg, intervalIntegral.integral_neg]
  have hpair : (1 / Real.pi) *
      (∫ theta in 0..Real.pi,
        endpointAdjointAngularDensity
            sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          evenSecondKindAngularMode m theta) =
      endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus -
        (sigmaMinus *
            ((1 + rhoMinus ^ 2 - 2 * rhoMinus ^ (2 * m + 2)) /
              (1 - rhoMinus ^ 2)) +
          sigmaPlus *
            ((1 + rhoPlus ^ 2 - 2 * rhoPlus ^ (2 * m + 2)) /
              (1 - rhoPlus ^ 2))) :=
    one_div_pi_mul_integral_endpointAdjointDensity_evenMode
      hm0 hm1 hp0 hp1 m
  calc
    (2 / r) * (1 / Real.pi) *
          -(∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              evenSecondKindAngularMode m theta) =
        -(2 / r) * ((1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              evenSecondKindAngularMode m theta)) := by ring
    _ = endpointAdjointOddCosCoefficient
          r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
      rw [hpair]
      unfold endpointAdjointOddCosCoefficient
      ring

end

end Erdos1038
