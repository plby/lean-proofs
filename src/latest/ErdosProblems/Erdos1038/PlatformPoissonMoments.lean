import ErdosProblems.Erdos1038.PlatformPoissonIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact cosine moments of the platform Poisson kernel

The endpoint-corrected adjoint calculation is diagonal in cosine modes.
This file proves the required identity

`(1/π) ∫₀^π P_ρ(θ) cos(nθ) dθ = ρ^n`

without importing an external Fourier oracle.  The proof uses the defining
denominator identity, the cosine three-term recurrence, and exact interval
integrals.  It is the finite-mode kernel needed before the Abel passage for
piecewise target quantiles.
-/

set_option warningAsError false

open MeasureTheory

namespace Erdos1038

noncomputable section

/-- The unnormalized `n`th cosine moment on the half circle. -/
def platformPoissonCosMoment (rho : ℝ) (n : ℕ) : ℝ :=
  ∫ theta in 0..Real.pi,
    platformPoissonKernel rho theta * Real.cos ((n : ℝ) * theta)

lemma intervalIntegrable_cos_nat_mul (n : ℕ) :
    IntervalIntegrable (fun theta : ℝ ↦ Real.cos ((n : ℝ) * theta))
      volume 0 Real.pi :=
  (Real.continuous_cos.comp
    (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi

lemma integral_cos_nat_mul_zero_pi {n : ℕ} (hn : 0 < n) :
    (∫ theta in 0..Real.pi, Real.cos ((n : ℝ) * theta)) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [intervalIntegral.integral_comp_mul_left Real.cos hn0, integral_cos]
  simp

lemma platformPoissonKernel_mul_den
    {rho theta : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    platformPoissonKernel rho theta *
        (1 - 2 * rho * Real.cos theta + rho ^ 2) =
      1 - rho ^ 2 := by
  unfold platformPoissonKernel
  exact div_mul_cancel₀ _
    (platformPoissonKernel_den_pos (θ := theta) hrho0 hrho1).ne'

lemma intervalIntegrable_platformPoissonKernel_mul_cos
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (n : ℕ) :
    IntervalIntegrable
      (fun theta : ℝ ↦ platformPoissonKernel rho theta *
        Real.cos ((n : ℝ) * theta)) volume 0 Real.pi :=
  (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn

theorem platformPoissonCosMoment_zero
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    platformPoissonCosMoment rho 0 = Real.pi := by
  unfold platformPoissonCosMoment
  simpa using! integral_platformPoissonKernel hrho0 hrho1

theorem platformPoissonCosMoment_one
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    platformPoissonCosMoment rho 1 = Real.pi * rho := by
  by_cases hrho : rho = 0
  · subst rho
    unfold platformPoissonCosMoment platformPoissonKernel
    norm_num [integral_cos_nat_mul_zero_pi (n := 1) (by norm_num)]
  · have hrhoPos : 0 < rho := lt_of_le_of_ne hrho0 (Ne.symm hrho)
    have hP := intervalIntegrable_platformPoissonKernel hrho0 hrho1
    have hidentity :
        (fun theta : ℝ ↦
          2 * rho *
            (platformPoissonKernel rho theta * Real.cos theta)) =
        fun theta ↦
          (1 + rho ^ 2) * platformPoissonKernel rho theta -
            (1 - rho ^ 2) := by
      funext theta
      have hden := platformPoissonKernel_mul_den
        (theta := theta) hrho0 hrho1
      nlinarith
    have hintegral := intervalIntegral.integral_congr
      (μ := volume)
      (a := (0 : ℝ)) (b := Real.pi)
      (fun theta _ ↦ congrFun hidentity theta)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hP.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,
      integral_platformPoissonKernel hrho0 hrho1] at hintegral
    have hmom :
        2 * rho * platformPoissonCosMoment rho 1 =
          (1 + rho ^ 2) * Real.pi - Real.pi * (1 - rho ^ 2) := by
      simpa [platformPoissonCosMoment, smul_eq_mul] using! hintegral
    nlinarith

/-- Three-term recurrence for the half-circle Poisson moments. -/
theorem platformPoissonCosMoment_recurrence
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (n : ℕ) (hn : 0 < n) :
    rho * platformPoissonCosMoment rho (n + 1) =
      (1 + rho ^ 2) * platformPoissonCosMoment rho n -
        rho * platformPoissonCosMoment rho (n - 1) := by
  have hPn := intervalIntegrable_platformPoissonKernel_mul_cos
    hrho0 hrho1 n
  have hPnext := intervalIntegrable_platformPoissonKernel_mul_cos
    hrho0 hrho1 (n + 1)
  have hPprev := intervalIntegrable_platformPoissonKernel_mul_cos
    hrho0 hrho1 (n - 1)
  have hcosn := intervalIntegrable_cos_nat_mul n
  have hpoint :
      (fun theta : ℝ ↦
        rho * (platformPoissonKernel rho theta *
          Real.cos (((n + 1 : ℕ) : ℝ) * theta))) =
      fun theta ↦
        (1 + rho ^ 2) *
            (platformPoissonKernel rho theta *
              Real.cos ((n : ℝ) * theta)) -
          rho * (platformPoissonKernel rho theta *
            Real.cos (((n - 1 : ℕ) : ℝ) * theta)) -
          (1 - rho ^ 2) * Real.cos ((n : ℝ) * theta) := by
    funext theta
    have hden := platformPoissonKernel_mul_den
      (theta := theta) hrho0 hrho1
    have hncast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      exact Nat.cast_pred hn
    have hnext : (((n + 1 : ℕ) : ℝ)) * theta =
        (n : ℝ) * theta + theta := by
      push_cast
      ring
    have hprev : (((n - 1 : ℕ) : ℝ)) * theta =
        (n : ℝ) * theta - theta := by
      rw [hncast]
      ring
    have htrig := Real.two_mul_cos_mul_cos ((n : ℝ) * theta) theta
    have hcosrec :
        Real.cos (((n + 1 : ℕ) : ℝ) * theta) +
            Real.cos (((n - 1 : ℕ) : ℝ) * theta) =
          2 * Real.cos theta * Real.cos ((n : ℝ) * theta) := by
      rw [hnext, hprev]
      nlinarith
    have hdenCos := congrArg
      (fun z : ℝ ↦ z * Real.cos ((n : ℝ) * theta)) hden
    have hcosrecMul := congrArg
      (fun z : ℝ ↦ z * platformPoissonKernel rho theta * rho) hcosrec
    ring_nf at hcosrecMul hdenCos ⊢
    linarith
  have hintegral := intervalIntegral.integral_congr
    (μ := volume)
    (a := (0 : ℝ)) (b := Real.pi)
    (fun theta _ ↦ congrFun hpoint theta)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((hPn.const_mul _).sub (hPprev.const_mul _))
      (hcosn.const_mul _),
    intervalIntegral.integral_sub (hPn.const_mul _) (hPprev.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos_nat_mul_zero_pi hn] at hintegral
  simpa [platformPoissonCosMoment] using! hintegral

/-- Exact Poisson cosine moments. -/
theorem platformPoissonCosMoment_eq
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (n : ℕ) :
    platformPoissonCosMoment rho n = Real.pi * rho ^ n := by
  by_cases hrho : rho = 0
  · subst rho
    cases n with
    | zero => simpa using! platformPoissonCosMoment_zero (rho := 0) (by norm_num) (by norm_num)
    | succ n =>
        unfold platformPoissonCosMoment platformPoissonKernel
        norm_num
        simpa only [Nat.cast_add, Nat.cast_one] using!
          integral_cos_nat_mul_zero_pi (n := n + 1) (Nat.succ_pos n)
  · induction n using Nat.twoStepInduction with
    | zero =>
        simpa using! platformPoissonCosMoment_zero hrho0 hrho1
    | one =>
        simpa using! platformPoissonCosMoment_one hrho0 hrho1
    | more n ih0 ih1 =>
        have hrec := platformPoissonCosMoment_recurrence
          hrho0 hrho1 (n + 1) (Nat.succ_pos n)
        rw [show n + 1 + 1 = n + 2 by omega,
          show n + 1 - 1 = n by omega, ih0, ih1] at hrec
        apply (mul_left_cancel₀ hrho)
        rw [hrec]
        simp only [pow_add, pow_one, pow_two]
        ring

/-- Normalized form used by the adjoint coefficient calculation. -/
theorem one_div_pi_mul_platformPoissonCosMoment
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (n : ℕ) :
    (1 / Real.pi) * platformPoissonCosMoment rho n = rho ^ n := by
  rw [platformPoissonCosMoment_eq hrho0 hrho1]
  field_simp [Real.pi_ne_zero]

end

end Erdos1038
