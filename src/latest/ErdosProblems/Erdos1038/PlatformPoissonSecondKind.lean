import ErdosProblems.Erdos1038.PlatformPoissonMoments
import Mathlib.Algebra.Field.GeomSum

/-!
# Poisson moments of the finite second-kind cosine modes

The endpoint-corrected adjoint uses the elementary expansions

`U_(2m)(cos θ) = 1 + 2 ∑_{l=1}^m cos (2lθ)` and
`U_(2m-1)(cos θ) = 2 ∑_{l=1}^m cos ((2l-1)θ)`.

We take the right sides as the angular definitions.  This avoids making
the analytic argument depend on a particular library normalization of the
Chebyshev polynomials, while retaining exactly the modes that occur in the
finite Hilbert-transform calculation.
-/

set_option warningAsError false

open MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- The angular expansion of `U_(2m)(cos θ)`. -/
def evenSecondKindAngularMode (m : ℕ) (theta : ℝ) : ℝ :=
  1 + ∑ l ∈ Finset.range m, 2 *
    Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)

/-- The angular expansion of `U_(2m-1)(cos θ)`, with `m = 0` giving zero. -/
def oddSecondKindAngularMode (m : ℕ) (theta : ℝ) : ℝ :=
  ∑ l ∈ Finset.range m, 2 *
    Real.cos (((2 * l + 1 : ℕ) : ℝ) * theta)

lemma continuous_evenSecondKindAngularMode (m : ℕ) :
    Continuous (evenSecondKindAngularMode m) := by
  unfold evenSecondKindAngularMode
  fun_prop

lemma continuous_oddSecondKindAngularMode (m : ℕ) :
    Continuous (oddSecondKindAngularMode m) := by
  unfold oddSecondKindAngularMode
  fun_prop

lemma evenSecondKindAngularMode_succ (m : ℕ) (theta : ℝ) :
    evenSecondKindAngularMode (m + 1) theta =
      evenSecondKindAngularMode m theta +
        2 * Real.cos (((2 * (m + 1) : ℕ) : ℝ) * theta) := by
  simp [evenSecondKindAngularMode, Finset.sum_range_succ]
  ring

lemma oddSecondKindAngularMode_succ (m : ℕ) (theta : ℝ) :
    oddSecondKindAngularMode (m + 1) theta =
      oddSecondKindAngularMode m theta +
        2 * Real.cos (((2 * m + 1 : ℕ) : ℝ) * theta) := by
  simp [oddSecondKindAngularMode, Finset.sum_range_succ]

lemma even_power_sum_closed_form
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    1 + 2 * ∑ l ∈ Finset.range m, rho ^ (2 * (l + 1)) =
      (1 + rho ^ 2 - 2 * rho ^ (2 * m + 2)) / (1 - rho ^ 2) := by
  have hden : 1 - rho ^ 2 ≠ 0 := by nlinarith
  have hshift :
      (∑ l ∈ Finset.range m, rho ^ (2 * (l + 1))) =
        rho ^ 2 * ∑ l ∈ Finset.range m, (rho ^ 2) ^ l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_range] at hl
    rw [pow_mul, pow_succ]
    ring
  have hgeom := geom_sum_mul_neg (rho ^ 2) m
  have hlast : rho ^ (2 * m + 2) = rho ^ 2 * (rho ^ 2) ^ m := by
    rw [pow_add, pow_mul]
    ring
  apply (eq_div_iff hden).2
  rw [hshift, hlast]
  calc
    (1 + 2 * (rho ^ 2 * ∑ l ∈ Finset.range m, (rho ^ 2) ^ l)) *
          (1 - rho ^ 2) =
        (1 - rho ^ 2) + 2 * rho ^ 2 *
          ((∑ l ∈ Finset.range m, (rho ^ 2) ^ l) * (1 - rho ^ 2)) := by
            ring
    _ = (1 - rho ^ 2) + 2 * rho ^ 2 * (1 - (rho ^ 2) ^ m) := by
      rw [hgeom]
    _ = 1 + rho ^ 2 - 2 * (rho ^ 2 * (rho ^ 2) ^ m) := by ring

lemma odd_power_sum_closed_form
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    2 * ∑ l ∈ Finset.range m, rho ^ (2 * l + 1) =
      2 * rho * (1 - rho ^ (2 * m)) / (1 - rho ^ 2) := by
  have hden : 1 - rho ^ 2 ≠ 0 := by nlinarith
  have hshift :
      (∑ l ∈ Finset.range m, rho ^ (2 * l + 1)) =
        rho * ∑ l ∈ Finset.range m, (rho ^ 2) ^ l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_range] at hl
    rw [pow_add, pow_mul]
    ring
  have hgeom := geom_sum_mul_neg (rho ^ 2) m
  have hlast : rho ^ (2 * m) = (rho ^ 2) ^ m := pow_mul rho 2 m
  apply (eq_div_iff hden).2
  rw [hshift, hlast]
  calc
    (2 * (rho * ∑ l ∈ Finset.range m, (rho ^ 2) ^ l)) *
          (1 - rho ^ 2) =
        2 * rho *
          ((∑ l ∈ Finset.range m, (rho ^ 2) ^ l) * (1 - rho ^ 2)) := by
            ring
    _ = 2 * rho * (1 - (rho ^ 2) ^ m) := by rw [hgeom]

lemma integral_platformPoisson_evenSecondKind_eq_power_sum
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    (∫ theta in 0..Real.pi,
      platformPoissonKernel rho theta * evenSecondKindAngularMode m theta) =
      Real.pi *
        (1 + 2 * ∑ l ∈ Finset.range m, rho ^ (2 * (l + 1))) := by
  induction m with
  | zero =>
      simp [evenSecondKindAngularMode,
        integral_platformPoissonKernel hrho0 hrho1]
  | succ m ih =>
      have hPmode :=
        (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
          (continuous_evenSecondKindAngularMode m).continuousOn
      have hterm :=
        (intervalIntegrable_platformPoissonKernel_mul_cos
          hrho0 hrho1 (2 * (m + 1))).const_mul 2
      have hpoint :
          (fun theta : ℝ ↦ platformPoissonKernel rho theta *
            evenSecondKindAngularMode (m + 1) theta) =
          fun theta ↦
            platformPoissonKernel rho theta * evenSecondKindAngularMode m theta +
              2 * (platformPoissonKernel rho theta *
                Real.cos (((2 * (m + 1) : ℕ) : ℝ) * theta)) := by
        funext theta
        rw [evenSecondKindAngularMode_succ]
        ring
      rw [hpoint,
        intervalIntegral.integral_add hPmode hterm, ih,
        intervalIntegral.integral_const_mul]
      change Real.pi *
          (1 + 2 * ∑ l ∈ Finset.range m, rho ^ (2 * (l + 1))) +
          2 * platformPoissonCosMoment rho (2 * (m + 1)) = _
      rw [platformPoissonCosMoment_eq hrho0 hrho1,
        Finset.sum_range_succ]
      ring

lemma integral_platformPoisson_oddSecondKind_eq_power_sum
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    (∫ theta in 0..Real.pi,
      platformPoissonKernel rho theta * oddSecondKindAngularMode m theta) =
      Real.pi * (2 * ∑ l ∈ Finset.range m, rho ^ (2 * l + 1)) := by
  induction m with
  | zero => simp [oddSecondKindAngularMode]
  | succ m ih =>
      have hPmode :=
        (intervalIntegrable_platformPoissonKernel hrho0 hrho1).mul_continuousOn
          (continuous_oddSecondKindAngularMode m).continuousOn
      have hterm :=
        (intervalIntegrable_platformPoissonKernel_mul_cos
          hrho0 hrho1 (2 * m + 1)).const_mul 2
      have hpoint :
          (fun theta : ℝ ↦ platformPoissonKernel rho theta *
            oddSecondKindAngularMode (m + 1) theta) =
          fun theta ↦
            platformPoissonKernel rho theta * oddSecondKindAngularMode m theta +
              2 * (platformPoissonKernel rho theta *
                Real.cos (((2 * m + 1 : ℕ) : ℝ) * theta)) := by
        funext theta
        rw [oddSecondKindAngularMode_succ]
        ring
      rw [hpoint,
        intervalIntegral.integral_add hPmode hterm, ih,
        intervalIntegral.integral_const_mul]
      change Real.pi * (2 * ∑ l ∈ Finset.range m, rho ^ (2 * l + 1)) +
          2 * platformPoissonCosMoment rho (2 * m + 1) = _
      rw [platformPoissonCosMoment_eq hrho0 hrho1,
        Finset.sum_range_succ]
      ring

/-- Exact Poisson integral of the even second-kind mode. -/
theorem one_div_pi_mul_integral_platformPoisson_evenSecondKind
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta * evenSecondKindAngularMode m theta) =
      (1 + rho ^ 2 - 2 * rho ^ (2 * m + 2)) / (1 - rho ^ 2) := by
  rw [integral_platformPoisson_evenSecondKind_eq_power_sum hrho0 hrho1,
    even_power_sum_closed_form hrho0 hrho1]
  field_simp [Real.pi_ne_zero]

/-- Exact Poisson integral of the odd second-kind mode. -/
theorem one_div_pi_mul_integral_platformPoisson_oddSecondKind
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformPoissonKernel rho theta * oddSecondKindAngularMode m theta) =
      2 * rho * (1 - rho ^ (2 * m)) / (1 - rho ^ 2) := by
  rw [integral_platformPoisson_oddSecondKind_eq_power_sum hrho0 hrho1,
    odd_power_sum_closed_form hrho0 hrho1]
  field_simp [Real.pi_ne_zero]

/-- The normalized unweighted mean of `U_(2m)(cos θ)` is one. -/
theorem one_div_pi_mul_integral_evenSecondKind (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi, evenSecondKindAngularMode m theta) = 1 := by
  have h := one_div_pi_mul_integral_platformPoisson_evenSecondKind
    (rho := 0) (by norm_num) (by norm_num) m
  simpa [platformPoissonKernel, show 2 * m + 2 ≠ 0 by omega] using! h

/-- The normalized unweighted mean of `U_(2m-1)(cos θ)` is zero. -/
theorem one_div_pi_mul_integral_oddSecondKind (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi, oddSecondKindAngularMode m theta) = 0 := by
  have h := one_div_pi_mul_integral_platformPoisson_oddSecondKind
    (rho := 0) (by norm_num) (by norm_num) m
  simpa [platformPoissonKernel] using! h

end

end Erdos1038
