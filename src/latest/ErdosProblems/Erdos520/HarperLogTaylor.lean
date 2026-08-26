import ErdosProblems.Erdos520.HarperEulerProduct
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem520

/-!
# Taylor control for one Rademacher Euler factor

This is the deterministic local analytic layer in the kernel-level Harper
specialization.  We use the complex prime term

`epsilon_p * p^(-1/2-it)`

and Mathlib's proved logarithm remainder estimate.  Restricting to `p >= 4`
makes its norm at most `1/2`, so the quadratic logarithmic approximation has
an explicit cubic error.  No probabilistic or prime-distribution input is
used in this file.
-/

/-- The complex perturbation in the Rademacher Euler factor
`1 + epsilon_p * p^(-1/2-it)`, written with real trigonometric functions. -/
noncomputable def harperComplexPrimeTerm
    (omega : Omega) (p : ℕ) (t : ℝ) : ℂ :=
  ((ε omega p / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    Complex.exp
      ((-(t * Real.log (p : ℝ)) : ℝ) * Complex.I)

theorem norm_harperComplexPhase (u : ℝ) :
    ‖Complex.exp ((-u : ℝ) * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I (-u)

theorem norm_harperComplexPrimeTerm
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ‖harperComplexPrimeTerm omega p t‖ = (Real.sqrt (p : ℝ))⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [harperComplexPrimeTerm, norm_mul, norm_harperComplexPhase]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_div, abs_ε, abs_of_pos (Real.sqrt_pos.2 hpR)]
  simp

@[simp] theorem harperComplexPrimeTerm_re
    (omega : Omega) (p : ℕ) (t : ℝ) :
    (harperComplexPrimeTerm omega p t).re =
      ε omega p * Real.cos (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ) := by
  rw [harperComplexPrimeTerm, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.mul_re,
    Complex.ofReal_re, Complex.add_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, Complex.I_im, mul_one]
  ring

@[simp] theorem harperComplexPrimeTerm_im
    (omega : Omega) (p : ℕ) (t : ℝ) :
    (harperComplexPrimeTerm omega p t).im =
      -(ε omega p * Real.sin (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ)) := by
  rw [harperComplexPrimeTerm, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.mul_im,
    Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero]
  ring

/-- The real density used in `HarperEulerProduct` is exactly the squared
complex norm of `1 + epsilon_p p^(-1/2-it)`. -/
theorem harperEulerFactor_eq_normSq_complex
    (omega : Omega) (p : ℕ) (t : ℝ) :
    harperEulerFactor omega p t =
      ‖1 + harperComplexPrimeTerm omega p t‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re,
    harperComplexPrimeTerm_re, Complex.add_im, Complex.one_im,
    harperComplexPrimeTerm_im]
  unfold harperEulerFactor
  ring

theorem harperEulerFactor_pos
    (omega : Omega) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    0 < harperEulerFactor omega p t := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsqrtOne : (1 : ℝ) < Real.sqrt (p : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using! hpR
  have htermLt : ‖harperComplexPrimeTerm omega p t‖ < 1 := by
    rw [norm_harperComplexPrimeTerm omega hp.pos t]
    exact (inv_lt_one₀ (Real.sqrt_pos.2 (by positivity))).2 hsqrtOne
  have hne : 1 + harperComplexPrimeTerm omega p t ≠ 0 := by
    intro hzero
    have hneg : harperComplexPrimeTerm omega p t = -1 := by
      exact eq_neg_of_add_eq_zero_right hzero
    have hone : ‖harperComplexPrimeTerm omega p t‖ = 1 := by
      rw [hneg]
      norm_num
    linarith
  rw [harperEulerFactor_eq_normSq_complex]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

theorem norm_harperComplexPrimeTerm_le_half
    (omega : Omega) {p : ℕ} (hp : 4 ≤ p) (t : ℝ) :
    ‖harperComplexPrimeTerm omega p t‖ ≤ 1 / 2 := by
  rw [norm_harperComplexPrimeTerm omega (by omega) t]
  have hpR : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
    exact hp
  simpa [one_div] using! inv_anti₀ (by norm_num : (0 : ℝ) < 2) hsqrt

/-- The quadratic Taylor polynomial for `log (1 + z)`. -/
noncomputable def harperLogQuadratic (z : ℂ) : ℂ := z - z ^ 2 / 2

/-- Real part of the quadratic logarithmic approximation.  This is the
linear Rademacher increment plus the deterministic second harmonic that is
specific to the Rademacher model. -/
theorem harperLogQuadratic_primeTerm_re
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (harperLogQuadratic (harperComplexPrimeTerm omega p t)).re =
      ε omega p * Real.cos (t * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ) -
        Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * (p : ℝ)) := by
  let θ : ℝ := t * Real.log (p : ℝ)
  let a : ℝ := ε omega p / Real.sqrt (p : ℝ)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have haSq : a ^ 2 = (p : ℝ)⁻¹ := by
    dsimp [a]
    rw [div_pow, ε_sq, hsqrtSq]
    simp [one_div]
  unfold harperLogQuadratic
  rw [pow_two]
  simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.mul_im,
    harperComplexPrimeTerm_re, harperComplexPrimeTerm_im]
  norm_num [Complex.normSq]
  have hre : ε omega p * Real.cos (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ) = a * Real.cos θ := by
    dsimp [a, θ]
    ring
  have him : ε omega p * Real.sin (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ) = a * Real.sin θ := by
    dsimp [a, θ]
    ring
  rw [hre, him]
  change ((a * Real.cos θ) * (a * Real.cos θ) -
        (a * Real.sin θ) * (a * Real.sin θ)) * 2 / 4 =
      Real.cos (2 * θ) / (2 * (p : ℝ))
  rw [show Real.cos (2 * θ) =
      Real.cos θ ^ 2 - Real.sin θ ^ 2 by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]]
  rw [show a * Real.cos θ * (a * Real.cos θ) -
        a * Real.sin θ * (a * Real.sin θ) =
      a ^ 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) by ring, haSq]
  dsimp [a, θ]
  field_simp
  ring

/-- The real logarithmic increment of one critical Euler factor. -/
noncomputable def harperLogPrimeIncrement
    (omega : Omega) (p : ℕ) (t : ℝ) : ℝ :=
  (Complex.log (1 + harperComplexPrimeTerm omega p t)).re

/-- The complex-log definition is exactly half the logarithm of the real
squared density. -/
theorem harperLogPrimeIncrement_eq_half_log_factor
    (omega : Omega) (p : ℕ) (t : ℝ) :
    harperLogPrimeIncrement omega p t =
      (1 / 2 : ℝ) * Real.log (harperEulerFactor omega p t) := by
  rw [harperLogPrimeIncrement, Complex.log_re,
    harperEulerFactor_eq_normSq_complex, Real.log_pow]
  ring

theorem harperEulerDensity_pos
    (y : ℕ) (omega : Omega) (t : ℝ) :
    0 < harperEulerDensity y omega t := by
  unfold harperEulerDensity
  exact Finset.prod_pos fun p hp ↦
    harperEulerFactor_pos omega
      (Nat.prime_of_mem_primesBelow hp) t

/-- Exact logarithmic factorization of the finite Euler density. -/
theorem log_harperEulerDensity_eq_two_mul_sum_logIncrement
    (y : ℕ) (omega : Omega) (t : ℝ) :
    Real.log (harperEulerDensity y omega t) =
      2 * ∑ p ∈ (y + 1).primesBelow,
        harperLogPrimeIncrement omega p t := by
  unfold harperEulerDensity
  rw [Real.log_prod]
  · calc
      (∑ p ∈ (y + 1).primesBelow,
          Real.log (harperEulerFactor omega p t)) =
          ∑ p ∈ (y + 1).primesBelow,
            2 * harperLogPrimeIncrement omega p t := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [harperLogPrimeIncrement_eq_half_log_factor]
        ring
      _ = 2 * ∑ p ∈ (y + 1).primesBelow,
          harperLogPrimeIncrement omega p t := by
        rw [Finset.mul_sum]
  · intro p hp
    exact (harperEulerFactor_pos omega
      (Nat.prime_of_mem_primesBelow hp) t).ne'

/-- Explicit cubic remainder for the complex logarithm of one Euler factor. -/
theorem norm_log_one_add_harperPrimeTerm_sub_quadratic_le
    (omega : Omega) {p : ℕ} (hp : 4 ≤ p) (t : ℝ) :
    ‖Complex.log (1 + harperComplexPrimeTerm omega p t) -
        harperLogQuadratic (harperComplexPrimeTerm omega p t)‖ ≤
      (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let z := harperComplexPrimeTerm omega p t
  have hzhalf : ‖z‖ ≤ 1 / 2 :=
    norm_harperComplexPrimeTerm_le_half omega hp t
  have hzlt : ‖z‖ < 1 := hzhalf.trans_lt (by norm_num)
  have h := Complex.norm_log_sub_logTaylor_le 2 hzlt
  have hpoly : Complex.log (1 + z) - Complex.logTaylor 3 z =
      Complex.log (1 + z) - harperLogQuadratic z := by
    congr 1
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero,
      harperLogQuadratic]
    ring
  rw [hpoly] at h
  norm_num at h
  have hinv : (1 - ‖z‖)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ (by linarith [norm_nonneg z]) (by norm_num)).2
    linarith
  have hnorm := norm_harperComplexPrimeTerm omega (by omega : 0 < p) t
  calc
    ‖Complex.log (1 + z) - harperLogQuadratic z‖ ≤
        ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := h
    _ ≤ ‖z‖ ^ 3 * 2 / 3 := by
      gcongr
    _ = (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
      rw [hnorm]
      ring

/-- Scalar form of the one-prime expansion used in the tilted random-walk
calculation. -/
theorem abs_harperLogPrimeIncrement_sub_main_le
    (omega : Omega) {p : ℕ} (hp : 4 ≤ p) (t : ℝ) :
    |harperLogPrimeIncrement omega p t -
        (ε omega p * Real.cos (t * Real.log (p : ℝ)) /
            Real.sqrt (p : ℝ) -
          Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * (p : ℝ)))| ≤
      (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let z := harperComplexPrimeTerm omega p t
  let A := Complex.log (1 + z) - harperLogQuadratic z
  calc
    |harperLogPrimeIncrement omega p t -
        (ε omega p * Real.cos (t * Real.log (p : ℝ)) /
            Real.sqrt (p : ℝ) -
          Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * (p : ℝ)))| =
        |A.re| := by
      congr 1
      dsimp [A, z, harperLogPrimeIncrement]
      rw [harperLogQuadratic_primeTerm_re omega (by omega) t]
    _ ≤ ‖A‖ := Complex.abs_re_le_norm A
    _ ≤ (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
      exact norm_log_one_add_harperPrimeTerm_sub_quadratic_le
        omega hp t

/-- The cubic one-prime errors are absolutely summable even before
restricting the index to primes. -/
theorem summable_harperCubicScale :
    Summable (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
  have h := Real.summable_nat_rpow.mpr
    (by norm_num : (-3 / 2 : ℝ) < -1)
  convert! h using 1
  funext n
  rw [← Real.rpow_neg_one, ← Real.rpow_natCast,
    ← Real.rpow_mul (Real.sqrt_nonneg (n : ℝ)), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

end Problem520
end Erdos
