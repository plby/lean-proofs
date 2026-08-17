/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos697.Erdos697PrimeHarmonic
import ErdosProblems.Erdos697.Erdos697PrimeWindow

/-!
# Prime harmonic and Euler-product bounds for Erdős Problem 444

This file packages the one-sided consequences of reciprocal-prime Mertens
needed by the large-values argument.  The analytic input is the bounded-error
theorem proved in `Erdos697.PrimeHarmonic`; all window and Euler-product
estimates below are finite consequences of it.
-/

open scoped BigOperators

namespace Erdos444.PrimeBounds

noncomputable section

/-- The reciprocal-prime sum up to an inclusive natural cutoff. -/
abbrev primeHarmonic : ℕ → ℝ := Erdos697.PrimeHarmonic.sum

/-- Primes in the half-open window `(y, x]`. -/
abbrev primesInWindow : ℕ → ℕ → Finset ℕ := Erdos697.PrimeWindow.primes

/-- Reciprocal mass of the prime window `(y, x]`. -/
abbrev primeWindowMass : ℕ → ℕ → ℝ := Erdos697.PrimeWindow.reciprocalMass

/-- The inverse Euler product over primes at most `x`. -/
def smallPrimeEulerProduct (x : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE x, (1 - (1 : ℝ) / p)⁻¹

/-- A fixed nonnegative constant for the bounded-error reciprocal-prime
Mertens estimate. -/
def mertensConstant : ℝ :=
  Classical.choose Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem mertensConstant_nonneg : 0 ≤ mertensConstant :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).1

/-- Uniform bounded-error Mertens estimate, re-exported for the 444
development. -/
theorem abs_primeHarmonic_sub_log_log_le {x : ℕ} (hx : 2 ≤ x) :
    |primeHarmonic x - Real.log (Real.log (x : ℝ))| ≤ mertensConstant :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).2 x hx

/-- Upper one-sided reciprocal-prime Mertens estimate. -/
theorem primeHarmonic_le_log_log_add {x : ℕ} (hx : 2 ≤ x) :
    primeHarmonic x ≤ Real.log (Real.log (x : ℝ)) + mertensConstant := by
  have h := abs_primeHarmonic_sub_log_log_le hx
  rw [abs_le] at h
  linarith

/-- Lower one-sided reciprocal-prime Mertens estimate. -/
theorem log_log_sub_le_primeHarmonic {x : ℕ} (hx : 2 ≤ x) :
    Real.log (Real.log (x : ℝ)) - mertensConstant ≤ primeHarmonic x := by
  have h := abs_primeHarmonic_sub_log_log_le hx
  rw [abs_le] at h
  linarith

/-- A prime-window sum is the difference of its two prime-harmonic
prefixes. -/
theorem primeWindowMass_eq_sub {y x : ℕ} (hyx : y ≤ x) :
    primeWindowMass y x = primeHarmonic x - primeHarmonic y :=
  Erdos697.PrimeWindow.reciprocalMass_eq_sub hyx

theorem primeWindowMass_nonneg (y x : ℕ) : 0 ≤ primeWindowMass y x := by
  change 0 ≤ ∑ p ∈ Erdos697.PrimeWindow.primes y x, 1 / (p : ℝ)
  positivity

/-- Mertens' estimate on an arbitrary prime window, with a uniform explicit
error `2 * mertensConstant`. -/
theorem primeWindowMass_le_log_log_sub_add
    {y x : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    primeWindowMass y x ≤
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ)) +
        2 * mertensConstant := by
  rw [primeWindowMass_eq_sub hyx]
  have hx : 2 ≤ x := hy.trans hyx
  have hupper := primeHarmonic_le_log_log_add hx
  have hlower := log_log_sub_le_primeHarmonic hy
  linarith

/-- Coarse window bound used when only the upper cutoff matters. -/
theorem primeWindowMass_le_log_log_add
    {y x : ℕ} (hx : 2 ≤ x) (hyx : y ≤ x) :
    primeWindowMass y x ≤
      Real.log (Real.log (x : ℝ)) + mertensConstant := by
  rw [primeWindowMass_eq_sub hyx]
  have hy0 : 0 ≤ primeHarmonic y := by
    change 0 ≤ ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p
    positivity
  exact (sub_le_self _ hy0).trans (primeHarmonic_le_log_log_add hx)

/-- The quadratic reciprocal correction over primes is uniformly bounded. -/
theorem sum_primesLE_two_div_sq_le (x : ℕ) :
    (∑ p ∈ Nat.primesLE x, (2 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have h := Erdos697.PrimeWindow.squareReciprocalMass_le
    (L := 1) (U := x) (by norm_num)
  have hsets : Erdos697.PrimeWindow.primes 1 x = Nat.primesLE x := by
    ext p
    simp only [Erdos697.PrimeWindow.mem_primes, Nat.mem_primesLE]
    constructor
    · rintro ⟨hp1, hpx, hp⟩
      exact ⟨hpx, hp⟩
    · rintro ⟨hpx, hp⟩
      exact ⟨hp.one_lt, hpx, hp⟩
  rw [hsets] at h
  have h' :
      (∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 := by
    simpa using h
  calc
    (∑ p ∈ Nat.primesLE x, (2 : ℝ) / (p : ℝ) ^ 2) =
        2 * ∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h' (by norm_num)
    _ = 2 := by norm_num

/-- A sharp enough elementary estimate for a single inverse Euler factor.
The square correction is summable, so the coefficient of `1 / p` remains
one. -/
theorem eulerFactor_le_exp_reciprocal_add_square
    {p : ℕ} (hp : p.Prime) :
    (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp ((1 : ℝ) / p + 2 / (p : ℝ) ^ 2) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hpm1 : (0 : ℝ) < p - 1 := by linarith
  have hfactor :
      (1 - (1 : ℝ) / p)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
    field_simp
    ring
  have hcorrection :
      (1 : ℝ) / (p - 1) ≤ 1 / p + 2 / p ^ 2 := by
    rw [div_le_iff₀ hpm1]
    field_simp
    nlinarith
  calc
    (1 - (1 : ℝ) / p)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := hfactor
    _ ≤ Real.exp (1 / ((p : ℝ) - 1)) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / ((p : ℝ) - 1))
    _ ≤ Real.exp ((1 : ℝ) / p + 2 / (p : ℝ) ^ 2) :=
      Real.exp_monotone hcorrection

/-- Finite Euler-product logarithmic estimate before Mertens is inserted. -/
theorem smallPrimeEulerProduct_le_exp_primeHarmonic_add_two (x : ℕ) :
    smallPrimeEulerProduct x ≤ Real.exp (primeHarmonic x + 2) := by
  calc
    smallPrimeEulerProduct x ≤
        ∏ p ∈ Nat.primesLE x,
          Real.exp ((1 : ℝ) / p + 2 / (p : ℝ) ^ 2) := by
      unfold smallPrimeEulerProduct
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := (Nat.mem_primesLE.mp hp).2
        have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
          rw [sub_pos]
          exact (div_lt_one (by positivity)).2 hpR
        positivity
      · intro p hp
        exact eulerFactor_le_exp_reciprocal_add_square
          (Nat.mem_primesLE.mp hp).2
    _ = Real.exp
        (∑ p ∈ Nat.primesLE x,
          ((1 : ℝ) / p + 2 / (p : ℝ) ^ 2)) := by
      rw [← Real.exp_sum]
    _ = Real.exp
        (primeHarmonic x +
          ∑ p ∈ Nat.primesLE x, (2 : ℝ) / (p : ℝ) ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ Real.exp (primeHarmonic x + 2) := by
      apply Real.exp_monotone
      gcongr
      exact sum_primesLE_two_div_sq_le x

/-- Uniform `C * log x` upper bound for the inverse small-prime Euler
product.  The explicit constant is `exp (mertensConstant + 2)`. -/
theorem smallPrimeEulerProduct_le_const_mul_log
    {x : ℕ} (hx : 2 ≤ x) :
    smallPrimeEulerProduct x ≤
      Real.exp (mertensConstant + 2) * Real.log (x : ℝ) := by
  calc
    smallPrimeEulerProduct x ≤
        Real.exp (primeHarmonic x + 2) :=
      smallPrimeEulerProduct_le_exp_primeHarmonic_add_two x
    _ ≤ Real.exp
        (Real.log (Real.log (x : ℝ)) + mertensConstant + 2) := by
      apply Real.exp_monotone
      linarith [primeHarmonic_le_log_log_add hx]
    _ = Real.exp (mertensConstant + 2) * Real.log (x : ℝ) := by
      have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
      have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
      rw [show Real.log (Real.log (x : ℝ)) + mertensConstant + 2 =
          (mertensConstant + 2) + Real.log (Real.log (x : ℝ)) by ring,
        Real.exp_add, Real.exp_log hlogx]

end

end Erdos444.PrimeBounds
