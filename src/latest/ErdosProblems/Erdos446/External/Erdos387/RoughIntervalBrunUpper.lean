/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos446.External.Erdos387.RoughBrunApproximation
import ErdosProblems.Erdos387.RoughHarmonicEstimate

/-!
# A sharp finite upper sieve for rough intervals

The minimum-prime-factor injection gives a useful completely elementary
bound for rough intervals, but loses an extra rough harmonic mass.  The
zero Fourier mode in the convenient-factor argument needs the usual
one-dimensional upper-bound sieve instead.  This file records that finite
argument with all truncation and endpoint losses explicit.
-/

namespace Erdos387

open scoped BigOperators

open Finset Nat Real

namespace RoughBrun

/-- The one-dimensional sieve Euler product is exactly the primorial
density through `z - 1`. -/
theorem roughFiniteEulerProduct_eq_preSieveSingularSeries (z : ℕ) :
    finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
        (fun p ↦ binomialSieveNu 1 p) =
      BoundedGaps.Maynard.preSieveSingularSeries (z - 1) := by
  classical
  have hprimes : (sievePrimeProduct 1 z).primeFactors =
      Nat.primesLE (z - 1) := by
    ext p
    constructor
    · intro hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDvd := Nat.dvd_of_mem_primeFactors hp
      have hpSieve := mem_sievePrimes.mp
        (prime_mem_sievePrimes_of_dvd_product hpPrime hpDvd)
      exact Nat.mem_primesLE.mpr
        ⟨Nat.le_sub_one_of_lt hpSieve.2.2, hpPrime⟩
    · intro hp
      have hpData := Nat.mem_primesLE.mp hp
      have hpz : p < z := by
        by_cases hz : z = 0
        · subst z
          exfalso
          have := hpData.2.two_le
          omega
        · exact hpData.1.trans_lt (Nat.sub_lt (Nat.pos_of_ne_zero hz) (by norm_num))
      have hpMem : p ∈ sievePrimes 1 z :=
        mem_sievePrimes.mpr ⟨hpData.2, hpData.2.one_lt, hpz⟩
      have hpDvd : p ∣ sievePrimeProduct 1 z := by
        exact Finset.dvd_prod_of_mem id hpMem
      exact Nat.mem_primeFactors.mpr
        ⟨hpData.2, hpDvd, (sievePrimeProduct_pos 1 z).ne'⟩
  rw [hprimes]
  unfold finiteEulerProduct BoundedGaps.Maynard.preSieveSingularSeries
  apply Finset.prod_congr rfl
  intro p hp
  change 1 - binomialSieveNu 1 p = 1 - 1 / (p : ℝ)
  rw [binomialSieveNu_prime (Nat.prime_of_mem_primesLE hp)]
  ring

/-- The primorial-density estimate gives the sharp `1 / log z` upper
bound for the one-dimensional sieve Euler product. -/
theorem roughFiniteEulerProduct_le_inv_log
    {z : ℕ} (hz : 2 ≤ z) :
    finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
        (fun p ↦ binomialSieveNu 1 p) ≤
      (Real.log (z : ℝ))⁻¹ := by
  rw [roughFiniteEulerProduct_eq_preSieveSingularSeries]
  have hzSub : z - 1 + 1 = z := by omega
  have hlogPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have h := RoughHarmonic.log_mul_preSieveSingularSeries_le_one (z - 1)
  rw [hzSub] at h
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hlogPos).2
  nlinarith

/-- A finite upper-bound Brun sieve for one rough interval.  The first term
has the source-faithful density `1 / log z`; the second is the explicit
CRT endpoint loss from the truncated divisor sum. -/
theorem card_roughPositiveIoc_le_brunDensity_add_endpoint
    {z A U L : ℕ} (hAU : A ≤ U) (hz : 2 ≤ z) (hL : Even L)
    (htail :
      2 * brunSubsetTail (sievePrimeProduct 1 z).primeFactors
          (fun p ↦ binomialSieveNu 1 p) L ≤
        finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
          (fun p ↦ binomialSieveNu 1 p)) :
    ((RoughHarmonic.roughPositiveIoc z A U).card : ℝ) ≤
      ((Finset.Ioc A U).card : ℝ) *
          (3 / (2 * Real.log (z : ℝ))) +
        2 * (z ^ L + 1 : ℕ) := by
  let s := intervalSieve z A U
  let V := finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
    (fun p ↦ binomialSieveNu 1 p)
  have hsieve := brunUpperBound s hL
  have hmain :=
    (boundingSieve_brunMainSums_half_threeHalves s L htail).2
  have herr := intervalSieve_brunErrSum_le hAU (by omega : 1 ≤ z) (L := L)
  have hV := roughFiniteEulerProduct_le_inv_log hz
  have hmass : 0 ≤ s.totalMass := by
    change 0 ≤ ((Finset.Ioc A U).card : ℝ)
    positivity
  have hlogPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hmainLog : s.mainSum (brunUpperWeight L) ≤
      3 / (2 * Real.log (z : ℝ)) := by
    calc
      s.mainSum (brunUpperWeight L) ≤ 3 * V / 2 := by
        simpa only [s, V, intervalSieve] using hmain
      _ ≤ 3 * (Real.log (z : ℝ))⁻¹ / 2 := by gcongr
      _ = 3 / (2 * Real.log (z : ℝ)) := by
        field_simp
  rw [intervalSieve_siftedSum] at hsieve
  calc
    ((RoughHarmonic.roughPositiveIoc z A U).card : ℝ) ≤
        s.totalMass * s.mainSum (brunUpperWeight L) +
          s.errSum (brunUpperWeight L) := hsieve
    _ ≤ s.totalMass * (3 / (2 * Real.log (z : ℝ))) +
          2 * (z ^ L + 1 : ℕ) := by
      gcongr
    _ = ((Finset.Ioc A U).card : ℝ) *
          (3 / (2 * Real.log (z : ℝ))) +
        2 * (z ^ L + 1 : ℕ) := by rfl

/-- A version with the interval length written as a natural difference. -/
theorem card_roughPositiveIoc_le_brunDensity_add_endpoint'
    {z A U L : ℕ} (hAU : A ≤ U) (hz : 2 ≤ z) (hL : Even L)
    (htail :
      2 * brunSubsetTail (sievePrimeProduct 1 z).primeFactors
          (fun p ↦ binomialSieveNu 1 p) L ≤
        finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
          (fun p ↦ binomialSieveNu 1 p)) :
    ((RoughHarmonic.roughPositiveIoc z A U).card : ℝ) ≤
      ((U - A : ℕ) : ℝ) * (3 / (2 * Real.log (z : ℝ))) +
        2 * (z ^ L + 1 : ℕ) := by
  simpa using
    (card_roughPositiveIoc_le_brunDensity_add_endpoint hAU hz hL htail)

end RoughBrun

end Erdos387
