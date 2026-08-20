/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedPrimeSupport
import ErdosProblems.Erdos446.FixedMultiplicityIsolationRatio
import ErdosProblems.Erdos446.ElementaryMass

/-!
# Erdős Problem 446: selecting the separated outer primes

This module turns the reciprocal mass of the prime windows indexed by
isolated divisors into a reciprocal mass of `r`-element prime sets.  It also
records the exact arithmetic properties of every selected prime: it is
prime, it has a unique small divisor which moves it into `(y,2y]`, and under
Ford's small-factor size condition the selected primes are larger than the
small factor and pairwise multiplicatively separated.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The admissible unordered sets of `r` outer primes for a fixed small
factor. -/
noncomputable def isolatedOuterPrimeSets (y a r : ℕ) :
    Finset (Finset ℕ) :=
  (isolatedDyadicPrimeSupport y a).powersetCard r

theorem mem_isolatedOuterPrimeSets {y a r : ℕ} {P : Finset ℕ} :
    P ∈ isolatedOuterPrimeSets y a r ↔
      P ⊆ isolatedDyadicPrimeSupport y a ∧ P.card = r := by
  simp [isolatedOuterPrimeSets, Finset.mem_powersetCard]

/-- The reciprocal mass of the admissible outer-prime sets is exactly the
elementary symmetric mass of the isolated prime support. -/
theorem sum_isolatedOuterPrimeSets_eq_elementaryMass (y a r : ℕ) :
    (∑ P ∈ isolatedOuterPrimeSets y a r,
        ∏ p ∈ P, 1 / (p : ℝ)) =
      elementaryMass (isolatedDyadicPrimeSupport y a)
        (fun p ↦ 1 / (p : ℝ)) r := by
  rfl

/-- Weighted sampling without replacement on the isolated prime support.
The atom bound `a/y` is supplied by `isolatedDyadicPrimeSupport_atom_upper`.
-/
theorem isolatedOuterPrimeSets_mass_lower
    {y a r : ℕ} (hy : 0 < y) (ha : 0 < a)
    (hsmall : (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
      isolatedDyadicPrimeMass y a / 2) :
    (isolatedDyadicPrimeMass y a / 2) ^ r / (r.factorial : ℝ) ≤
      ∑ P ∈ isolatedOuterPrimeSets y a r,
        ∏ p ∈ P, 1 / (p : ℝ) := by
  rw [sum_isolatedOuterPrimeSets_eq_elementaryMass]
  apply half_total_pow_div_factorial_le_elementaryMass
    (isolatedDyadicPrimeSupport y a) (fun p ↦ 1 / (p : ℝ))
    (m := (a : ℝ) / (y : ℝ)) (W := isolatedDyadicPrimeMass y a)
  · rfl
  · intro p hp
    refine ⟨by positivity, ?_⟩
    exact isolatedDyadicPrimeSupport_atom_upper hy ha hp
  · exact hsmall

/-- Combining the PNT lower bound for every isolated window with elementary
sampling gives the explicit `I(a)^r / log(y)^r` selection mass. -/
theorem isolatedCount_pow_mass_lower
    {N y a r : ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (ha : 0 < a)
    (hscale : ∀ d ∈ a.divisors, N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hsmall : (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
      isolatedDyadicPrimeMass y a / 2) :
    (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
        ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
        (r.factorial : ℝ) ≤
      ∑ P ∈ isolatedOuterPrimeSets y a r,
        ∏ p ∈ P, 1 / (p : ℝ) := by
  have hy : 0 < y := by
    have hdone : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha.ne'
    have := (hscale 1 hdone).1
    omega
  have hW := isolatedDyadicPrimeMass_lower_of_divisor_scales
    hN hprime ha hscale
  have hW0 : 0 ≤ isolatedDyadicPrimeMass y a := by
    rw [isolatedDyadicPrimeMass]
    positivity
  have hbase :
      ((sigmaIsolatedCount a (Real.log 2) : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2 ≤
        isolatedDyadicPrimeMass y a / 2 :=
    div_le_div_of_nonneg_right hW (by norm_num)
  calc
    (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
          (r.factorial : ℝ) ≤
        (isolatedDyadicPrimeMass y a / 2) ^ r /
          (r.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hbase r
    _ ≤ ∑ P ∈ isolatedOuterPrimeSets y a r,
          ∏ p ∈ P, 1 / (p : ℝ) :=
      isolatedOuterPrimeSets_mass_lower hy ha hsmall

/-- Every prime in the isolated support has a unique divisor of `a` which
moves it into the dyadic target interval. -/
theorem exists_unique_eligible_isolated_divisor
    {y a p : ℕ} (ha : 0 < a)
    (hp : p ∈ isolatedDyadicPrimeSupport y a) :
    ∃ d ∈ sigmaIsolatedDivisors a (Real.log 2),
      y < d * p ∧ d * p ≤ 2 * y ∧
        ∀ e ∈ a.divisors, y < e * p → e * p ≤ 2 * y → e = d := by
  rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
  obtain ⟨d, hdIso, hpd⟩ := hp
  have hdDiv := (mem_sigmaIsolatedDivisors.mp hdIso).1
  have hdPos := Nat.pos_of_mem_divisors hdDiv
  have hpInfo := mem_dyadicPrimes.mp hpd
  have hpPos := hpInfo.2.2.pos
  have hdLower : y < d * p := by
    have h := (Nat.div_lt_iff_lt_mul hdPos).mp hpInfo.1
    simpa [Nat.mul_comm] using h
  have hdUpper : d * p ≤ 2 * y := by
    calc
      d * p ≤ d * (2 * (y / d)) := Nat.mul_le_mul_left d hpInfo.2.1
      _ = 2 * (d * (y / d)) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.mul_div_le y d)
  refine ⟨d, hdIso, hdLower, hdUpper, ?_⟩
  intro e heDiv heLower heUpper
  have hed : e < 2 * d := by
    apply (Nat.mul_lt_mul_right hpPos).mp
    calc
      e * p ≤ 2 * y := heUpper
      _ < 2 * (d * p) :=
        Nat.mul_lt_mul_of_pos_left hdLower (by omega : 0 < 2)
      _ = (2 * d) * p := by ring
  have hde : d < 2 * e := by
    apply (Nat.mul_lt_mul_right hpPos).mp
    calc
      d * p ≤ 2 * y := hdUpper
      _ < 2 * (e * p) :=
        Nat.mul_lt_mul_of_pos_left heLower (by omega : 0 < 2)
      _ = (2 * e) * p := by ring
  exact eq_of_mem_divisors_of_lt_two_mul_of_sigmaIsolated_log_two
    hdIso heDiv hed hde

theorem prime_of_mem_isolatedDyadicPrimeSupport
    {y a p : ℕ} (hp : p ∈ isolatedDyadicPrimeSupport y a) : p.Prime := by
  rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
  obtain ⟨d, hd, hpd⟩ := hp
  exact (mem_dyadicPrimes.mp hpd).2.2

/-- Every prime in the isolated dyadic support is at most the target upper
endpoint. -/
theorem le_two_mul_y_of_mem_isolatedDyadicPrimeSupport
    {y a p : ℕ} (hp : p ∈ isolatedDyadicPrimeSupport y a) :
    p ≤ 2 * y := by
  rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
  obtain ⟨d, hdIso, hpd⟩ := hp
  have hpInfo := mem_dyadicPrimes.mp hpd
  calc
    p ≤ 2 * (y / d) := hpInfo.2.1
    _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.div_le_self y d)

/-- If the small factor lies below the square-root scale, every selected
outer prime is larger than it. -/
theorem smallFactor_lt_of_mem_isolatedDyadicPrimeSupport
    {y a p : ℕ} (ha : 0 < a) (hay : a * a < y)
    (hp : p ∈ isolatedDyadicPrimeSupport y a) : a < p := by
  obtain ⟨d, hdIso, hdLower, hdUpper, hdUnique⟩ :=
    exists_unique_eligible_isolated_divisor ha hp
  have hdDiv := (mem_sigmaIsolatedDivisors.mp hdIso).1
  have hda : d ≤ a := Nat.divisor_le hdDiv
  by_contra hpa
  have hple : p ≤ a := Nat.le_of_not_gt hpa
  have hdp : d * p ≤ a * a := Nat.mul_le_mul hda hple
  omega

/-- Ford's `a^2 = o(y)` restriction makes products of two distinct selected
outer primes exceed the upper endpoint `2y`. -/
theorem two_mul_y_lt_mul_of_mem_isolatedDyadicPrimeSupport
    {y a p q : ℕ} (ha : 0 < a) (hy : 0 < y)
    (hasmall : 2 * a * a < y)
    (hp : p ∈ isolatedDyadicPrimeSupport y a)
    (hq : q ∈ isolatedDyadicPrimeSupport y a) :
    2 * y < p * q := by
  obtain ⟨d, hdIso, hdp, hdUpper, hdUnique⟩ :=
    exists_unique_eligible_isolated_divisor ha hp
  obtain ⟨e, heIso, heq, heUpper, heUnique⟩ :=
    exists_unique_eligible_isolated_divisor ha hq
  have hda : d ≤ a := Nat.divisor_le (mem_sigmaIsolatedDivisors.mp hdIso).1
  have hea : e ≤ a := Nat.divisor_le (mem_sigmaIsolatedDivisors.mp heIso).1
  have hyp : y < a * p := hdp.trans_le (Nat.mul_le_mul_right p hda)
  have hyq : y < a * q := heq.trans_le (Nat.mul_le_mul_right q hea)
  have haaPos : 0 < a * a := Nat.mul_pos ha ha
  have hleft : (2 * a * a) * y < y * y :=
    Nat.mul_lt_mul_of_pos_right hasmall hy
  have hright : y * y < (a * p) * (a * q) := by
    calc
      y * y < (a * p) * y := Nat.mul_lt_mul_of_pos_right hyp hy
      _ < (a * p) * (a * q) :=
        Nat.mul_lt_mul_of_pos_left hyq (Nat.mul_pos ha
          (prime_of_mem_isolatedDyadicPrimeSupport hp).pos)
  have hcancel : (a * a) * (2 * y) < (a * a) * (p * q) := by
    calc
      (a * a) * (2 * y) = (2 * a * a) * y := by ring
      _ < y * y := hleft
      _ < (a * p) * (a * q) := hright
      _ = (a * a) * (p * q) := by ring
  exact Nat.lt_of_mul_lt_mul_left hcancel

end Erdos446
