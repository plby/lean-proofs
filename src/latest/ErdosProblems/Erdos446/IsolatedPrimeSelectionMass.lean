/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ElementaryMass
import ErdosProblems.Erdos446.FixedMultiplicityModuliMass
import ErdosProblems.Erdos446.IsolatedPrimeSupport

/-!
# Erdős Problem 446: selecting several isolated prime windows

The dyadic windows attached to distinct `log 2`-isolated divisors are
disjoint.  This file combines their reciprocal-prime lower bound with the
finite weighted sampling-without-replacement estimate.  The result is the
precise `r`th-power gain needed before forming Ford's exact-multiplicity
moduli.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The `r`-element outer-prime sets selected from all isolated dyadic
windows of `a`. -/
noncomputable def isolatedPrimeSubsets (y a r : ℕ) : Finset (Finset ℕ) :=
  (isolatedDyadicPrimeSupport y a).powersetCard r

theorem isolatedPrimeSubsetMass_eq_elementaryMass (y a r : ℕ) :
    (∑ P ∈ isolatedPrimeSubsets y a r,
        ∏ p ∈ P, 1 / (p : ℝ)) =
      elementaryMass (isolatedDyadicPrimeSupport y a)
        (fun p ↦ 1 / (p : ℝ)) r := by
  rfl

/-- A uniform small-atom condition turns the isolated-divisor count into
an `r`-element reciprocal prime mass.  The hypothesis is deliberately
independent of `I(a;log 2)`: if that count is nonzero it is at least one,
while if it vanishes the asserted lower bound is automatic. -/
theorem isolatedPrimeSubsetMass_lower
    {N y a r : ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hy : 0 < y) (ha : 0 < a) (hr : 1 ≤ r)
    (hscale : ∀ d ∈ a.divisors, N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
      1 / (8 * Real.log (y : ℝ))) :
    (((sigmaIsolatedCount a (Real.log 2) : ℝ) /
          (8 * Real.log (y : ℝ))) ^ r) / (r.factorial : ℝ) ≤
      ∑ P ∈ isolatedPrimeSubsets y a r,
        ∏ p ∈ P, 1 / (p : ℝ) := by
  let I : ℕ := sigmaIsolatedCount a (Real.log 2)
  let W : ℝ := isolatedDyadicPrimeMass y a
  let m : ℝ := (a : ℝ) / (y : ℝ)
  have hy3 : 3 ≤ y := by
    have hdone : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha.ne'
    exact hN.trans (by simpa using (hscale 1 hdone).1)
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hw : ∀ p ∈ isolatedDyadicPrimeSupport y a,
      0 ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ m := by
    intro p hp
    have hpPrime : p.Prime := by
      rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
      obtain ⟨d, hd, hpd⟩ := hp
      exact (mem_dyadicPrimes.mp hpd).2.2
    refine ⟨by positivity, ?_⟩
    exact isolatedDyadicPrimeSupport_atom_upper hy ha hp
  have hW : W = ∑ p ∈ isolatedDyadicPrimeSupport y a, 1 / (p : ℝ) := rfl
  by_cases hI : I = 0
  · have hleft : (((I : ℝ) / (8 * Real.log (y : ℝ))) ^ r) /
        (r.factorial : ℝ) = 0 := by
      rw [hI]
      norm_num [Nat.ne_zero_of_lt hr]
    rw [show sigmaIsolatedCount a (Real.log 2) = I by rfl,
      hleft, isolatedPrimeSubsetMass_eq_elementaryMass]
    exact elementaryMass_nonneg_of_mem
      (P := isolatedDyadicPrimeSupport y a)
      (w := fun p : ℕ ↦ 1 / (p : ℝ))
      (fun p hp ↦ (hw p hp).1) r
  · have hIpos : 1 ≤ I := Nat.one_le_iff_ne_zero.mpr hI
    have hmass : (I : ℝ) * ((1 / 4 : ℝ) / Real.log (y : ℝ)) ≤ W := by
      exact isolatedDyadicPrimeMass_lower_of_divisor_scales
        hN hprime ha hscale
    have hsmall : (r : ℝ) * m ≤ W / 2 := by
      calc
        (r : ℝ) * m ≤ 1 / (8 * Real.log (y : ℝ)) := hatom
        _ ≤ (I : ℝ) / (8 * Real.log (y : ℝ)) := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast hIpos
          · positivity
        _ = ((I : ℝ) * ((1 / 4 : ℝ) /
              Real.log (y : ℝ))) / 2 := by ring
        _ ≤ W / 2 := div_le_div_of_nonneg_right hmass (by norm_num)
    have hsample := half_total_pow_div_factorial_le_elementaryMass
      (isolatedDyadicPrimeSupport y a) (fun p : ℕ ↦ 1 / (p : ℝ))
      hW hw hsmall
    rw [← isolatedPrimeSubsetMass_eq_elementaryMass] at hsample
    have hbase : (I : ℝ) / (8 * Real.log (y : ℝ)) ≤ W / 2 := by
      calc
        (I : ℝ) / (8 * Real.log (y : ℝ)) =
            ((I : ℝ) * ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2 := by ring
        _ ≤ W / 2 := div_le_div_of_nonneg_right hmass (by norm_num)
    calc
      (((sigmaIsolatedCount a (Real.log 2) : ℝ) /
            (8 * Real.log (y : ℝ))) ^ r) / (r.factorial : ℝ) =
          (((I : ℝ) / (8 * Real.log (y : ℝ))) ^ r) /
            (r.factorial : ℝ) := by rfl
      _ ≤ ((W / 2) ^ r) / (r.factorial : ℝ) := by
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hbase r) (by positivity)
      _ ≤ ∑ P ∈ isolatedPrimeSubsets y a r,
          ∏ p ∈ P, 1 / (p : ℝ) := hsample

/-- Summed form of `isolatedPrimeSubsetMass_lower`: after the small/outer
factorization has been shown injective, the whole isolated-divisor moment
passes to the reciprocal mass of the constructed moduli with the explicit
factor `(8 log y)^{-r}/r!`. -/
theorem isolatedPowerMass_le_isolatedPrimeModuliMass
    {N y r : ℕ} {A : Finset ℕ}
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hy : 0 < y) (hr : 1 ≤ r)
    (hApos : ∀ a ∈ A, 0 < a)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ)))
    (hinj : Set.InjOn smallOuterModulus
      (smallOuterPairs A (fun a ↦ isolatedPrimeSubsets y a r))) :
    (((1 / (8 * Real.log (y : ℝ))) ^ r) /
          (r.factorial : ℝ)) *
        (∑ a ∈ A,
          ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ)) ≤
      ∑ c ∈ smallOuterModuli A (fun a ↦ isolatedPrimeSubsets y a r),
        1 / (c : ℝ) := by
  apply isolatedPowerMass_le_sum_reciprocal_smallOuterModuli
    A (fun a ↦ isolatedPrimeSubsets y a r) r
      (((1 / (8 * Real.log (y : ℝ))) ^ r) / (r.factorial : ℝ))
      hinj hApos
  intro a ha
  have hpoint := isolatedPrimeSubsetMass_lower hN hprime hy
    (hApos a ha) hr (hscale a ha) (hatom a ha)
  calc
    (((1 / (8 * Real.log (y : ℝ))) ^ r) / (r.factorial : ℝ)) *
          (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r =
        (((sigmaIsolatedCount a (Real.log 2) : ℝ) /
            (8 * Real.log (y : ℝ))) ^ r) / (r.factorial : ℝ) := by
      norm_num [div_pow, div_eq_mul_inv]
      ring
    _ ≤ ∑ P ∈ isolatedPrimeSubsets y a r,
          ∏ p ∈ P, 1 / (p : ℝ) := hpoint

end Erdos446
