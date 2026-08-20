/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisorMass
import ErdosProblems.Erdos446.PrimeCluster

/-!
# Erdős Problem 446: prime windows indexed by isolated divisors

At scale `log 2`, the dyadic prime windows belonging to distinct isolated
divisors are disjoint.  Their reciprocal mass is therefore the sum of the
individual dyadic prime masses, with no second-moment loss.  This is the
prime-selection input for Ford's prescribed-multiplicity construction.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The union of dyadic prime windows indexed only by `log 2`-isolated
divisors. -/
noncomputable def isolatedDyadicPrimeSupport (y a : ℕ) : Finset ℕ :=
  (sigmaIsolatedDivisors a (Real.log 2)).biUnion
    fun d ↦ dyadicPrimes (y / d)

noncomputable def isolatedDyadicPrimeMass (y a : ℕ) : ℝ :=
  ∑ p ∈ isolatedDyadicPrimeSupport y a, 1 / (p : ℝ)

theorem isolated_dyadic_window_unique
    {y a d e p : ℕ}
    (hd : d ∈ sigmaIsolatedDivisors a (Real.log 2))
    (he : e ∈ sigmaIsolatedDivisors a (Real.log 2))
    (hpd : p ∈ dyadicPrimes (y / d))
    (hpe : p ∈ dyadicPrimes (y / e)) :
    d = e := by
  have hddiv := (mem_sigmaIsolatedDivisors.mp hd).1
  have hediv := (mem_sigmaIsolatedDivisors.mp he).1
  have hclose := close_of_mem_dyadicPrimes
    (Nat.pos_of_mem_divisors hddiv) (Nat.pos_of_mem_divisors hediv) hpd hpe
  have hemem : e ∈ sigmaNeighborDivisors a d (Real.log 2) :=
    mem_sigmaNeighborDivisors.mpr ⟨hediv, hclose⟩
  rw [(mem_sigmaIsolatedDivisors.mp hd).2] at hemem
  have hed : e = d := by simpa using hemem
  exact hed.symm

theorem isolatedDyadicPrimeWindows_pairwiseDisjoint (y a : ℕ) :
    ((sigmaIsolatedDivisors a (Real.log 2) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun d ↦ (dyadicPrimes (y / d) : Set ℕ)) := by
  intro d hd e he hde
  change Disjoint (dyadicPrimes (y / d) : Set ℕ)
    (dyadicPrimes (y / e) : Set ℕ)
  rw [Set.disjoint_left]
  intro p hpd hpe
  exact hde (isolated_dyadic_window_unique hd he hpd hpe)

theorem isolatedDyadicPrimeMass_eq_sum (y a : ℕ) :
    isolatedDyadicPrimeMass y a =
      ∑ d ∈ sigmaIsolatedDivisors a (Real.log 2),
        dyadicPrimeMass (y / d) := by
  rw [isolatedDyadicPrimeMass, isolatedDyadicPrimeSupport,
    Finset.sum_biUnion]
  · rfl
  · intro d hd e he hde
    change Disjoint (dyadicPrimes (y / d)) (dyadicPrimes (y / e))
    rw [Finset.disjoint_left]
    intro p hpd hpe
    exact hde (isolated_dyadic_window_unique hd he hpd hpe)

theorem isolatedDyadicPrimeMass_lower_of_divisor_scales
    {N y a : ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (ha : 0 < a)
    (hscale : ∀ d ∈ a.divisors, N ≤ y / d ∧ y ≤ (y / d) ^ 2) :
    (sigmaIsolatedCount a (Real.log 2) : ℝ) *
        ((1 / 4 : ℝ) / Real.log (y : ℝ)) ≤
      isolatedDyadicPrimeMass y a := by
  have hy3 : 3 ≤ y := by
    have hdone : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha.ne'
    exact hN.trans (by simpa using (hscale 1 hdone).1)
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlocal (d : ℕ) (hd : d ∈ a.divisors) :
      (1 / 4 : ℝ) / Real.log (y : ℝ) ≤ dyadicPrimeMass (y / d) := by
    have hs := hscale d hd
    have hx3 : 3 ≤ y / d := hN.trans hs.1
    have hxlog : 0 < Real.log (y / d : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y / d by omega))
    have hxle : y / d ≤ y := Nat.div_le_self y d
    have hlogle : Real.log (y / d : ℕ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hxle
    exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hxlog hlogle).trans (hprime (y / d) hs.1)
  rw [isolatedDyadicPrimeMass_eq_sum]
  calc
    (sigmaIsolatedCount a (Real.log 2) : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ)) =
        ∑ _d ∈ sigmaIsolatedDivisors a (Real.log 2),
          (1 / 4 : ℝ) / Real.log (y : ℝ) := by
      simp [sigmaIsolatedCount, nsmul_eq_mul]
    _ ≤ ∑ d ∈ sigmaIsolatedDivisors a (Real.log 2),
          dyadicPrimeMass (y / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hlocal d (mem_sigmaIsolatedDivisors.mp hd).1

theorem isolatedDyadicPrimeSupport_atom_upper
    {y a p : ℕ} (hy : 0 < y) (ha : 0 < a)
    (hp : p ∈ isolatedDyadicPrimeSupport y a) :
    1 / (p : ℝ) ≤ (a : ℝ) / (y : ℝ) := by
  rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
  obtain ⟨d, hdIso, hpd⟩ := hp
  have hd := (mem_sigmaIsolatedDivisors.mp hdIso).1
  have hdPos := Nat.pos_of_mem_divisors hd
  have hpinfo := mem_dyadicPrimes.mp hpd
  have hinterval : y < d * p := by
    have h := (Nat.div_lt_iff_lt_mul hdPos).mp hpinfo.1
    simpa [Nat.mul_comm] using h
  have hda : d ≤ a := Nat.divisor_le hd
  have hpPos : 0 < p := (mem_dyadicPrimes.mp hpd).2.2.pos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hprod : (y : ℝ) < (a : ℝ) * (p : ℝ) := by
    exact_mod_cast hinterval.trans_le (Nat.mul_le_mul_right p hda)
  apply (div_le_div_iff₀ hpR hyR).2
  simpa using hprod.le

end Erdos446
