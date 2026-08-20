/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PrimeDyadic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Erdős Problem 446: dyadic primes and divisor clusters

We apply a finite weighted second-moment inequality to the dyadic prime
intervals indexed by the divisors of `a`.  Their pairwise intersections can
occur only for the close divisor pairs counted by `closePairCount`.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

variable {X : Type*}

/-- Finite weighted Cauchy--Schwarz, with a natural-valued multiplicity. -/
theorem weighted_multiplicity_second_moment
    (s : Finset X) (w : X → ℝ) (r : X → ℕ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * (r x : ℝ)) ^ 2 ≤
      (∑ x ∈ s, w x) *
        (∑ x ∈ s, w x * (r x : ℝ) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · exact hw
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    have hxw := hw x hx
    nlinarith [sq_nonneg (w x - w x * (r x : ℝ) ^ 2)]

/-- The union of the dyadic prime intervals indexed by divisors of `a`. -/
def dyadicPrimeSupport (y a : ℕ) : Finset ℕ :=
  a.divisors.biUnion fun d ↦ dyadicPrimes (y / d)

/-- Number of divisor-indexed dyadic prime intervals containing `p`. -/
def dyadicPrimeMultiplicity (y a p : ℕ) : ℕ :=
  (a.divisors.filter fun d ↦ p ∈ dyadicPrimes (y / d)).card

theorem mem_dyadicPrimeSupport {y a p : ℕ} :
    p ∈ dyadicPrimeSupport y a ↔
      ∃ d ∈ a.divisors, p ∈ dyadicPrimes (y / d) := by
  simp [dyadicPrimeSupport]

theorem dyadicPrimeMultiplicity_pos_of_mem {y a p : ℕ}
    (hp : p ∈ dyadicPrimeSupport y a) :
    0 < dyadicPrimeMultiplicity y a p := by
  rw [mem_dyadicPrimeSupport] at hp
  obtain ⟨d, hd, hpd⟩ := hp
  exact Finset.card_pos.mpr
    ⟨d, Finset.mem_filter.mpr ⟨hd, hpd⟩⟩

theorem dyadicPrimes_subset_support (y a : ℕ) {d : ℕ}
    (hd : d ∈ a.divisors) :
    dyadicPrimes (y / d) ⊆ dyadicPrimeSupport y a := by
  intro p hp
  exact mem_dyadicPrimeSupport.mpr ⟨d, hd, hp⟩

/-- Every prime in the support is eligible for Ford's modulus construction. -/
theorem dyadicPrimeSupport_subset_eligiblePrimes {y a : ℕ} (ha : 0 < a) :
    dyadicPrimeSupport y a ⊆ eligiblePrimes y a := by
  intro p hp
  obtain ⟨d, hd, hp⟩ := mem_dyadicPrimeSupport.mp hp
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hpinfo := mem_dyadicPrimes.mp hp
  have hydp : y < d * p := by
    have := (Nat.div_lt_iff_lt_mul hdpos).mp hpinfo.1
    simpa [Nat.mul_comm] using this
  have hdp : d * p ≤ 2 * y := by
    calc
      d * p ≤ d * (2 * (y / d)) := Nat.mul_le_mul_left d hpinfo.2.1
      _ = 2 * (d * (y / d)) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.mul_div_le y d)
  exact mem_eligiblePrimes.mpr
    ⟨hpinfo.2.2,
      (Nat.le_mul_of_pos_left p hdpos).trans hdp, d, hd, hydp, hdp⟩

/-- The support reciprocal mass is bounded by the full eligible mass. -/
theorem dyadicPrimeSupport_mass_le_eligiblePrimeMass {y a : ℕ} (ha : 0 < a) :
    (∑ p ∈ dyadicPrimeSupport y a, 1 / (p : ℝ)) ≤
      eligiblePrimeMass y a := by
  rw [eligiblePrimeMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (dyadicPrimeSupport_subset_eligiblePrimes ha)
  intro p hp hnot
  positivity

/-- Double-counting incidences: the weighted multiplicity sum over the union
equals the sum of the individual reciprocal prime masses. -/
theorem sum_support_mul_multiplicity (y a : ℕ) :
    (∑ p ∈ dyadicPrimeSupport y a,
        (1 / (p : ℝ)) * (dyadicPrimeMultiplicity y a p : ℝ)) =
      ∑ d ∈ a.divisors, dyadicPrimeMass (y / d) := by
  classical
  have hcount (p : ℕ) :
      (dyadicPrimeMultiplicity y a p : ℝ) =
        ∑ d ∈ a.divisors,
          if p ∈ dyadicPrimes (y / d) then 1 else 0 := by
    unfold dyadicPrimeMultiplicity
    exact (Finset.sum_boole
      (R := ℝ) (fun d ↦ p ∈ dyadicPrimes (y / d)) a.divisors).symm
  simp_rw [hcount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [dyadicPrimeMass]
  have hsub := dyadicPrimes_subset_support y a hd
  calc
    (∑ p ∈ dyadicPrimeSupport y a,
        1 / (p : ℝ) * if p ∈ dyadicPrimes (y / d) then 1 else 0) =
        ∑ p ∈ dyadicPrimeSupport y a,
          if p ∈ dyadicPrimes (y / d) then 1 / (p : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            split <;> simp_all
    _ = ∑ p ∈ dyadicPrimes (y / d), 1 / (p : ℝ) := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hsub h, h⟩

/-- Reciprocal mass in an intersection of two divisor-indexed dyadic prime
intervals. -/
noncomputable def dyadicPrimeIntersectionMass (y d e : ℕ) : ℝ :=
  ∑ p ∈ dyadicPrimes (y / d) ∩ dyadicPrimes (y / e), 1 / (p : ℝ)

/-- Expanding the square of the incidence multiplicity gives the sum of all
pairwise intersection masses. -/
theorem sum_support_mul_multiplicity_sq (y a : ℕ) :
    (∑ p ∈ dyadicPrimeSupport y a,
        (1 / (p : ℝ)) * (dyadicPrimeMultiplicity y a p : ℝ) ^ 2) =
      ∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
        dyadicPrimeIntersectionMass y d e := by
  classical
  have hcount (p : ℕ) :
      (dyadicPrimeMultiplicity y a p : ℝ) =
        ∑ d ∈ a.divisors,
          if p ∈ dyadicPrimes (y / d) then 1 else 0 := by
    unfold dyadicPrimeMultiplicity
    exact (Finset.sum_boole
      (R := ℝ) (fun d ↦ p ∈ dyadicPrimes (y / d)) a.divisors).symm
  have hpoint (p : ℕ) :
      (1 / (p : ℝ)) * (dyadicPrimeMultiplicity y a p : ℝ) ^ 2 =
        ∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
          (1 / (p : ℝ)) *
            (if p ∈ dyadicPrimes (y / d) then 1 else 0) *
            (if p ∈ dyadicPrimes (y / e) then 1 else 0) := by
    rw [hcount, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    ring
  apply Eq.trans (Finset.sum_congr rfl fun p hp ↦ hpoint p)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [dyadicPrimeIntersectionMass]
  have hsubD := dyadicPrimes_subset_support y a hd
  have hsubE := dyadicPrimes_subset_support y a he
  calc
    (∑ p ∈ dyadicPrimeSupport y a,
        1 / (p : ℝ) *
          (if p ∈ dyadicPrimes (y / d) then 1 else 0) *
          (if p ∈ dyadicPrimes (y / e) then 1 else 0)) =
        ∑ p ∈ dyadicPrimeSupport y a,
          if p ∈ dyadicPrimes (y / d) ∩ dyadicPrimes (y / e)
          then 1 / (p : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hpd : p ∈ dyadicPrimes (y / d) <;>
              by_cases hpe : p ∈ dyadicPrimes (y / e) <;>
              simp [hpd, hpe]
    _ = ∑ p ∈ dyadicPrimes (y / d) ∩ dyadicPrimes (y / e),
          1 / (p : ℝ) := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hsubD h.1, h⟩

private theorem dyadic_mem_interval_bounds {y d p : ℕ} (hd : 0 < d)
    (hp : p ∈ dyadicPrimes (y / d)) :
    y < d * p ∧ d * p ≤ 2 * y := by
  have hpinfo := mem_dyadicPrimes.mp hp
  constructor
  · have h := (Nat.div_lt_iff_lt_mul hd).mp hpinfo.1
    simpa [Nat.mul_comm] using h
  · calc
      d * p ≤ d * (2 * (y / d)) := Nat.mul_le_mul_left d hpinfo.2.1
      _ = 2 * (d * (y / d)) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.mul_div_le y d)

/-- Intersecting dyadic prime intervals force their divisor indices to be
within a factor of two. -/
theorem close_of_mem_dyadicPrimes {y d e p : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hpd : p ∈ dyadicPrimes (y / d))
    (hpe : p ∈ dyadicPrimes (y / e)) :
    |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2 := by
  have hpPos : 0 < p := (mem_dyadicPrimes.mp hpd).2.2.pos
  have hdI := dyadic_mem_interval_bounds hd hpd
  have heI := dyadic_mem_interval_bounds he hpe
  have hed : e < 2 * d := by
    apply (Nat.mul_lt_mul_right hpPos).mp
    calc
      e * p ≤ 2 * y := heI.2
      _ < 2 * (d * p) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr hdI.1
      _ = (2 * d) * p := by ring
  have hde : d < 2 * e := by
    apply (Nat.mul_lt_mul_right hpPos).mp
    calc
      d * p ≤ 2 * y := hdI.2
      _ < 2 * (e * p) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr heI.1
      _ = (2 * e) * p := by ring
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hlogDE : Real.log (d : ℝ) ≤ Real.log 2 + Real.log (e : ℝ) := by
    calc
      Real.log (d : ℝ) ≤ Real.log (2 * e : ℕ) :=
        Real.log_le_log hdR (by exact_mod_cast hde.le)
      _ = Real.log 2 + Real.log (e : ℝ) := by
        norm_num [Nat.cast_mul]
        rw [Real.log_mul (by norm_num) heR.ne']
  have hlogED : Real.log (e : ℝ) ≤ Real.log 2 + Real.log (d : ℝ) := by
    calc
      Real.log (e : ℝ) ≤ Real.log (2 * d : ℕ) :=
        Real.log_le_log heR (by exact_mod_cast hed.le)
      _ = Real.log 2 + Real.log (d : ℝ) := by
        norm_num [Nat.cast_mul]
        rw [Real.log_mul (by norm_num) hdR.ne']
  rw [abs_le]
  constructor <;> linarith

/-- A pair intersection is empty unless the divisor pair is close. -/
theorem dyadicPrimes_inter_eq_empty_of_not_close {y d e : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hclose : ¬|Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2) :
    dyadicPrimes (y / d) ∩ dyadicPrimes (y / e) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hp' := Finset.mem_inter.mp hp
  exact hclose (close_of_mem_dyadicPrimes hd he hp'.1 hp'.2)

/-- Summed pairwise intersections are controlled by the close-pair count. -/
theorem sum_dyadicPrimeIntersectionMass_le
    {y a : ℕ} {M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hupper : ∀ d ∈ a.divisors, dyadicPrimeMass (y / d) ≤ M) :
    (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
        dyadicPrimeIntersectionMass y d e) ≤
      (closePairCount a : ℝ) * M := by
  classical
  calc
    (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
        dyadicPrimeIntersectionMass y d e) ≤
        ∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
          if |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2
          then M else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      by_cases hclose :
          |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2
      · simp only [hclose, if_true]
        rw [dyadicPrimeIntersectionMass]
        calc
          (∑ p ∈ dyadicPrimes (y / d) ∩ dyadicPrimes (y / e),
              1 / (p : ℝ)) ≤ dyadicPrimeMass (y / d) := by
            rw [dyadicPrimeMass]
            apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
            intro p hp hnot
            positivity
          _ ≤ M := hupper d hd
      · simp only [hclose, if_false]
        rw [dyadicPrimeIntersectionMass,
          dyadicPrimes_inter_eq_empty_of_not_close
            (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he) hclose]
        simp
    _ = (closePairCount a : ℝ) * M := by
      rw [← Finset.sum_product']
      simp only [closePairCount, closeDivisorPairs, Finset.card_filter]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro de hde
      by_cases hclose :
          |Real.log (de.1 : ℝ) - Real.log (de.2 : ℝ)| ≤ Real.log 2 <;>
        simp [hclose]

/-- The prime-support version of Ford's divisor-cluster second moment. -/
theorem prime_cluster_second_moment
    {y a : ℕ} {M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hupper : ∀ d ∈ a.divisors, dyadicPrimeMass (y / d) ≤ M) :
    (∑ d ∈ a.divisors, dyadicPrimeMass (y / d)) ^ 2 ≤
      eligiblePrimeMass y a * ((closePairCount a : ℝ) * M) := by
  have hcs := weighted_multiplicity_second_moment
    (dyadicPrimeSupport y a) (fun p ↦ 1 / (p : ℝ))
      (dyadicPrimeMultiplicity y a) (fun p hp ↦ by positivity)
  rw [sum_support_mul_multiplicity,
    sum_support_mul_multiplicity_sq] at hcs
  calc
    (∑ d ∈ a.divisors, dyadicPrimeMass (y / d)) ^ 2 ≤
        (∑ p ∈ dyadicPrimeSupport y a, 1 / (p : ℝ)) *
          (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
            dyadicPrimeIntersectionMass y d e) := hcs
    _ ≤ eligiblePrimeMass y a * ((closePairCount a : ℝ) * M) := by
      have hpairs : 0 ≤
          ∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
            dyadicPrimeIntersectionMass y d e := by
        apply Finset.sum_nonneg
        intro d hd
        apply Finset.sum_nonneg
        intro e he
        rw [dyadicPrimeIntersectionMass]
        positivity
      have helig : 0 ≤ eligiblePrimeMass y a := by
        rw [eligiblePrimeMass]
        positivity
      exact mul_le_mul
        (dyadicPrimeSupport_mass_le_eligiblePrimeMass ha)
        (sum_dyadicPrimeIntersectionMass_le ha hM hupper)
        hpairs helig

/-- A natural threshold after which both dyadic reciprocal-prime bounds hold. -/
theorem exists_uniform_dyadicPrimeMass_bounds :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ) := by
  have hb := eventually_dyadicPrimeMass_bounds
  rw [Filter.eventually_atTop] at hb
  obtain ⟨N₀, hN₀⟩ := hb
  refine ⟨max 3 N₀, by simp, ?_⟩
  intro x hx
  exact hN₀ x (le_trans (le_max_right 3 N₀) hx)

/-- Pointwise Ford bound for the eligible-prime mass.  The scale hypotheses
say that every divisor-indexed prime interval is beyond the PNT threshold
and has logarithm at least half of `log y`. -/
theorem eligiblePrimeMass_lower_of_divisor_scales
    {N y a : ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (ha : 0 < a)
    (hscale : ∀ d ∈ a.divisors, N ≤ y / d ∧ y ≤ (y / d) ^ 2) :
    ((a.divisors.card : ℝ) ^ 2) /
        (96 * (closePairCount a : ℝ) * Real.log (y : ℝ)) ≤
      eligiblePrimeMass y a := by
  have hy3 : 3 ≤ y := by
    have hdone : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha.ne'
    have hs := (hscale 1 hdone).1
    simpa using le_trans hN hs
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlocal (d : ℕ) (hd : d ∈ a.divisors) :
      (1 / 4 : ℝ) / Real.log (y : ℝ) ≤
          dyadicPrimeMass (y / d) ∧
        dyadicPrimeMass (y / d) ≤ 6 / Real.log (y : ℝ) := by
    have hs := hscale d hd
    have hx3 : 3 ≤ y / d := hN.trans hs.1
    have hxlog : 0 < Real.log (y / d : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y / d by omega))
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hxle : y / d ≤ y := Nat.div_le_self y d
    have hlogle : Real.log (y / d : ℕ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hxle
    have hloghalf : Real.log (y : ℝ) ≤
        2 * Real.log (y / d : ℕ) := by
      calc
        Real.log (y : ℝ) ≤ Real.log (((y / d) ^ 2 : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hs.2)
        _ = 2 * Real.log (y / d : ℕ) := by
          rw [Nat.cast_pow, Real.log_pow]
          norm_num
    have hp := hprime (y / d) hs.1
    constructor
    · exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 4)
        hxlog hlogle).trans hp.1
    · calc
        dyadicPrimeMass (y / d) ≤ 3 / Real.log (y / d : ℕ) := hp.2
        _ ≤ 6 / Real.log (y : ℝ) := by
          rw [div_le_div_iff₀ hxlog hylog]
          nlinarith
  have hsumLower :
      (a.divisors.card : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ)) ≤
        ∑ d ∈ a.divisors, dyadicPrimeMass (y / d) := by
    calc
      (a.divisors.card : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ)) =
          ∑ d ∈ a.divisors, (1 / 4 : ℝ) / Real.log (y : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ d ∈ a.divisors, dyadicPrimeMass (y / d) :=
        Finset.sum_le_sum fun d hd ↦ (hlocal d hd).1
  have hsumNonneg : 0 ≤
      ∑ d ∈ a.divisors, dyadicPrimeMass (y / d) := by
    apply Finset.sum_nonneg
    intro d hd
    exact le_trans (by positivity) (hlocal d hd).1
  have hleftNonneg : 0 ≤
      (a.divisors.card : ℝ) *
        ((1 / 4 : ℝ) / Real.log (y : ℝ)) := by positivity
  have hsquare :
      ((a.divisors.card : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ))) ^ 2 ≤
        (∑ d ∈ a.divisors, dyadicPrimeMass (y / d)) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hsumNonneg).mpr hsumLower
  have hmoment := prime_cluster_second_moment ha
    (show 0 ≤ 6 / Real.log (y : ℝ) by positivity)
    (fun d hd ↦ (hlocal d hd).2)
  have hWpos : (0 : ℝ) < closePairCount a := by
    exact_mod_cast lt_of_lt_of_le
      (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ha.ne'⟩)
      (card_divisors_le_closePairCount a)
  have helig : 0 ≤ eligiblePrimeMass y a := by
    rw [eligiblePrimeMass]
    positivity
  have hcombined :
      ((a.divisors.card : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ))) ^ 2 ≤
        eligiblePrimeMass y a *
          ((closePairCount a : ℝ) * (6 / Real.log (y : ℝ))) :=
    hsquare.trans hmoment
  rw [div_le_iff₀ (by positivity :
    0 < 96 * (closePairCount a : ℝ) * Real.log (y : ℝ))]
  field_simp [hylog.ne', hWpos.ne'] at hcombined ⊢
  nlinarith

end Erdos446
