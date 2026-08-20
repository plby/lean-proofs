/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SieveFamilyLower

/-!
# Erdős Problem 446: an exact finite rough-factor sieve

This file supplies the finite CRT statement used at the first stage of
Ford's fixed-multiplicity argument.  `roughAt N b` says that `b` has no
prime divisor at most `N`.  Its period is the product of those primes.
After a fixed factor `c` has been extracted, the set of integers `c*b` with
`b` rough has density exactly the small-prime Euler product divided by `c`.

The result is an equality, rather than an asymptotic sieve estimate.  It is
therefore suitable as the arithmetic core of the lower rough-number sieve;
the Mertens estimate for the Euler product is inserted only afterwards.
-/

namespace Erdos446

open Filter Finset Set Real
open scoped BigOperators Topology

/-- Product of all primes at most `N`; this is a period for `roughAt N`. -/
def roughPeriod (N : ℕ) : ℕ := ∏ p ∈ primesUpTo N, p

theorem roughPeriod_pos (N : ℕ) : 0 < roughPeriod N := by
  unfold roughPeriod
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

theorem prime_dvd_roughPeriod {N p : ℕ} (hp : p ∈ primesUpTo N) :
    p ∣ roughPeriod N := by
  exact Finset.dvd_prod_of_mem (fun q : ℕ ↦ q) hp

/-- An integer is `N`-rough when no prime at most `N` divides it. -/
def roughAt (N b : ℕ) : Prop := primePattern N b = ∅

instance roughAtDecidable (N b : ℕ) : Decidable (roughAt N b) := by
  unfold roughAt
  infer_instance

theorem roughAt_iff {N b : ℕ} :
    roughAt N b ↔ ∀ p ∈ primesUpTo N, ¬ p ∣ b := by
  classical
  constructor
  · intro h p hp hpb
    let q : PrimeIndex N := ⟨p, hp⟩
    have hq : q ∈ primePattern N b := mem_primePattern_iff.mpr hpb
    rw [h] at hq
    simpa using hq
  · intro h
    ext q
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_primePattern_iff]
    exact h q.1 q.2

theorem primePattern_add_roughPeriod (N b : ℕ) :
    primePattern N (b + roughPeriod N) = primePattern N b := by
  ext p
  rw [mem_primePattern_iff, mem_primePattern_iff]
  exact (Nat.dvd_add_iff_left (prime_dvd_roughPeriod p.2)).symm

theorem roughAt_add_roughPeriod (N b : ℕ) :
    roughAt N (b + roughPeriod N) ↔ roughAt N b := by
  rw [roughAt, roughAt, primePattern_add_roughPeriod]

theorem roughAt_periodic (N : ℕ) :
    Function.Periodic (roughAt N) (roughPeriod N) := by
  intro b
  exact propext (roughAt_add_roughPeriod N b)

/-- The density of rough integers is the finite Euler product. -/
theorem roughAt_hasDensity (N : ℕ) :
    ({b : ℕ | roughAt N b} : Set ℕ).HasDensity
      (smallPrimeEulerDensity N) := by
  have h := primePattern_eq_hasDensity N ∅
  have hempty : primePatternWeight N ∅ = smallPrimeEulerDensity N := by
    unfold primePatternWeight Erdos697.Bernoulli.weight
    simp [smallPrimeEulerDensity]
  simpa [roughAt, hempty] using h

/-- Integers obtained after extracting the fixed factor `c` and leaving an
`N`-rough quotient.  The quotient is written canonically as `n / c`. -/
def roughFactorEvent (N c : ℕ) : Set ℕ :=
  {n | c ∣ n ∧ roughAt N (n / c)}

instance roughFactorEventDecidable (N c n : ℕ) :
    Decidable (n ∈ roughFactorEvent N c) := by
  unfold roughFactorEvent
  infer_instance

theorem mem_roughFactorEvent_iff {N c n : ℕ} :
    n ∈ roughFactorEvent N c ↔ c ∣ n ∧ roughAt N (n / c) := by
  rfl

theorem mem_roughFactorEvent_mul {N c b : ℕ} (hc : 0 < c) :
    c * b ∈ roughFactorEvent N c ↔ roughAt N b := by
  rw [mem_roughFactorEvent_iff]
  simp [hc]

theorem roughFactorEvent_periodic (N c : ℕ) (hc : 0 < c) :
    Function.Periodic (fun n ↦ n ∈ roughFactorEvent N c)
      (c * roughPeriod N) := by
  intro n
  apply propext
  change (n + c * roughPeriod N ∈ roughFactorEvent N c) ↔
    n ∈ roughFactorEvent N c
  rw [mem_roughFactorEvent_iff, mem_roughFactorEvent_iff]
  constructor
  · rintro ⟨hcshift, hrough⟩
    have hcprod : c ∣ c * roughPeriod N := dvd_mul_right c _
    have hcn : c ∣ n := (Nat.dvd_add_iff_left hcprod).mpr hcshift
    refine ⟨hcn, ?_⟩
    rw [Nat.add_div_of_dvd_right hcn, Nat.mul_div_cancel_left _ hc] at hrough
    exact (roughAt_add_roughPeriod N (n / c)).1 hrough
  · rintro ⟨hcn, hrough⟩
    have hcprod : c ∣ c * roughPeriod N := dvd_mul_right c _
    have hcshift : c ∣ n + c * roughPeriod N :=
      (Nat.dvd_add_iff_left hcprod).mp hcn
    refine ⟨hcshift, ?_⟩
    rw [Nat.add_div_of_dvd_right hcn, Nat.mul_div_cancel_left _ hc]
    exact (roughAt_add_roughPeriod N (n / c)).2 hrough

theorem filter_roughFactorEvent_one_period (N c : ℕ) (hc : 0 < c) :
    (Finset.range (c * roughPeriod N)).filter
        (fun n ↦ n ∈ roughFactorEvent N c) =
      ((Finset.range (roughPeriod N)).filter (roughAt N)).image
        (fun b ↦ c * b) := by
  classical
  ext n
  constructor
  · intro hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rcases hn with ⟨hnlt, hcn, hrough⟩
    refine Finset.mem_image.mpr ⟨n / c, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.div_lt_iff_lt_mul hc).2 (by simpa [mul_comm] using hnlt)
      · exact hrough
    · exact Nat.mul_div_cancel' hcn
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(Nat.mul_lt_mul_left hc).2 hb.1,
      (mem_roughFactorEvent_mul hc).2 hb.2⟩

theorem card_roughFactorEvent_one_period (N c : ℕ) (hc : 0 < c) :
    ((Finset.range (c * roughPeriod N)).filter
        (fun n ↦ n ∈ roughFactorEvent N c)).card =
      ((Finset.range (roughPeriod N)).filter (roughAt N)).card := by
  classical
  rw [filter_roughFactorEvent_one_period N c hc,
    Finset.card_image_of_injective]
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hc hxy

/-- Exact lower rough-number sieve after extraction of a fixed factor. -/
theorem roughFactorEvent_hasDensity (N c : ℕ) (hc : 0 < c) :
    (roughFactorEvent N c).HasDensity
      (smallPrimeEulerDensity N / (c : ℝ)) := by
  classical
  have hperiod := hasDensity_of_periodic
    (fun n ↦ n ∈ roughFactorEvent N c) (c * roughPeriod N)
    (Nat.mul_pos hc (roughPeriod_pos N))
    (roughFactorEvent_periodic N c hc)
  have hroughPeriod := hasDensity_of_periodic (roughAt N) (roughPeriod N)
    (roughPeriod_pos N) (roughAt_periodic N)
  have heq :
      ((((Finset.range (roughPeriod N)).filter (roughAt N)).card : ℝ) /
          (roughPeriod N : ℝ)) = smallPrimeEulerDensity N :=
    tendsto_nhds_unique hroughPeriod (roughAt_hasDensity N)
  rw [card_roughFactorEvent_one_period N c hc] at hperiod
  have harith :
      ((((Finset.range (roughPeriod N)).filter (roughAt N)).card : ℝ) /
          (c * roughPeriod N : ℝ)) =
        smallPrimeEulerDensity N / (c : ℝ) := by
    rw [← heq]
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have hQR : (roughPeriod N : ℝ) ≠ 0 := by
      exact_mod_cast (roughPeriod_pos N).ne'
    push_cast
    field_simp
  rw [Nat.cast_mul] at hperiod
  rw [harith] at hperiod
  simpa using hperiod

/-- Exact multiplication of a periodic count over complete periods. -/
theorem periodic_nat_count_mul_fixedRough
    (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : Function.Periodic p L) (q : ℕ) :
    ((Finset.range (q * L)).filter p).card =
      q * ((Finset.range L).filter p).card := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.range_add_eq_union, Finset.filter_union]
      rw [Finset.card_union_of_disjoint]
      · rw [ih]
        have hblock := Nat.filter_Ico_card_eq_of_periodic (q * L) L p hp
        have hmap :
            (Finset.range L).map (addLeftEmbedding (q * L)) =
              Finset.Ico (q * L) (q * L + L) := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp only [Finset.mem_range, Finset.mem_Ico,
              addLeftEmbedding_apply] at hy ⊢
            omega
          · intro hx
            rw [Finset.mem_Ico] at hx
            refine Finset.mem_map.mpr ⟨x - q * L, ?_, ?_⟩
            · simp
              omega
            · simp
              omega
        rw [hmap, hblock, Nat.count_eq_card_filter_range]
        ring
      · rw [Finset.disjoint_left]
        intro x hx hxl
        rcases Finset.mem_filter.mp hx with ⟨hxrange, _⟩
        rcases Finset.mem_filter.mp hxl with ⟨hxlmap, _⟩
        rcases Finset.mem_map.mp hxlmap with ⟨y, hy, rfl⟩
        simp only [Finset.mem_range, addLeftEmbedding_apply] at hxrange hy
        omega

/-- Complete-period count for the exact rough-factor cell. -/
theorem card_roughFactorEvent_completePeriods (N c q : ℕ) (hc : 0 < c) :
    ((Finset.range (q * (c * roughPeriod N))).filter
        (fun n ↦ n ∈ roughFactorEvent N c)).card =
      q * ((Finset.range (roughPeriod N)).filter (roughAt N)).card := by
  classical
  rw [periodic_nat_count_mul_fixedRough
    (fun n ↦ n ∈ roughFactorEvent N c) (c * roughPeriod N)
    (roughFactorEvent_periodic N c hc) q,
    card_roughFactorEvent_one_period N c hc]

/-- The factorization represented by `roughFactorEvent` is unique. -/
theorem roughFactor_unique {N c n b : ℕ} (hc : 0 < c)
    (hn : n ∈ roughFactorEvent N c) (hnb : n = c * b) :
    b = n / c ∧ roughAt N b := by
  have hcn : c ∣ n := hn.1
  have hb : b = n / c := by
    rw [hnb, Nat.mul_div_cancel_left _ hc]
  exact ⟨hb, hb.symm ▸ hn.2⟩

end Erdos446
