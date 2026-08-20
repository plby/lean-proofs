/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityRoughReduction
import ErdosProblems.Erdos446.IsolatedDivisors

/-!
# Erdős Problem 446: distinguished primes attached to isolated divisors

Ford obtains exact multiplicity by adjoining `r` distinct large primes to a
small factor.  Each large prime is placed in the multiplicative window
belonging to an isolated divisor.  The lemmas below formalize this finite
step.  In a dyadic interval, logarithmic `log 2`-isolation makes the divisor
attached to a fixed prime unique.  Distinct primes give distinct lifted
divisors, so `r` prime coordinates give exactly `r` interval divisors.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Divisors of `a` which, after multiplication by `p`, lie in `(y,z]`. -/
def primeLiftDivisors (a p y z : ℕ) : Finset ℕ :=
  a.divisors.filter fun d ↦ d * p ∈ Finset.Ioc y z

theorem mem_primeLiftDivisors {a p y z d : ℕ} :
    d ∈ primeLiftDivisors a p y z ↔
      d ∈ a.divisors ∧ d * p ∈ Finset.Ioc y z := by
  simp [primeLiftDivisors]

/-- In a dyadic interval, two divisors attached to the same positive prime
are within logarithmic distance `log 2`. -/
theorem log_distance_le_log_two_of_primeLifts
    {a p y d e : ℕ} (hy : 0 < y) (hp : 0 < p)
    (hd : d ∈ primeLiftDivisors a p y (2 * y))
    (he : e ∈ primeLiftDivisors a p y (2 * y)) :
    |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2 := by
  have hdDiv := (mem_primeLiftDivisors.mp hd).1
  have heDiv := (mem_primeLiftDivisors.mp he).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdDiv
  have hepos : 0 < e := Nat.pos_of_mem_divisors heDiv
  have hdIoc := (mem_primeLiftDivisors.mp hd).2
  have heIoc := (mem_primeLiftDivisors.mp he).2
  have hedNat : e < 2 * d := by
    have hmul : e * p < (2 * d) * p := by
      have htwo : 2 * y < 2 * (d * p) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2
          (Finset.mem_Ioc.mp hdIoc).1
      calc
        e * p ≤ 2 * y := (Finset.mem_Ioc.mp heIoc).2
        _ < 2 * (d * p) := htwo
        _ = (2 * d) * p := by simp [mul_assoc]
    exact (Nat.mul_lt_mul_right hp).mp (by simpa [mul_comm] using hmul)
  have hdeNat : d < 2 * e := by
    have hmul : d * p < (2 * e) * p := by
      have htwo : 2 * y < 2 * (e * p) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2
          (Finset.mem_Ioc.mp heIoc).1
      calc
        d * p ≤ 2 * y := (Finset.mem_Ioc.mp hdIoc).2
        _ < 2 * (e * p) := htwo
        _ = (2 * e) * p := by simp [mul_assoc]
    exact (Nat.mul_lt_mul_right hp).mp (by simpa [mul_comm] using hmul)
  have hed : (e : ℝ) ≤ 2 * d := by exact_mod_cast hedNat.le
  have hde : (d : ℝ) ≤ 2 * e := by exact_mod_cast hdeNat.le
  have hlogE : Real.log (e : ℝ) ≤ Real.log 2 + Real.log (d : ℝ) := by
    calc
      Real.log (e : ℝ) ≤ Real.log (2 * (d : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hepos) hed
      _ = Real.log 2 + Real.log (d : ℝ) := by
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hdpos.ne')]
  have hlogD : Real.log (d : ℝ) ≤ Real.log 2 + Real.log (e : ℝ) := by
    calc
      Real.log (d : ℝ) ≤ Real.log (2 * (e : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hdpos) hde
      _ = Real.log 2 + Real.log (e : ℝ) := by
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hepos.ne')]
  rw [abs_le]
  constructor <;> linarith

/-- A `log 2`-isolated divisor is the unique divisor which a fixed prime can
lift into the dyadic interval. -/
theorem primeLiftDivisors_eq_singleton_of_isolated
    {a p y d : ℕ} (hy : 0 < y) (hp : 0 < p)
    (hiso : d ∈ sigmaIsolatedDivisors a (Real.log 2))
    (hd : d ∈ primeLiftDivisors a p y (2 * y)) :
    primeLiftDivisors a p y (2 * y) = {d} := by
  ext e
  constructor
  · intro he
    have heDiv := (mem_primeLiftDivisors.mp he).1
    have hnear : e ∈ sigmaNeighborDivisors a d (Real.log 2) := by
      rw [mem_sigmaNeighborDivisors]
      exact ⟨heDiv, log_distance_le_log_two_of_primeLifts hy hp hd he⟩
    have hneighbors := (mem_sigmaIsolatedDivisors.mp hiso).2
    rw [hneighbors] at hnear
    simpa using hnear
  · intro he
    have hed : e = d := by simpa using he
    simpa [hed] using hd

/-- All interval divisors obtained from the distinguished prime coordinates. -/
def distinguishedLiftFamily (a : ℕ) (P : Finset ℕ) (y z : ℕ) :
    Finset ℕ :=
  P.biUnion fun p ↦ (primeLiftDivisors a p y z).image (fun d ↦ d * p)

theorem distinguishedLiftFamily_eq_image_of_singletons
    {a y z : ℕ} {P : Finset ℕ} {d : ℕ → ℕ}
    (hsingle : ∀ p ∈ P, primeLiftDivisors a p y z = {d p}) :
    distinguishedLiftFamily a P y z = P.image (fun p ↦ d p * p) := by
  classical
  ext n
  simp only [distinguishedLiftFamily, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, e, he, rfl⟩
    have : e = d p := by
      have he' : e ∈ ({d p} : Finset ℕ) := by simpa [hsingle p hp] using he
      simpa using he'
    subst e
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, hp, d p, ?_, rfl⟩
    rw [hsingle p hp]
    simp

/-- Products attached to distinct distinguished primes are distinct, as
long as none of those primes divides the small factor. -/
theorem distinguishedProducts_injectiveOn
    {a : ℕ} {P : Finset ℕ} {d : ℕ → ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hnmid : ∀ p ∈ P, ¬ p ∣ a)
    (hddiv : ∀ p ∈ P, d p ∈ a.divisors) :
    Set.InjOn (fun p ↦ d p * p) P := by
  intro p hpP q hqP hpq
  have hpPrime := hprime p hpP
  have hqPrime := hprime q hqP
  have hpdvd : p ∣ d q * q := by
    have hleft : p ∣ d p * p := dvd_mul_left p (d p)
    change d p * p = d q * q at hpq
    exact hpq ▸ hleft
  rcases hpPrime.dvd_mul.mp hpdvd with hpdq | hpqdiv
  · have hdqa : d q ∣ a := Nat.dvd_of_mem_divisors (hddiv q hqP)
    exact ((hnmid p hpP) (hpdq.trans hdqa)).elim
  · rcases (Nat.dvd_prime hqPrime).mp hpqdiv with hpone | hpeq
    · exact (hpPrime.ne_one hpone).elim
    · exact hpeq

/-- If each prime coordinate has one lifted divisor, the lifted family has
exactly as many elements as there are distinguished primes. -/
theorem card_distinguishedLiftFamily
    {a y z : ℕ} {P : Finset ℕ} {d : ℕ → ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hnmid : ∀ p ∈ P, ¬ p ∣ a)
    (hsingle : ∀ p ∈ P, primeLiftDivisors a p y z = {d p}) :
    (distinguishedLiftFamily a P y z).card = P.card := by
  classical
  rw [distinguishedLiftFamily_eq_image_of_singletons hsingle]
  apply Finset.card_image_iff.mpr
  exact distinguishedProducts_injectiveOn hprime hnmid fun p hp ↦ by
    have : d p ∈ primeLiftDivisors a p y z := by
      rw [hsingle p hp]
      simp
    exact (mem_primeLiftDivisors.mp this).1

/-- Exact `r`-divisor conclusion from the single-prime shape decomposition.
The shape equality is the elementary size-separation statement: every
divisor in the interval contains exactly one distinguished prime. -/
theorem divisorCountIoc_mul_primeProd_eq
    {a y z r : ℕ} {P : Finset ℕ} {d : ℕ → ℕ}
    (hPcard : P.card = r)
    (hprime : ∀ p ∈ P, p.Prime)
    (hnmid : ∀ p ∈ P, ¬ p ∣ a)
    (hsingle : ∀ p ∈ P, primeLiftDivisors a p y z = {d p})
    (hshape :
      (Finset.Ioc y z).filter (fun e ↦ e ∣ a * ∏ p ∈ P, p) =
        distinguishedLiftFamily a P y z) :
    divisorCountIoc y z (a * ∏ p ∈ P, p) = r := by
  rw [divisorCountIoc, hshape,
    card_distinguishedLiftFamily hprime hnmid hsingle, hPcard]

/-- Dyadic specialization using genuine logarithmically isolated divisors. -/
theorem divisorCountIoc_mul_primeProd_eq_of_isolated
    {a y r : ℕ} {P : Finset ℕ} {d : ℕ → ℕ}
    (hy : 0 < y) (hPcard : P.card = r)
    (hprime : ∀ p ∈ P, p.Prime)
    (hnmid : ∀ p ∈ P, ¬ p ∣ a)
    (hiso : ∀ p ∈ P, d p ∈ sigmaIsolatedDivisors a (Real.log 2))
    (hlift : ∀ p ∈ P, d p ∈ primeLiftDivisors a p y (2 * y))
    (hshape :
      (Finset.Ioc y (2 * y)).filter
          (fun e ↦ e ∣ a * ∏ p ∈ P, p) =
        distinguishedLiftFamily a P y (2 * y)) :
    divisorCountIoc y (2 * y) (a * ∏ p ∈ P, p) = r := by
  apply divisorCountIoc_mul_primeProd_eq hPcard hprime hnmid
  · intro p hp
    exact primeLiftDivisors_eq_singleton_of_isolated hy
      (hprime p hp).pos (hiso p hp) (hlift p hp)
  · exact hshape

end Erdos446
