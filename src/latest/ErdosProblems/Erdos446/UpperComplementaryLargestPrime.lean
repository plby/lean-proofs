/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperPrimeClusterWindow

/-!
# Erdős Problem 446: complementary largest-prime selection

Ford's rough residual is nontrivial because the pivot is chosen from the
one of a divisor and its complementary divisor having the smaller largest
prime.  This file records the exact finite arithmetic statement.  In a
squarefree integer the two factors are coprime, so their largest primes are
distinct; the factorization from `UpperLargestPrimeShell` then has residual
part strictly larger than the pivot.
-/

namespace Erdos446

open Finset

noncomputable section

theorem complementaryDivisor_pos {n m : ℕ} (hn : 0 < n) (hm : m ∣ n) :
    0 < n / m := by
  have hmPos : 0 < m := Nat.pos_of_dvd_of_pos hm hn
  exact Nat.div_pos (Nat.le_of_dvd hn hm) hmPos

theorem complementaryDivisor_dvd {n m : ℕ} (hm : m ∣ n) :
    n / m ∣ n := by
  exact ⟨m, (Nat.div_mul_cancel hm).symm⟩

theorem divisor_coprime_complement_of_squarefree
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n) :
    m.Coprime (n / m) := by
  have hprod : m * (n / m) = n := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hm
  have hsq : Squarefree (m * (n / m)) := by
    rw [hprod]
    exact hn
  exact Nat.coprime_of_squarefree_mul hsq

theorem largestPrimeFactors_ne_of_complementary_squarefree
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n)
    (hmOne : 1 < m) (heOne : 1 < n / m) :
    Erdos469.largestPrimeFactor m ≠
      Erdos469.largestPrimeFactor (n / m) := by
  intro heq
  let p := Erdos469.largestPrimeFactor m
  have hpM := Erdos469.largestPrimeFactor_spec hmOne
  have hpE := Erdos469.largestPrimeFactor_spec heOne
  have hcop := divisor_coprime_complement_of_squarefree hn hm
  have hpdvdGcd : p ∣ Nat.gcd m (n / m) := by
    apply Nat.dvd_gcd hpM.dvd
    simpa [p, heq] using hpE.dvd
  have hpOne : p ∣ 1 := by simpa [hcop.gcd_eq_one] using hpdvdGcd
  exact hpM.prime.not_dvd_one hpOne

/-- Select the factor with smaller largest prime.  The two output factors
are the original divisor and its complement, in one order or the other. -/
theorem exists_ordered_complementary_factors
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n)
    (hmOne : 1 < m) (heOne : 1 < n / m) :
    ∃ s t : ℕ,
      s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
      (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
      Erdos469.largestPrimeFactor s <
        Erdos469.largestPrimeFactor t := by
  have heDvd := complementaryDivisor_dvd hm
  have hne := largestPrimeFactors_ne_of_complementary_squarefree
    hn hm hmOne heOne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨m, n / m, hm, heDvd, hmOne, heOne,
      Or.inl ⟨rfl, rfl⟩, hlt⟩
  · exact ⟨n / m, m, heDvd, hm, heOne, hmOne,
      Or.inr ⟨rfl, rfl⟩, hgt⟩

/-- Source-faithful squarefree shell factorization: the residual factor is
strictly larger than the chosen pivot prime. -/
theorem squarefree_complementary_largestPrime_shell
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n)
    (hmOne : 1 < m) (heOne : 1 < n / m) :
    ∃ s t p a b : ℕ,
      s ∣ n ∧ t ∣ n ∧ 1 < s ∧ 1 < t ∧
      (s = m ∧ t = n / m ∨ s = n / m ∧ t = m) ∧
      Erdos469.largestPrimeFactor s < Erdos469.largestPrimeFactor t ∧
      p = Erdos469.largestPrimeFactor s ∧
      a = fordLowerPrimePart n p ∧ b = fordUpperPrimePart n p ∧
      p.Prime ∧ 0 < a ∧ p < b ∧
      n = a * p * b ∧ Erdos387.IsZRough p b ∧
      s / p ∈ a.divisors ∧ s = (s / p) * p := by
  obtain ⟨s, t, hs, ht, hsOne, htOne, hst, hlt⟩ :=
    exists_ordered_complementary_factors hn hm hmOne heOne
  let p := Erdos469.largestPrimeFactor s
  let a := fordLowerPrimePart n p
  let b := fordUpperPrimePart n p
  have hshell := squarefree_largestPrime_shell hn hs hsOne
  have hpb : p < b :=
    largestPrimeFactor_lt_fordUpperPrimePart_of_complement
      hn hs hsOne ht htOne hlt
  refine ⟨s, t, p, a, b, hs, ht, hsOne, htOne, hst,
    hlt, rfl, rfl, rfl, hshell.1, hshell.2.2.1, hpb,
    hshell.2.2.2.2.1, hshell.2.2.2.2.2.1,
    hshell.2.2.2.2.2.2.1, hshell.2.2.2.2.2.2.2⟩

end

end Erdos446
