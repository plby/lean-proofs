/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.WeightedKernelAssembly
import ErdosProblems.Erdos822.ShiftedTotientResidues

/-!
# The coprime-totient part of B4

For the fixed cutoff-two model, the paper's condition that
`gcd(m, φ(m))` has no prime factor above the cutoff becomes the concrete
condition `Nat.Coprime m (Nat.totient m)` on odd cofactors.  This file keeps
that condition as an honest finite filter and proves the local divisibility
facts needed by the common-divisor argument.
-/

namespace Erdos822

/-- Odd raw cofactors for which the cofactor and its totient are coprime. -/
def coprimeTotientOddCofactors (N : ℕ) : Finset ℕ :=
  (oddRawCofactors N).filter fun m => Nat.Coprime m (Nat.totient m)

@[simp]
theorem mem_coprimeTotientOddCofactors_iff {N m : ℕ} :
    m ∈ coprimeTotientOddCofactors N ↔
      m ∈ oddRawCofactors N ∧ Nat.Coprime m (Nat.totient m) := by
  simp [coprimeTotientOddCofactors]

theorem coprimeTotientOddCofactors_subset_oddRaw (N : ℕ) :
    coprimeTotientOddCofactors N ⊆ oddRawCofactors N := by
  intro m hm
  exact (mem_coprimeTotientOddCofactors_iff.mp hm).1

theorem coprimeTotientOddCofactors_pos {N m : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N) : 0 < m :=
  oddRawCofactors_pos (coprimeTotientOddCofactors_subset_oddRaw N hm)

theorem coprimeTotientOddCofactors_odd {N m : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N) : Odd m :=
  oddRawCofactors_odd (coprimeTotientOddCofactors_subset_oddRaw N hm)

/-- Coprimality with the totient passes from a number to every divisor. -/
theorem coprime_totient_of_dvd_of_coprime_totient
    {l m : ℕ} (hlm : l ∣ m) (hcop : Nat.Coprime m (Nat.totient m)) :
    Nat.Coprime l (Nat.totient l) := by
  exact Nat.Coprime.of_dvd hlm (Nat.totient_dvd_of_dvd hlm) hcop

/-- The common shifted coefficient is coprime to a B4 cofactor itself. -/
theorem shiftedCoefficientGcd_coprime_left_of_coprime_totient
    {m m' : ℕ} (hcop : Nat.Coprime m (Nat.totient m)) :
    Nat.Coprime (shiftedCoefficientGcd m m') m := by
  have hshift : shiftedCoefficientGcd m m' ∣ shiftedTotient m := by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_dvd_left _ _
  have hshiftCop : Nat.Coprime (shiftedTotient m) m := by
    have h := (Nat.coprime_add_self_left).2 hcop.symm
    simpa [shiftedTotient, Nat.add_comm] using h
  exact Nat.Coprime.of_dvd_left hshift hshiftCop

/-- The same common shifted coefficient is coprime to the cofactor's
totient. -/
theorem shiftedCoefficientGcd_coprime_totient_left_of_coprime_totient
    {m m' : ℕ} (hcop : Nat.Coprime m (Nat.totient m)) :
    Nat.Coprime (shiftedCoefficientGcd m m') (Nat.totient m) := by
  have hshift : shiftedCoefficientGcd m m' ∣ shiftedTotient m := by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_dvd_left _ _
  have hshiftCop : Nat.Coprime (shiftedTotient m) (Nat.totient m) := by
    exact (Nat.coprime_add_self_left).2 hcop
  exact Nat.Coprime.of_dvd_left hshift hshiftCop

/-- Hence every divisor `l` of a B4 cofactor is coprime to the common
shifted coefficient. -/
theorem shiftedCoefficientGcd_coprime_leftFactor_of_coprime_totient
    {m m' l : ℕ} (hlm : l ∣ m)
    (hcop : Nat.Coprime m (Nat.totient m)) :
    Nat.Coprime (shiftedCoefficientGcd m m') l := by
  exact Nat.Coprime.of_dvd_right hlm
    (shiftedCoefficientGcd_coprime_left_of_coprime_totient hcop)

/-- Its totient is coprime to the same common shifted coefficient as well. -/
theorem shiftedCoefficientGcd_coprime_totient_leftFactor_of_coprime_totient
    {m m' l : ℕ} (hlm : l ∣ m)
    (hcop : Nat.Coprime m (Nat.totient m)) :
    Nat.Coprime (shiftedCoefficientGcd m m') (Nat.totient l) := by
  exact Nat.Coprime.of_dvd_right (Nat.totient_dvd_of_dvd hlm)
    (shiftedCoefficientGcd_coprime_totient_left_of_coprime_totient hcop)

/-- A prime dividing both a coprime-totient number and its shifted totient
would also divide its totient, which is impossible. -/
theorem not_dvd_of_dvd_shiftedTotient_of_coprime_totient
    {p m : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime m (Nat.totient m))
    (hshift : p ∣ shiftedTotient m) :
    ¬ p ∣ m := by
  intro hpm
  have hphi : p ∣ Nat.totient m := by
    apply (Nat.dvd_add_iff_right hpm).mpr
    simpa [shiftedTotient] using hshift
  have hpone : p = 1 := Nat.eq_one_of_dvd_coprimes hcop hpm hphi
  exact hp.ne_one hpone

/-- Every prime factor of the common shifted coefficient is absent from a
coprime-totient cofactor. -/
theorem not_dvd_coprimeTotientCofactor_of_dvd_shiftedCoefficientGcd
    {N m m' p : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N)
    (hp : p.Prime)
    (hpg : p ∣ shiftedCoefficientGcd m m') :
    ¬ p ∣ m := by
  apply not_dvd_of_dvd_shiftedTotient_of_coprime_totient hp
    (mem_coprimeTotientOddCofactors_iff.mp hm).2
  exact dvd_trans hpg (by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_dvd_left _ _)

/-- If `m = l*q` is coprime to its totient, then every prime factor of the
common shifted coefficient is absent already from `l`. -/
theorem not_dvd_leftFactor_of_dvd_shiftedCoefficientGcd
    {N m m' l q p : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N)
    (hp : p.Prime)
    (hpg : p ∣ shiftedCoefficientGcd m m')
    (hmlq : m = l * q) :
    ¬ p ∣ l := by
  intro hpl
  exact (not_dvd_coprimeTotientCofactor_of_dvd_shiftedCoefficientGcd
    hm hp hpg) (by
      rw [hmlq]
      exact dvd_mul_of_dvd_left hpl q)

/-- Consequently the linear coefficient `l + φ(l)` is invertible at every
prime factor of a supported common shifted coefficient. -/
theorem not_dvd_shiftedTotient_leftFactor_of_dvd_shiftedCoefficientGcd
    {N m m' l q p : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N)
    (hp : p.Prime) (hq : q.Prime)
    (hpg : p ∣ shiftedCoefficientGcd m m')
    (hmlq : m = l * q) (hql : ¬ q ∣ l) :
    ¬ p ∣ shiftedTotient l := by
  have hpl : ¬ p ∣ l :=
    not_dvd_leftFactor_of_dvd_shiftedCoefficientGcd hm hp hpg hmlq
  apply not_dvd_shiftedTotient_of_dvd_shiftedTotient_mul_prime
    hq hql hpl
  rw [← hmlq]
  exact dvd_trans hpg (by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_dvd_left _ _)

/-- Shifted totients of sufficiently large odd cofactors are odd. -/
theorem shiftedTotient_odd_of_odd_of_two_lt
    {m : ℕ} (hmOdd : Odd m) (hm : 2 < m) :
    Odd (shiftedTotient m) := by
  unfold shiftedTotient
  exact hmOdd.add_even (Nat.totient_even hm)

/-- Thus the common shifted coefficient of two sufficiently large odd
cofactors is odd. -/
theorem shiftedCoefficientGcd_odd_of_odd_of_two_lt
    {m m' : ℕ} (hmOdd : Odd m) (hm : 2 < m) :
    Odd (shiftedCoefficientGcd m m') := by
  unfold shiftedCoefficientGcd
  exact Odd.of_dvd_nat
    (shiftedTotient_odd_of_odd_of_two_lt hmOdd hm)
    (Nat.gcd_dvd_left _ _)

/-- Prime factors of that common coefficient are therefore odd primes. -/
theorem prime_odd_of_dvd_shiftedCoefficientGcd_of_odd
    {m m' p : ℕ} (_hp : p.Prime)
    (hmOdd : Odd m) (_hm'Odd : Odd m')
    (hm : 2 < m) (_hm' : 2 < m')
    (hpg : p ∣ shiftedCoefficientGcd m m') :
    Odd p := by
  exact Odd.of_dvd_nat
    (shiftedCoefficientGcd_odd_of_odd_of_two_lt hmOdd hm) hpg

end Erdos822
