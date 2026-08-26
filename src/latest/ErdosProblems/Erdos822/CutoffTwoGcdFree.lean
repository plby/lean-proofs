/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CoprimeTotientFilter
import ErdosProblems.Erdos822.OddSmoothClass

/-!
# The B4 filter at cutoff two

On the odd structured layer, asking that no prime above two divide both a
cofactor and its totient is exactly global coprimality with the totient.
This identifies the fixed-cutoff version of B4 with the earlier
`coprimeTotientOddCofactors` interface.
-/

namespace Erdos822

theorem coprime_totient_of_mem_largeGcdFree_two
    {N m : ℕ} (hm : m ∈ largeGcdFreeOddCofactors N 2) :
    Nat.Coprime m (Nat.totient m) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  rintro p hp hpgcd
  have hpm : p ∣ m := dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
  have hpφ : p ∣ Nat.totient m :=
    dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
  have hmOdd : Odd m := oddRawCofactors_odd
    (largeGcdFreeOddCofactors_subset_oddRaw N 2 hm)
  have hpne : p ≠ 2 := by
    intro hpeq
    subst p
    exact hmOdd.not_two_dvd_nat hpm
  have hpTwo : 2 < p := by
    have := hp.two_le
    omega
  exact (mem_largeGcdFreeOddCofactors_iff.mp hm).2
    p hp hpTwo ⟨hpm, hpφ⟩

theorem mem_largeGcdFree_two_of_coprime_totient
    {N m : ℕ} (hm : m ∈ oddRawCofactors N)
    (hcop : Nat.Coprime m (Nat.totient m)) :
    m ∈ largeGcdFreeOddCofactors N 2 := by
  rw [mem_largeGcdFreeOddCofactors_iff]
  refine ⟨hm, ?_⟩
  intro p hp hpTwo hboth
  exact hp.not_unit (Nat.eq_one_of_dvd_coprimes hcop hboth.1 hboth.2)

theorem largeGcdFreeOddCofactors_two_eq_coprimeTotient
    (N : ℕ) :
    largeGcdFreeOddCofactors N 2 = coprimeTotientOddCofactors N := by
  ext m
  constructor
  · intro hm
    rw [mem_coprimeTotientOddCofactors_iff]
    exact ⟨largeGcdFreeOddCofactors_subset_oddRaw N 2 hm,
      coprime_totient_of_mem_largeGcdFree_two hm⟩
  · intro hm
    have hmData := mem_coprimeTotientOddCofactors_iff.mp hm
    exact mem_largeGcdFree_two_of_coprime_totient hmData.1 hmData.2

/-- At cutoff two the squarefree correction is literal squarefreeness of
the (odd) shifted coefficient. -/
theorem mem_squarefreeLargeGcdFree_two_iff
    {N m : ℕ} (hN : 2 ≤ N) :
    m ∈ squarefreeLargeGcdFreeOddCofactors N 2 ↔
      m ∈ coprimeTotientOddCofactors N ∧
        Squarefree (shiftedTotient m) := by
  constructor
  · intro hm
    have hmLarge :=
      squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree N 2 hm
    have hmRaw := largeGcdFreeOddCofactors_subset_oddRaw N 2 hmLarge
    have hmOdd := oddRawCofactors_odd hmRaw
    have hmGe := oddRawCofactors_ge_pow_twenty_five hN hmRaw
    have hmTwo : 2 < m := by
      have hpow : 2 ^ 25 ≤ N ^ 25 := Nat.pow_le_pow_left hN 25
      norm_num at hpow
      omega
    refine ⟨?_, ?_⟩
    · rw [← largeGcdFreeOddCofactors_two_eq_coprimeTotient]
      exact hmLarge
    · rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpsq
      have hshiftOdd := shiftedTotient_odd_of_odd hmOdd hmTwo
      have hpne : p ≠ 2 := by
        intro hpeq
        subst p
        exact hshiftOdd.not_two_dvd_nat
          (dvd_trans (dvd_pow_self 2 (by norm_num)) hpsq)
      have hpTwo : 2 < p := by
        have := hp.two_le
        omega
      exact (mem_squarefreeLargeGcdFreeOddCofactors_iff.mp hm).2
        p hp hpTwo hpsq
  · rintro ⟨hm, hsq⟩
    rw [mem_squarefreeLargeGcdFreeOddCofactors_iff]
    refine ⟨?_, ?_⟩
    · rw [largeGcdFreeOddCofactors_two_eq_coprimeTotient]
      exact hm
    · intro p hp hpTwo hpsq
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp hpsq

end Erdos822
