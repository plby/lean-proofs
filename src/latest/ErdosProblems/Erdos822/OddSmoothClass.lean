/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OddSmooth
import ErdosProblems.Erdos822.CommonDivisorSplit

/-!
# The unique smooth class at cutoff two

Every odd integer has trivial `2`-smooth part.  Consequently, for odd
cofactors above two, their shifted coefficients and their common shifted
coefficient gcd are entirely rough at cutoff two.  These identities are the
exact bridge from the fixed-cutoff collision partition to the rough-modulus
quadratic estimates.
-/

namespace Erdos822

/-- An odd integer has no nontrivial prime factor at most two, hence its
`2`-smooth part is one. -/
theorem smoothPart_two_eq_one_of_odd {n : ℕ} (hn : Odd n) :
    smoothPart n 2 = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  rintro p hp hpdvd
  have hmem : p ∈ (smoothPart n 2).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hpdvd, smoothPart_ne_zero n 2⟩
  have hpdata := mem_primeFactors_smoothPart_iff.mp hmem
  have hp2 : p = 2 := Nat.le_antisymm hpdata.2 hp.two_le
  subst p
  exact hn.not_two_dvd_nat (dvd_trans hpdvd (smoothPart_dvd n 2))

/-- For an odd nonzero integer, the complementary rough part at cutoff two
is the integer itself. -/
theorem roughPart_two_eq_self_of_odd {n : ℕ} (hn : Odd n) :
    roughPart n 2 = n := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have hsplit := smoothPart_mul_roughPart (n := n) (y := 2) hn0
  simpa [smoothPart_two_eq_one_of_odd hn] using hsplit

/-- The shifted totient of an odd integer above two is odd. -/
theorem shiftedTotient_odd_of_odd {m : ℕ} (hmOdd : Odd m)
    (hmTwo : 2 < m) : Odd (shiftedTotient m) := by
  unfold shiftedTotient
  exact hmOdd.add_even (Nat.totient_even hmTwo)

/-- The gcd of two shifted coefficients is odd as soon as the first
cofactor is odd and above two. -/
theorem shiftedCoefficientGcd_odd {m m' : ℕ} (hmOdd : Odd m)
    (hmTwo : 2 < m) : Odd (shiftedCoefficientGcd m m') := by
  unfold shiftedCoefficientGcd
  exact Odd.of_dvd_nat (shiftedTotient_odd_of_odd hmOdd hmTwo)
    (Nat.gcd_dvd_left _ _)

/-- At cutoff two, no smooth factor is lost from a common shifted
coefficient: its rough part is the full gcd. -/
theorem roughPart_shiftedCoefficientGcd_two_eq
    {m m' : ℕ} (hmOdd : Odd m) (hmTwo : 2 < m) :
    roughPart (shiftedCoefficientGcd m m') 2 =
      shiftedCoefficientGcd m m' := by
  exact roughPart_two_eq_self_of_odd
    (shiftedCoefficientGcd_odd hmOdd hmTwo)

/-- Every divisor of a common shifted coefficient of odd cofactors is also
entirely rough at cutoff two. -/
theorem roughPart_commonDivisor_two_eq
    {m m' h : ℕ} (hmOdd : Odd m) (hmTwo : 2 < m)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    roughPart h 2 = h := by
  have hhOdd : Odd h := Odd.of_dvd_nat
    (shiftedCoefficientGcd_odd hmOdd hmTwo) hh
  exact roughPart_two_eq_self_of_odd hhOdd

end Erdos822
