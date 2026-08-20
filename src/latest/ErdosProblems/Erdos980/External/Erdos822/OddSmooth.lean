/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.CollisionEquation

/-!
# A fixed smooth-part class from odd cofactors

Choosing odd cofactors lets the smooth cutoff be the fixed value two.  Then
the only small prime is two, its exponent in the cofactor is zero, and the
standard evenness of the totient supplies the required one power of two.
This avoids any growing normal-order hypothesis in this elementary part of
the collision partition.
-/

namespace Erdos822

/-- For an odd cofactor above two, every prime power required by the
smooth-part preservation lemma at cutoff two divides its totient. -/
theorem small_prime_power_dvd_totient_of_odd
    {m q a : ℕ} (hmOdd : Odd m) (hmTwo : 2 < m)
    (hq : q.Prime) (hqle : q ≤ 2)
    (ha : a ≤ m.factorization q + 1) :
    q ^ a ∣ Nat.totient m := by
  have hqeq : q = 2 := by
    exact Nat.le_antisymm hqle hq.two_le
  subst q
  have hfac : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hmOdd.not_two_dvd_nat
  rw [hfac] at ha
  have ha' : a = 0 ∨ a = 1 := by omega
  rcases ha' with rfl | rfl
  · simp
  · simpa using (even_iff_two_dvd.mp (Nat.totient_even hmTwo))

/-- At cutoff two, the shifted totient of an odd cofactor has the same
smooth part as the cofactor itself. -/
theorem smoothPart_shiftedTotient_eq_of_odd {m : ℕ}
    (hmOdd : Odd m) (hmTwo : 2 < m) :
    smoothPart (shiftedTotient m) 2 = smoothPart m 2 := by
  apply smoothPart_shiftedTotient_eq (by omega)
  intro q hq hqle a ha
  exact small_prime_power_dvd_totient_of_odd hmOdd hmTwo hq hqle ha

/-- Adjoining a larger outer prime preserves the fixed cutoff-two smooth
part for odd cofactors. -/
theorem smoothPart_shiftedTotient_mul_prime_eq_of_odd
    {m p : ℕ} (hmOdd : Odd m) (hmTwo : 2 < m)
    (hp : p.Prime) (hmp : m < p) :
    smoothPart (shiftedTotient (m * p)) 2 = smoothPart m 2 := by
  apply smoothPart_shiftedTotient_mul_prime_eq (by omega) hp hmp
    (hmTwo.trans hmp)
  intro q hq hqle a ha
  exact small_prime_power_dvd_totient_of_odd hmOdd hmTwo hq hqle ha

/-- Hence every collision between odd cofactors above two lies in the same
cutoff-two smooth-part class. -/
theorem smoothPart_eq_of_outer_collision_odd
    {x m m' p p' : ℕ}
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmOdd : Odd m) (hm'Odd : Odd m')
    (hmTwo : 2 < m) (hm'Two : 2 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    smoothPart m 2 = smoothPart m' 2 := by
  have hpPrime : p.Prime := (mem_outerPrimes_iff.mp hp).2.2
  have hp'Prime : p'.Prime := (mem_outerPrimes_iff.mp hp').2.2
  have h := congrArg (fun n => smoothPart n 2) hcollision
  rw [smoothPart_shiftedTotient_mul_prime_eq_of_odd hmOdd hmTwo hpPrime hmp,
    smoothPart_shiftedTotient_mul_prime_eq_of_odd hm'Odd hm'Two hp'Prime hm'p'] at h
  exact h

end Erdos822
