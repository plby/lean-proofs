/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CollisionFiber

/-!
# Eliminating the zero determinant off the diagonal

If two cofactors have the same totient, the constant terms in their outer
linear forms agree.  Once each outer prime is larger than the opposite
linear coefficient, unique prime divisibility forces the two outer primes,
and then the two cofactors, to agree.  Thus the zero determinant never needs
to be charged in the off-diagonal singular-factor average.
-/

namespace Erdos822

/-- Equal totients cannot give an off-diagonal outer collision when each
outer prime is larger than the opposite shifted coefficient. -/
theorem eq_of_outer_collision_of_totient_eq_of_cross_large
    {x m m' p p' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmp : m < p) (hm'p' : m' < p')
    (hpm' : m' + Nat.totient m' < p)
    (hp'm : m + Nat.totient m < p')
    (hphi : Nat.totient m = Nat.totient m')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    m = m' ∧ p = p' := by
  have hpPrime : p.Prime := (mem_outerPrimes_iff.mp hp).2.2
  have hp'Prime : p'.Prime := (mem_outerPrimes_iff.mp hp').2.2
  have hlin := outer_collision_linear_eq_int hp hp' hm hm' hmp hm'p'
    hcollision
  have hprodZ :
      ((m + Nat.totient m : ℕ) : ℤ) * p =
        ((m' + Nat.totient m' : ℕ) : ℤ) * p' := by
    unfold shiftedTotient at hlin
    rw [hphi] at hlin
    have hprodZ' :
        ((m + Nat.totient m' : ℕ) : ℤ) * p =
          ((m' + Nat.totient m' : ℕ) : ℤ) * p' := by
      linarith
    simpa [hphi] using hprodZ'
  have hprod :
      (m + Nat.totient m) * p =
        (m' + Nat.totient m') * p' := by
    exact_mod_cast hprodZ
  have hpdvd : p ∣ (m' + Nat.totient m') * p' := by
    rw [← hprod]
    exact dvd_mul_left p (m + Nat.totient m)
  have hpp' : p = p' := by
    rcases hpPrime.dvd_mul.mp hpdvd with hleft | hright
    · exact False.elim ((not_le_of_gt hpm')
        (Nat.le_of_dvd (by positivity) hleft))
    · exact ((hp'Prime.dvd_iff_eq hpPrime.ne_one).mp hright).symm
  subst p'
  have hcoefPos : 0 < p := hpPrime.pos
  have hcoef :
      m + Nat.totient m = m' + Nat.totient m' :=
    Nat.eq_of_mul_eq_mul_right hcoefPos hprod
  constructor
  · omega
  · rfl

/-- Under the same cross-large hypothesis, equal totients make the whole
off-diagonal fixed-cofactor fiber empty. -/
theorem outerCollisionPairs_eq_empty_of_totient_eq_of_ne
    {x m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hcross : ∀ p ∈ outerPrimes x m,
      m' + Nat.totient m' < p)
    (hcross' : ∀ p ∈ outerPrimes x m',
      m + Nat.totient m < p)
    (hphi : Nat.totient m = Nat.totient m')
    (hne : m ≠ m') :
    outerCollisionPairs x m m' = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨⟨p, p'⟩, hpairs⟩
  rw [mem_outerCollisionPairs_iff] at hpairs
  have heq := eq_of_outer_collision_of_totient_eq_of_cross_large
    hm hm' hpairs.1 hpairs.2.1
    (hlarge p hpairs.1) (hlarge' p' hpairs.2.1)
    (hcross p hpairs.1) (hcross' p' hpairs.2.1)
    hphi hpairs.2.2
  exact hne heq.1

/-- At the perfect-power scale, an outer prime attached to one odd raw
cofactor is larger even than the opposite shifted cofactor.  The exponent
gap 60 - 2 * 28 = 4 absorbs the factor four from the two shifted
coefficients. -/
theorem oddOuterPrime_cross_shifted_large
    {N m m' p : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ oddRawCofactors N) (hm' : m' ∈ oddRawCofactors N)
    (hp : p ∈ outerPrimes (N ^ 60) m) :
    m' + Nat.totient m' < p := by
  have hmpos : 0 < m := oddRawCofactors_pos hm
  have hmle : m ≤ N ^ 28 := oddRawCofactors_le_pow_twenty_eight hm
  have hm'le : m' ≤ N ^ 28 := oddRawCofactors_le_pow_twenty_eight hm'
  have hfour : 4 ≤ N ^ 4 := by
    exact (by norm_num : 4 ≤ 2 ^ 4).trans
      (Nat.pow_le_pow_left hN 4)
  have hmul :
      (2 * m') * (2 * m) ≤ N ^ 60 := by
    calc
      (2 * m') * (2 * m) ≤
          (2 * N ^ 28) * (2 * N ^ 28) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm'le)
          (Nat.mul_le_mul_left 2 hmle)
      _ = 4 * N ^ 56 := by ring
      _ ≤ N ^ 4 * N ^ 56 := Nat.mul_le_mul_right _ hfour
      _ = N ^ 60 := by ring
  have hdenom : 0 < 2 * m := by positivity
  have hquot : 2 * m' ≤ N ^ 60 / (2 * m) :=
    (Nat.le_div_iff_mul_le hdenom).2 (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul)
  have hshift : m' + Nat.totient m' ≤ 2 * m' := by
    simpa [shiftedTotient] using shiftedTotient_le_two_mul m'
  exact hshift.trans_lt
    (hquot.trans_lt (mem_outerPrimes_iff.mp hp).1)

/-- Therefore a zero totient determinant contributes no off-diagonal
collision fiber on the odd raw layer. -/
theorem oddOuterCollisionPairs_eq_empty_of_totient_eq_of_ne
    {N m m' : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ oddRawCofactors N) (hm' : m' ∈ oddRawCofactors N)
    (hphi : Nat.totient m = Nat.totient m') (hne : m ≠ m') :
    outerCollisionPairs (N ^ 60) m m' = ∅ := by
  apply outerCollisionPairs_eq_empty_of_totient_eq_of_ne
    (oddRawCofactors_pos hm) (oddRawCofactors_pos hm')
    (fun p hp => oddOuterPrime_large_of_mem hN hm hp)
    (fun p hp => oddOuterPrime_large_of_mem hN hm' hp)
    (fun p hp => oddOuterPrime_cross_shifted_large hN hm hm' hp)
    (fun p hp => oddOuterPrime_cross_shifted_large hN hm' hm hp)
    hphi hne

end Erdos822
