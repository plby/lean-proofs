/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.DeterminantSupport
import ErdosProblems.Erdos822.StructuredTotientFormula

/-!
# Residues forced by primes in the reduced determinant

In the small-common-divisor range the singular factor is averaged rather
than bounded pointwise.  With `k` and the middle prime `r` fixed, a prime
dividing the reduced determinant forces the large prime `q` into one residue
class, unless it divides one of the two fixed totient coefficients.  This is
the exact algebraic step behind the paper's modulus-`p*h` progression.
-/

namespace Erdos822

/-- A common divisor of two shifted coefficients fixes the new prime
modulo that divisor whenever the old shifted coefficient is invertible. -/
theorem largePrimes_modEq_of_commonShiftedDivisor
    {k r q q₀ h : ℕ}
    (hq : q.Prime) (hq₀ : q₀.Prime)
    (hqkr : ¬ q ∣ k * r) (hq₀kr : ¬ q₀ ∣ k * r)
    (hcoef : Nat.Coprime h (shiftedTotient (k * r)))
    (hdiv : h ∣ shiftedTotient (k * r * q))
    (hdiv₀ : h ∣ shiftedTotient (k * r * q₀)) :
    q ≡ q₀ [MOD h] := by
  have hadd := shiftedTotient_mul_prime_add_totient_basic hq hqkr
  have hadd₀ := shiftedTotient_mul_prime_add_totient_basic hq₀ hq₀kr
  have hmod :
      shiftedTotient (k * r) * q ≡ Nat.totient (k * r) [MOD h] := by
    rw [← hadd]
    simpa using hdiv.modEq_zero_nat.add_right (Nat.totient (k * r))
  have hmod₀ :
      shiftedTotient (k * r) * q₀ ≡ Nat.totient (k * r) [MOD h] := by
    rw [← hadd₀]
    simpa using hdiv₀.modEq_zero_nat.add_right (Nat.totient (k * r))
  exact Nat.ModEq.cancel_left_of_coprime hcoef (hmod.trans hmod₀.symm)

/-- Two supported large primes charged by the same reduced-determinant
prime are congruent modulo that prime once the fixed coefficient is
invertible. -/
theorem largePrimes_modEq_of_dvd_reducedTotientDet
    {x k r q q₀ m' p : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hq : q.Prime) (hq₀ : q₀.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hq₀kr : ¬ q₀ ∣ k * r)
    (hm' : 0 < m')
    (hlarge : ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge₀ : ∀ s ∈ outerPrimes x (k * r * q₀), k * r * q₀ < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hne : (outerCollisionPairs x (k * r * q) m').Nonempty)
    (hne₀ : (outerCollisionPairs x (k * r * q₀) m').Nonempty)
    (hpdet : p ∣ reducedTotientDet (k * r * q) m')
    (hpdet₀ : p ∣ reducedTotientDet (k * r * q₀) m')
    (hpK : ¬ p ∣ Nat.totient k)
    (hpR : ¬ p ∣ r - 1) :
    q ≡ q₀ [MOD p] := by
  have hkpos : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, nonpos_iff_eq_zero] at hk
    subst k
    simp at hrk
  have hm : 0 < k * r * q :=
    Nat.mul_pos (Nat.mul_pos hkpos hr.pos) hq.pos
  have hm₀ : 0 < k * r * q₀ :=
    Nat.mul_pos (Nat.mul_pos hkpos hr.pos) hq₀.pos
  have htot := totients_modEq_of_dvd_reducedTotientDet
    hm hm' hlarge hlarge' hne hpdet
  have htot₀ := totients_modEq_of_dvd_reducedTotientDet
    hm₀ hm' hlarge₀ hlarge' hne₀ hpdet₀
  have hpair :
      Nat.totient (k * r * q) ≡
        Nat.totient (k * r * q₀) [MOD p] :=
    htot.trans htot₀.symm
  rw [totient_mul_two_primes hr hq hrk hqkr,
    totient_mul_two_primes hr hq₀ hrk hq₀kr] at hpair
  have hpCoef : ¬ p ∣ Nat.totient k * (r - 1) := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpK h
    · exact hpR h
  have hsub : q - 1 ≡ q₀ - 1 [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime
      ((hp.coprime_iff_not_dvd).2 hpCoef) hpair
  have hadd := hsub.add_right 1
  simpa [Nat.sub_add_cancel hq.one_le,
    Nat.sub_add_cancel hq₀.one_le] using hadd

/-- Combining the common-shifted-divisor class modulo `h` with the
determinant-prime class modulo `p` gives the paper's single progression
modulo `p*h`. -/
theorem largePrimes_modEq_mul_of_commonDivisor_and_reducedDet
    {x k r q q₀ m' p h : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hq : q.Prime) (hq₀ : q₀.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hq₀kr : ¬ q₀ ∣ k * r)
    (hm' : 0 < m')
    (hlarge : ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge₀ : ∀ s ∈ outerPrimes x (k * r * q₀), k * r * q₀ < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hne : (outerCollisionPairs x (k * r * q) m').Nonempty)
    (hne₀ : (outerCollisionPairs x (k * r * q₀) m').Nonempty)
    (hpdet : p ∣ reducedTotientDet (k * r * q) m')
    (hpdet₀ : p ∣ reducedTotientDet (k * r * q₀) m')
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hcoef : Nat.Coprime h (shiftedTotient (k * r)))
    (hdiv : h ∣ shiftedTotient (k * r * q))
    (hdiv₀ : h ∣ shiftedTotient (k * r * q₀))
    (hph : Nat.Coprime p h) :
    q ≡ q₀ [MOD p * h] := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul hph).mp
  constructor
  · exact largePrimes_modEq_of_dvd_reducedTotientDet
      hp hr hq hq₀ hrk hqkr hq₀kr hm'
      hlarge hlarge₀ hlarge' hne hne₀ hpdet hpdet₀ hpK hpR
  · exact largePrimes_modEq_of_commonShiftedDivisor
      hq hq₀ hqkr hq₀kr hcoef hdiv hdiv₀

/-- A divisor of the common shifted coefficient also fixes `q` modulo `h`
through the collision distance `|k*r*q-m'|`.  This version only asks that
`h` be coprime to the actual fixed cofactor `k*r`, which is the condition
provided by the large-gcd-free B4 filter. -/
theorem largePrimes_modEq_mul_of_commonDivisor_distance_and_reducedDet
    {x k r q q₀ m' p h : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hq : q.Prime) (hq₀ : q₀.Prime)
    (hrk : ¬ r ∣ k) (hqkr : ¬ q ∣ k * r)
    (hq₀kr : ¬ q₀ ∣ k * r)
    (hm' : 0 < m')
    (hlarge : ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge₀ : ∀ s ∈ outerPrimes x (k * r * q₀), k * r * q₀ < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hne : (outerCollisionPairs x (k * r * q) m').Nonempty)
    (hne₀ : (outerCollisionPairs x (k * r * q₀) m').Nonempty)
    (hh : h ∣ shiftedCoefficientGcd (k * r * q) m')
    (hh₀ : h ∣ shiftedCoefficientGcd (k * r * q₀) m')
    (hpdet : p ∣ reducedTotientDet (k * r * q) m')
    (hpdet₀ : p ∣ reducedTotientDet (k * r * q₀) m')
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hcop : Nat.Coprime h (k * r)) (hph : Nat.Coprime p h) :
    q ≡ q₀ [MOD p * h] := by
  have hkpos : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, nonpos_iff_eq_zero] at hk
    subst k
    simp at hrk
  have hm : 0 < k * r * q :=
    Nat.mul_pos (Nat.mul_pos hkpos hr.pos) hq.pos
  have hm₀ : 0 < k * r * q₀ :=
    Nat.mul_pos (Nat.mul_pos hkpos hr.pos) hq₀.pos
  have hdist : h ∣ Nat.dist (k * r * q) m' :=
    hh.trans (shiftedCoefficientGcd_dvd_dist_of_nonempty
      hm hm' hlarge hlarge' hne)
  have hdist₀ : h ∣ Nat.dist (k * r * q₀) m' :=
    hh₀.trans (shiftedCoefficientGcd_dvd_dist_of_nonempty
      hm₀ hm' hlarge₀ hlarge' hne₀)
  have hmod : k * r * q ≡ m' [MOD h] := by
    by_cases hle : k * r * q ≤ m'
    · rw [Nat.dist_eq_sub_of_le hle] at hdist
      exact (Nat.modEq_iff_dvd' hle).2 hdist
    · have hle' : m' ≤ k * r * q := by omega
      rw [Nat.dist_eq_sub_of_le_right hle'] at hdist
      exact ((Nat.modEq_iff_dvd' hle').2 hdist).symm
  have hmod₀ : k * r * q₀ ≡ m' [MOD h] := by
    by_cases hle : k * r * q₀ ≤ m'
    · rw [Nat.dist_eq_sub_of_le hle] at hdist₀
      exact (Nat.modEq_iff_dvd' hle).2 hdist₀
    · have hle' : m' ≤ k * r * q₀ := by omega
      rw [Nat.dist_eq_sub_of_le_right hle'] at hdist₀
      exact ((Nat.modEq_iff_dvd' hle').2 hdist₀).symm
  have hqmod : q ≡ q₀ [MOD h] := by
    apply Nat.ModEq.cancel_left_of_coprime hcop
    simpa [Nat.mul_assoc] using hmod.trans hmod₀.symm
  apply (Nat.modEq_and_modEq_iff_modEq_mul hph).mp
  exact ⟨largePrimes_modEq_of_dvd_reducedTotientDet
    hp hr hq hq₀ hrk hqkr hq₀kr hm'
    hlarge hlarge₀ hlarge' hne hne₀ hpdet hpdet₀ hpK hpR, hqmod⟩

end Erdos822
