/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmoothTotientPreserving

/-!
# The arithmetic implication behind the B1 exceptional set

The source paper chooses a small factor `k` whose totient is divisible by
the square of every integer up to the smoothness cutoff.  If the remaining
small-prime powers in the full cofactor are themselves at most the cutoff,
then this forces the exact `SmoothTotientPreserving` condition used by the
collision argument.
-/

namespace Erdos822

/-- The square of every positive integer up to `y` divides the totient of
`k`.  This is the exact
condition imposed on the small factor `k` in the source construction. -/
def TotientSquareRich (k y : ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → d ≤ y → d ^ 2 ∣ Nat.totient k

/-- The source's formulation using all positive integers is equivalent to
the prime-power formulation in its preliminary density lemma. -/
theorem totientSquareRich_iff_prime_pow {k y : ℕ} :
    TotientSquareRich k y ↔
      ∀ p a : ℕ, p.Prime → p ^ a ≤ y →
        p ^ (2 * a) ∣ Nat.totient k := by
  constructor
  · intro h p a hp hpa
    have hsq := h (p ^ a) (pow_pos hp.pos a) hpa
    rw [← pow_mul, Nat.mul_comm a 2] at hsq
    exact hsq
  · intro h d hd hdy
    by_cases hφ : Nat.totient k = 0
    · simp [hφ]
    apply (Nat.factorization_prime_le_iff_dvd
      (pow_ne_zero 2 hd.ne') hφ).mp
    intro p hp
    have hpd : p ^ d.factorization p ≤ d :=
      Nat.le_of_dvd hd (Nat.ordProj_dvd d p)
    have hpow := h p (d.factorization p) hp (hpd.trans hdy)
    have hle := (hp.pow_dvd_iff_le_factorization hφ).mp hpow
    simpa [Nat.factorization_pow] using hle

/-- Two distinct prime divisors congruent to one modulo `t` each supply
one factor `t` to Euler's product for the totient. -/
theorem sq_dvd_totient_of_two_prime_divisors
    {n t q₁ q₂ : ℕ}
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (hq₁n : q₁ ∣ n) (hq₂n : q₂ ∣ n)
    (ht₁ : t ∣ q₁ - 1) (ht₂ : t ∣ q₂ - 1) :
    t ^ 2 ∣ Nat.totient n := by
  have hcop : q₁.Coprime q₂ := (Nat.coprime_primes hq₁ hq₂).mpr hne
  have hprod : q₁ * q₂ ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hq₁n hq₂n
  have htot : t ^ 2 ∣ Nat.totient (q₁ * q₂) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hq₁,
      Nat.totient_prime hq₂, pow_two]
    exact Nat.mul_dvd_mul ht₁ ht₂
  exact htot.trans (Nat.totient_dvd_of_dvd hprod)

/-- No prime-power component at a prime up to `y` exceeds `y`. -/
def SmallPrimePowersBounded (m y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ y → p ^ m.factorization p ≤ y

/-- Square richness of a divisor `k` supplies the one-extra-power
divisibility needed for each small prime in a multiple `m` of `k`. -/
theorem pow_succ_factorization_dvd_totient_of_squareRich
    {k m y p : ℕ}
    (hkm : k ∣ m)
    (hrich : TotientSquareRich k y)
    (hbounded : SmallPrimePowersBounded m y)
    (hp : p.Prime) (hpy : p ≤ y) :
    p ^ (m.factorization p + 1) ∣ Nat.totient m := by
  let e := m.factorization p
  have htot : Nat.totient k ∣ Nat.totient m :=
    Nat.totient_dvd_of_dvd hkm
  by_cases he : e = 0
  · have hpSq : p ^ 2 ∣ Nat.totient k := hrich p hp.pos hpy
    have hpOne : p ^ (e + 1) ∣ p ^ 2 :=
      Nat.pow_dvd_pow p (by omega)
    exact hpOne.trans (hpSq.trans htot)
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hpe : p ^ e ≤ y := hbounded p hp hpy
    have hpSq : (p ^ e) ^ 2 ∣ Nat.totient k :=
      hrich (p ^ e) (pow_pos hp.pos e) hpe
    have hpDouble : p ^ (2 * e) ∣ Nat.totient k := by
      have hpDouble' : p ^ (e * 2) ∣ Nat.totient k := by
        simpa [pow_mul] using hpSq
      simpa [Nat.mul_comm] using hpDouble'
    have hsucc : e + 1 ≤ 2 * e := by omega
    exact (Nat.pow_dvd_pow p hsucc).trans (hpDouble.trans htot)

/-- The two explicit arithmetic conditions imply the abstract B1 interface
used by the rest of the formalization. -/
theorem smoothTotientPreserving_of_squareRich
    {k m y : ℕ}
    (hkm : k ∣ m)
    (hrich : TotientSquareRich k y)
    (hbounded : SmallPrimePowersBounded m y) :
    SmoothTotientPreserving m y := by
  intro p hp hpy a ha
  exact (Nat.pow_dvd_pow p ha).trans
    (pow_succ_factorization_dvd_totient_of_squareRich
      hkm hrich hbounded hp hpy)

/-- Convenient specialization for the structured cofactors `m = k*r*q`
appearing in the paper. -/
theorem smoothTotientPreserving_mul_mul_of_squareRich
    {k r q y : ℕ}
    (hrich : TotientSquareRich k y)
    (hbounded : SmallPrimePowersBounded (k * r * q) y) :
    SmoothTotientPreserving (k * r * q) y := by
  apply smoothTotientPreserving_of_squareRich
    (k := k) (m := k * r * q) (y := y)
  · exact ⟨r * q, by simp [Nat.mul_assoc]⟩
  · exact hrich
  · exact hbounded

end Erdos822
