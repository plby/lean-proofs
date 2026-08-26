/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargeGcdFreeFilter
import ErdosProblems.Erdos822.QuadraticResidueRelation

/-!
# Common-divisor residues for the genuine B4 filter

The earlier cutoff-two interface is useful for elementary experiments, but
the published proof uses a growing cutoff.  The lemmas here repeat the
product, sum, and quadratic-residue consequences with the exact B4
hypothesis: every prime factor of the common divisor lies above the cutoff.
-/

namespace Erdos822

/-- A supported collision and a divisor of its common shifted coefficient
force the product of the two new prime factors into one residue class. -/
theorem cofactorProduct_modEq_of_supported_largeGcdFree_commonDivisor
    {N y x h m m' k r q : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne : (outerCollisionPairs x m m').Nonempty)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hmul : m = k * r * q) :
    k * (r * q) ≡ m' [MOD h] := by
  have hdistG : shiftedCoefficientGcd m m' ∣ Nat.dist m m' :=
    shiftedCoefficientGcd_dvd_dist_of_nonempty
      (largeGcdFreeOddCofactors_pos hm) hm' hlarge hlarge' hne
  have hdist : h ∣ Nat.dist m m' := dvd_trans hh hdistG
  have hmul' : m = k * (r * q) := by
    simpa [Nat.mul_assoc] using hmul
  exact mul_modEq_of_dvd_dist hdist hmul'

/-- With k,m',h fixed, the two product residues agree after cancellation
by the genuine growing-cutoff B4 condition. -/
theorem cofactorProducts_modEq_of_supported_largeGcdFree_commonDivisor
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ largeGcdFreeOddCofactors N y)
    (hm₂ : m₂ ∈ largeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p)
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂) :
    r₁ * q₁ ≡ r₂ * q₂ [MOD h] := by
  have hu₁ : k * (r₁ * q₁) ≡ m' [MOD h] :=
    cofactorProduct_modEq_of_supported_largeGcdFree_commonDivisor
      hm₁ hm' hlarge₁ hlarge' hne₁ hh₁ hmul₁
  have hu₂ : k * (r₂ * q₂) ≡ m' [MOD h] :=
    cofactorProduct_modEq_of_supported_largeGcdFree_commonDivisor
      hm₂ hm' hlarge₂ hlarge' hne₂ hh₂ hmul₂
  have hkdiv : k ∣ m₁ := by
    rw [hmul₁]
    exact ⟨r₁ * q₁, by ring⟩
  have hcop : Nat.Coprime h k :=
    commonDivisor_coprime_leftFactor_of_largeGcdFree
      hm₁ hkdiv hh₁ hprimeLarge
  exact product_modEq_of_mul_modEq_target hcop hu₁ hu₂

/-- The second congruence determines the sum residue as well, because the
totient of k is invertible modulo the large-supported common divisor. -/
theorem cofactorSums_modEq_of_supported_largeGcdFree_commonDivisor
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ largeGcdFreeOddCofactors N y)
    (hm₂ : m₂ ∈ largeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p)
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ + q₁ ≡ r₂ + q₂ [MOD h] := by
  have hprod : r₁ * q₁ ≡ r₂ * q₂ [MOD h] :=
    cofactorProducts_modEq_of_supported_largeGcdFree_commonDivisor
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
      hh₁ hh₂ hprimeLarge hmul₁ hmul₂
  have hsum₁ := sum_modEq_of_supported_commonDivisor
    hr₁ hq₁ hr₁k hq₁kr₁ hh₁ hmul₁
  have hsum₂ := sum_modEq_of_supported_commonDivisor
    hr₂ hq₂ hr₂k hq₂kr₂ hh₂ hmul₂
  have hrhs :
      shiftedTotient k * (r₁ * q₁) + Nat.totient k ≡
        shiftedTotient k * (r₂ * q₂) + Nat.totient k [MOD h] :=
    (hprod.mul_left (shiftedTotient k)).add_right (Nat.totient k)
  have hphi :
      Nat.totient k * (r₁ + q₁) ≡
        Nat.totient k * (r₂ + q₂) [MOD h] :=
    hsum₁.trans (hrhs.trans hsum₂.symm)
  have hkdiv : k ∣ m₁ := by
    rw [hmul₁]
    exact ⟨r₁ * q₁, by ring⟩
  have hcop : Nat.Coprime h (Nat.totient k) :=
    commonDivisor_coprime_totient_leftFactor_of_largeGcdFree
      hm₁ hkdiv hh₁ hprimeLarge
  exact Nat.ModEq.cancel_left_of_coprime hcop hphi

/-- Hence both new prime factors satisfy one fixed monic quadratic
congruence modulo the large-supported common divisor. -/
theorem supported_pair_roots_of_largeGcdFree_commonDivisor
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ largeGcdFreeOddCofactors N y)
    (hm₂ : m₂ ∈ largeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p)
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ ^ 2 + r₂ * q₂ ≡ (r₂ + q₂) * r₁ [MOD h] ∧
      q₁ ^ 2 + r₂ * q₂ ≡ (r₂ + q₂) * q₁ [MOD h] := by
  have hprod :=
    cofactorProducts_modEq_of_supported_largeGcdFree_commonDivisor
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
      hh₁ hh₂ hprimeLarge hmul₁ hmul₂
  have hsum :=
    cofactorSums_modEq_of_supported_largeGcdFree_commonDivisor
      hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge' hne₁ hne₂
      hh₁ hh₂ hprimeLarge hmul₁ hmul₂ hr₁ hq₁ hr₂ hq₂
      hr₁k hq₁kr₁ hr₂k hq₂kr₂
  exact pair_roots_of_sum_product_modEq hprod hsum

end Erdos822
