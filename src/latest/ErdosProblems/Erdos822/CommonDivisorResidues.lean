/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CoprimeTotientFilter
import ErdosProblems.Erdos822.CollisionAdmissibility

/-!
# Product residue classes forced by a common divisor

The medium-range argument first uses `h ∣ m-m'` to determine the product
`r*q` modulo `h` when `m=k*r*q`.  The B4 coprimality condition makes `k`
invertible modulo every divisor of the common shifted coefficient, so two
candidate products with the same `k,m',h` are congruent.
-/

namespace Erdos822

/-- Divisibility of the natural distance is exactly enough to obtain a
natural modular congruence. -/
theorem modEq_of_dvd_dist {h a b : ℕ}
    (hdist : h ∣ Nat.dist a b) :
    a ≡ b [MOD h] := by
  by_cases hab : a ≤ b
  · rw [Nat.dist_eq_sub_of_le hab] at hdist
    exact (Nat.modEq_iff_dvd' hab).2 hdist
  · have hba : b ≤ a := by omega
    rw [Nat.dist_eq_sub_of_le_right hba] at hdist
    exact ((Nat.modEq_iff_dvd' hba).2 hdist).symm

/-- If `m=k*u` and `h` divides the distance from `m` to `m'`, then
`k*u` occupies the residue class of `m'` modulo `h`. -/
theorem mul_modEq_of_dvd_dist
    {h m m' k u : ℕ} (hdist : h ∣ Nat.dist m m')
    (hmul : m = k * u) :
    k * u ≡ m' [MOD h] := by
  rw [← hmul]
  exact modEq_of_dvd_dist hdist

/-- Two products with the same invertible leading coefficient and the same
target residue are congruent after cancellation. -/
theorem product_modEq_of_mul_modEq_target
    {h k u u₀ t : ℕ}
    (hcop : Nat.Coprime h k)
    (hu : k * u ≡ t [MOD h])
    (hu₀ : k * u₀ ≡ t [MOD h]) :
    u ≡ u₀ [MOD h] := by
  apply Nat.ModEq.cancel_left_of_coprime hcop
  exact hu.trans hu₀.symm

/-- Every divisor of the common shifted coefficient is coprime to a fixed
left factor of a B4 cofactor. -/
theorem commonDivisor_coprime_leftFactor_of_coprimeTotientCofactor
    {N h m m' l : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N)
    (hlm : l ∣ m)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    Nat.Coprime h l := by
  exact Nat.Coprime.of_dvd_left hh
    (shiftedCoefficientGcd_coprime_leftFactor_of_coprime_totient
      hlm (mem_coprimeTotientOddCofactors_iff.mp hm).2)

/-- A supported collision and a divisor `h` of its common shifted
coefficient force `k*(r*q)` into the residue class of the other cofactor. -/
theorem cofactorProduct_modEq_of_supported_commonDivisor
    {N x h m m' k r q : ℕ}
    (hm : m ∈ coprimeTotientOddCofactors N)
    (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne : (outerCollisionPairs x m m').Nonempty)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hmul : m = k * r * q) :
    k * (r * q) ≡ m' [MOD h] := by
  have hdistG : shiftedCoefficientGcd m m' ∣ Nat.dist m m' :=
    shiftedCoefficientGcd_dvd_dist_of_nonempty
      (coprimeTotientOddCofactors_pos hm) hm' hlarge hlarge' hne
  have hdist : h ∣ Nat.dist m m' := dvd_trans hh hdistG
  have hmul' : m = k * (r * q) := by
    simpa [Nat.mul_assoc] using hmul
  exact mul_modEq_of_dvd_dist hdist hmul'

/-- With `k,m',h` fixed, any two supported B4 cofactors have the same
`r*q` residue modulo `h`. -/
theorem cofactorProducts_modEq_of_supported_commonDivisor
    {N x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ coprimeTotientOddCofactors N)
    (hm₂ : m₂ ∈ coprimeTotientOddCofactors N)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂) :
    r₁ * q₁ ≡ r₂ * q₂ [MOD h] := by
  have hu₁ : k * (r₁ * q₁) ≡ m' [MOD h] :=
    cofactorProduct_modEq_of_supported_commonDivisor
      hm₁ hm' hlarge₁ hlarge' hne₁ hh₁ hmul₁
  have hu₂ : k * (r₂ * q₂) ≡ m' [MOD h] :=
    cofactorProduct_modEq_of_supported_commonDivisor
      hm₂ hm' hlarge₂ hlarge' hne₂ hh₂ hmul₂
  have hkdiv : k ∣ m₁ := by
    rw [hmul₁]
    exact ⟨r₁ * q₁, by ring⟩
  have hcop : Nat.Coprime h k :=
    commonDivisor_coprime_leftFactor_of_coprimeTotientCofactor
      hm₁ hkdiv hh₁
  exact product_modEq_of_mul_modEq_target hcop hu₁ hu₂

end Erdos822
