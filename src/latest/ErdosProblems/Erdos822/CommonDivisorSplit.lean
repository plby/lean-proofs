/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SquarefreeQuadraticClasses
import ErdosProblems.Erdos822.SmoothPart

/-!
# Splitting a common shifted divisor at the B4 cutoff

The corrected B4 condition applies only to primes above its cutoff.  Thus a
common shifted coefficient cannot honestly be treated as wholly rough.  This
file introduces its complementary rough part and records the exact facts
needed by the CRT argument: the rough part divides the original modulus, all
of its prime factors are above the cutoff, and on the corrected B4 family it
is both coprime to the cofactor and squarefree.
-/

namespace Erdos822

/-- The part of `n.factorization` supported on primes strictly above `y`. -/
def roughFactorization (n y : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter fun p ↦ y < p

/-- The factor of `n` supported on primes strictly above `y`. -/
def roughPart (n y : ℕ) : ℕ :=
  (roughFactorization n y).prod fun p e ↦ p ^ e

lemma roughFactorization_le_factorization (n y : ℕ) :
    roughFactorization n y ≤ n.factorization := by
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split <;> simp

/-- Taking the factorization of the rough part recovers the filtered
factorization. -/
lemma factorization_roughPart (n y : ℕ) :
    (roughPart n y).factorization = roughFactorization n y := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (roughFactorization_le_factorization n y)

/-- A prime occurs in the rough part exactly when it occurs in `n` and is
strictly above the cutoff. -/
lemma mem_primeFactors_roughPart_iff {n y p : ℕ} :
    p ∈ (roughPart n y).primeFactors ↔ p ∈ n.primeFactors ∧ y < p := by
  change p ∈ (roughPart n y).factorization.support ↔
    p ∈ n.factorization.support ∧ y < p
  rw [factorization_roughPart]
  simp [roughFactorization, Finsupp.support_filter]

/-- The rough part is a divisor of the original integer. -/
lemma roughPart_dvd (n y : ℕ) : roughPart n y ∣ n := by
  exact Nat.prod_pow_dvd_of_le_factorization
    (roughFactorization_le_factorization n y)

lemma smoothPart_ne_zero (n y : ℕ) : smoothPart n y ≠ 0 := by
  unfold smoothPart
  refine (smoothFactorization n y).prod_ne_zero_iff.mpr ?_
  intro p hp
  exact pow_ne_zero _
    (Nat.prime_of_mem_primeFactors
      (Finsupp.support_mono
        (smoothFactorization_le_factorization n y) hp)).ne_zero

lemma roughPart_ne_zero (n y : ℕ) : roughPart n y ≠ 0 := by
  unfold roughPart
  refine (roughFactorization n y).prod_ne_zero_iff.mpr ?_
  intro p hp
  exact pow_ne_zero _
    (Nat.prime_of_mem_primeFactors
      (Finsupp.support_mono
        (roughFactorization_le_factorization n y) hp)).ne_zero

/-- The complementary smooth and rough parts have disjoint prime support. -/
lemma smoothPart_coprime_roughPart (n y : ℕ) :
    Nat.Coprime (smoothPart n y) (roughPart n y) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  rintro p hp hpgcd
  have hps : p ∣ smoothPart n y :=
    dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
  have hpr : p ∣ roughPart n y :=
    dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
  have hpsmem : p ∈ (smoothPart n y).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hps, smoothPart_ne_zero n y⟩
  have hprmem : p ∈ (roughPart n y).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hpr, roughPart_ne_zero n y⟩
  have hple : p ≤ y := (mem_primeFactors_smoothPart_iff.mp hpsmem).2
  have hylt : y < p := (mem_primeFactors_roughPart_iff.mp hprmem).2
  omega

/-- The smooth and rough filtered factorizations partition the full
factorization. -/
lemma smoothFactorization_add_roughFactorization (n y : ℕ) :
    smoothFactorization n y + roughFactorization n y =
      n.factorization := by
  ext p
  simp only [smoothFactorization, roughFactorization,
    Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hpy : p ≤ y
  · have hnlt : ¬ y < p := by omega
    simp [hpy, hnlt]
  · have hlt : y < p := by omega
    simp [hpy, hlt]

/-- For a nonzero integer, the smooth and rough parts multiply back to the
original integer. -/
lemma smoothPart_mul_roughPart {n y : ℕ} (hn : n ≠ 0) :
    smoothPart n y * roughPart n y = n := by
  apply Nat.eq_of_factorization_eq'
    (Nat.mul_ne_zero (smoothPart_ne_zero n y) (roughPart_ne_zero n y)) hn
  rw [Nat.factorization_mul (smoothPart_ne_zero n y) (roughPart_ne_zero n y),
    factorization_smoothPart, factorization_roughPart]
  exact smoothFactorization_add_roughFactorization n y

/-- Every prime divisor of a rough part is above the cutoff. -/
lemma prime_dvd_roughPart_gt {n y p : ℕ}
    (hp : p.Prime) (hpdvd : p ∣ roughPart n y) :
    y < p := by
  have hmem : p ∈ (roughPart n y).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hpdvd, roughPart_ne_zero n y⟩
  exact (mem_primeFactors_roughPart_iff.mp hmem).2

/-- The rough part of a divisor of a common shifted coefficient is again a
divisor of that common shifted coefficient. -/
lemma roughPart_dvd_shiftedCoefficientGcd
    {h m m' y : ℕ} (hh : h ∣ shiftedCoefficientGcd m m') :
    roughPart h y ∣ shiftedCoefficientGcd m m' :=
  dvd_trans (roughPart_dvd h y) hh

/-- The rough part of a common shifted coefficient is coprime to a genuine
B4 cofactor. -/
theorem roughPart_coprime_cofactor_of_largeGcdFree
    {N y h m m' : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    Nat.Coprime (roughPart h y) m := by
  apply commonDivisor_coprime_cofactor_of_largeGcdFree hm
    (roughPart_dvd_shiftedCoefficientGcd hh)
  intro p hp hpdvd
  exact prime_dvd_roughPart_gt hp hpdvd

/-- The rough part of a common shifted coefficient is squarefree on the
corrected B4 family. -/
theorem roughPart_squarefree_of_squarefreeLargeGcdFree
    {N y h m m' : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    Squarefree (roughPart h y) := by
  apply commonDivisor_squarefree_of_squarefreeLargeGcdFree hm
    (roughPart_dvd_shiftedCoefficientGcd hh)
  intro p hp hpdvd
  exact prime_dvd_roughPart_gt hp hpdvd

/-- The honest quadratic-CRT conclusion for a general common divisor:
only its rough part is used as the modulus. -/
theorem supported_pair_mod_mem_quadraticAssignments_of_roughPart
    {N y x h m₁ m₂ m' k r₁ q₁ r₂ q₂ : ℕ}
    (hm₁ : m₁ ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hm₂ : m₂ ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hm' : 0 < m')
    (hlarge₁ : ∀ p ∈ outerPrimes x m₁, m₁ < p)
    (hlarge₂ : ∀ p ∈ outerPrimes x m₂, m₂ < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne₁ : (outerCollisionPairs x m₁ m').Nonempty)
    (hne₂ : (outerCollisionPairs x m₂ m').Nonempty)
    (hh₁ : h ∣ shiftedCoefficientGcd m₁ m')
    (hh₂ : h ∣ shiftedCoefficientGcd m₂ m')
    (hmul₁ : m₁ = k * r₁ * q₁)
    (hmul₂ : m₂ = k * r₂ * q₂)
    (hr₁ : r₁.Prime) (hq₁ : q₁.Prime)
    (hr₂ : r₂.Prime) (hq₂ : q₂.Prime)
    (hr₁k : ¬ r₁ ∣ k) (hq₁kr₁ : ¬ q₁ ∣ k * r₁)
    (hr₂k : ¬ r₂ ∣ k) (hq₂kr₂ : ¬ q₂ ∣ k * r₂) :
    r₁ % roughPart h y ∈
        quadraticAssignmentResidues (r₂ * q₂) (r₂ + q₂) (roughPart h y) ∧
      q₁ % roughPart h y ∈
        quadraticAssignmentResidues (r₂ * q₂) (r₂ + q₂) (roughPart h y) := by
  apply supported_pair_mod_mem_quadraticAssignments_of_squarefreeLargeGcdFree
    hm₁ hm₂ hm' hlarge₁ hlarge₂ hlarge'
    hne₁ hne₂
    (roughPart_dvd_shiftedCoefficientGcd hh₁)
    (roughPart_dvd_shiftedCoefficientGcd hh₂)
  · intro p hp hpdvd
    exact prime_dvd_roughPart_gt hp hpdvd
  · exact hmul₁
  · exact hmul₂
  · exact hr₁
  · exact hq₁
  · exact hr₂
  · exact hq₂
  · exact hr₁k
  · exact hq₁kr₁
  · exact hr₂k
  · exact hq₂kr₂

/-- The corresponding rough CRT family has the honest squarefree
two-to-the-number-of-prime-factors bound. -/
theorem quadraticAssignments_roughPart_card_le_two_pow
    {N y h m m' u v : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m') :
    (quadraticAssignmentResidues u v (roughPart h y)).card ≤
      2 ^ (roughPart h y).primeFactors.card := by
  apply quadraticAssignments_card_le_two_pow_of_corrected_commonDivisor
    hm (roughPart_dvd_shiftedCoefficientGcd hh)
  intro p hp hpdvd
  exact prime_dvd_roughPart_gt hp hpdvd

end Erdos822
