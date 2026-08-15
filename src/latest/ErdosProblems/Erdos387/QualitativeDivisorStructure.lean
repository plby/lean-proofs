/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.QualitativeCounting

/-!
# Divisor structure on the frozen qualitative progression

The unconditional absorber leaves finitely many primes at most `k` in its
residual factors.  On the frozen subprogression those prime powers form a
fixed coefficient.  This file splits every residual-divisor component into
a divisor of that fixed coefficient and a divisor of the varying rough part.
-/

namespace Erdos387

open scoped BigOperators

/-- The product of all fixed small-prime coefficients at the chosen base
point of the frozen progression. -/
noncomputable def frozenSmallCoefficientProduct {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) : ℕ :=
  ∏ i : Fin k, CoverBPZ.AbsorberCoverValid.smallPrimePart k
    (C.residual t₀ (Fin.rev i))

theorem frozenSmallCoefficientProduct_pos {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) :
    0 < frozenSmallCoefficientProduct C t₀ := by
  unfold frozenSmallCoefficientProduct
  apply Finset.prod_pos
  intro i _hi
  exact CoverBPZ.AbsorberCoverValid.smallPrimePart_pos
    (C.residual_pos t₀ (Fin.rev i))

/-- The finite space of all possible fixed small-prime divisor choices. -/
noncomputable def frozenFixedPartChoices {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) :
    Finset (Fin k → ℕ) :=
  Fintype.piFinset fun i : Fin k =>
    (CoverBPZ.AbsorberCoverValid.smallPrimePart k
      (C.residual t₀ (Fin.rev i))).divisors

theorem mem_frozenFixedPartChoices_iff {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) (a : Fin k → ℕ) :
    a ∈ frozenFixedPartChoices C t₀ ↔
      ∀ i : Fin k,
        a i ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i)) := by
  rw [frozenFixedPartChoices, Fintype.mem_piFinset]
  apply forall_congr'
  intro i
  rw [Nat.mem_divisors]
  exact and_iff_left
    (CoverBPZ.AbsorberCoverValid.smallPrimePart_pos
      (C.residual_pos t₀ (Fin.rev i))).ne'

theorem card_frozenFixedPartChoices {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) :
    (frozenFixedPartChoices C t₀).card =
      ∏ i : Fin k,
        (CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i))).divisors.card := by
  exact Fintype.card_piFinset _

/-- Roughness passes from a number to each of its divisors. -/
theorem IsZRough.of_dvd {z a b : ℕ} (hb : IsZRough z b) (hab : a ∣ b) :
    IsZRough z a := by
  intro p hp hpz hpa
  exact hb p hp hpz (hpa.trans hab)

/-- A positive nonunit `z`-rough number is at least `z`. -/
theorem IsZRough.le_of_pos_of_ne_one {z a : ℕ} (ha : 0 < a)
    (hrough : IsZRough z a) (hne : a ≠ 1) : z ≤ a := by
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd hne
  have hzp : z ≤ p := by
    by_contra hpz
    exact hrough p hp (Nat.lt_of_not_ge hpz) hpa
  exact hzp.trans (Nat.le_of_dvd ha hpa)

/-- Every component of a divisor tuple on a frozen, sifted absorber splits
as a divisor of a fixed small-prime coefficient times a divisor of the
varying `z`-rough part. -/
theorem exists_frozen_residualDivisor_split
    {m k T z t₀ t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (ht : t ∈ SiftedAbsorberParameterCandidates (C.frozen t₀) T z)
    (E : CoverDivisorTuple ((C.frozen t₀).toCoverFactorization t)) :
    ∃ a b : Fin k → ℕ,
      (∀ i : Fin k,
        a i ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i))) ∧
      (∀ i : Fin k,
        b i ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
          ((C.frozen t₀).residual t (Fin.rev i))) ∧
      (∀ i : Fin k, E.factor i = a i * b i) ∧
      (∀ i : Fin k, IsZRough z (b i)) := by
  have hsplit : ∀ i : Fin k, ∃ ai bi : ℕ,
      ai ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i)) ∧
      bi ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
          ((C.frozen t₀).residual t (Fin.rev i)) ∧
      E.factor i = ai * bi := by
    intro i
    have hfactor :
        E.factor i ∣ (C.frozen t₀).residual t (Fin.rev i) := by
      rw [← (C.frozen t₀).coverQuotient_eq_residual t i]
      exact E.divides i
    rw [C.frozen_residual_eq_smallPrimePart_mul_largePrimePart
      t₀ t (Fin.rev i)] at hfactor
    exact exists_dvd_and_dvd_of_dvd_mul hfactor
  choose a b ha hb heq using hsplit
  refine ⟨a, b, ha, hb, heq, ?_⟩
  intro i
  exact (largePrimePart_isZRough_of_mem_siftedAbsorberParameters
    (C.frozen t₀) ht (Fin.rev i)).of_dvd (hb i)

/-- The represented divisor itself factors as the product of all fixed-part
choices times the product of all rough-part choices. -/
theorem frozen_residualDivisor_value_eq
    {m k T z t₀ t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (ht : t ∈ SiftedAbsorberParameterCandidates (C.frozen t₀) T z)
    (E : CoverDivisorTuple ((C.frozen t₀).toCoverFactorization t)) :
    ∃ a b : Fin k → ℕ,
      (∀ i : Fin k,
        a i ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i))) ∧
      (∀ i : Fin k,
        b i ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
          ((C.frozen t₀).residual t (Fin.rev i))) ∧
      (∀ i : Fin k, IsZRough z (b i)) ∧
      E.value = (∏ i, a i) * ∏ i, b i := by
  obtain ⟨a, b, ha, hb, heq, hrough⟩ :=
    exists_frozen_residualDivisor_split C ht E
  refine ⟨a, b, ha, hb, hrough, ?_⟩
  rw [CoverDivisorTuple.value]
  simp_rw [heq]
  exact Finset.prod_mul_distrib

/-- The product of all fixed-part divisor choices divides the one constant
`frozenSmallCoefficientProduct`. -/
theorem prod_fixedPart_dvd_frozenSmallCoefficientProduct
    {m k : ℕ} (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ)
    (a : Fin k → ℕ)
    (ha : ∀ i : Fin k,
      a i ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
        (C.residual t₀ (Fin.rev i))) :
    (∏ i, a i) ∣ frozenSmallCoefficientProduct C t₀ := by
  unfold frozenSmallCoefficientProduct
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _hi => ha i

/-- A near-top represented divisor yields a product of `z`-rough choices
which is already large after multiplying by the single fixed coefficient.
This removes all varying small-prime data from the remaining estimates. -/
theorem exists_roughProduct_of_near_frozen_residualDivisor
    {m k T z t₀ t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (ht : t ∈ SiftedAbsorberParameterCandidates (C.frozen t₀) T z)
    (E : CoverDivisorTuple ((C.frozen t₀).toCoverFactorization t))
    (hlower : (C.frozen t₀).nNat t < m * E.value)
    (hupper : E.value ≤ (C.frozen t₀).nNat t) :
    ∃ a b : Fin k → ℕ,
      (∀ i : Fin k,
        a i ∣ CoverBPZ.AbsorberCoverValid.smallPrimePart k
          (C.residual t₀ (Fin.rev i))) ∧
      (∀ i : Fin k,
        b i ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
          ((C.frozen t₀).residual t (Fin.rev i))) ∧
      (∀ i : Fin k, IsZRough z (b i)) ∧
      E.value = (∏ i, a i) * ∏ i, b i ∧
      (∏ i, a i) ∣ frozenSmallCoefficientProduct C t₀ ∧
      (C.frozen t₀).nNat t <
        m * frozenSmallCoefficientProduct C t₀ * ∏ i, b i ∧
      (∏ i, a i) * ∏ i, b i ≤ (C.frozen t₀).nNat t := by
  obtain ⟨a, b, ha, hb, heq, hrough⟩ :=
    exists_frozen_residualDivisor_split C ht E
  have hvalue : E.value = (∏ i, a i) * ∏ i, b i := by
    rw [CoverDivisorTuple.value]
    simp_rw [heq]
    exact Finset.prod_mul_distrib
  have hAdvd :
      (∏ i, a i) ∣ frozenSmallCoefficientProduct C t₀ :=
    prod_fixedPart_dvd_frozenSmallCoefficientProduct C t₀ a ha
  have hAle : (∏ i, a i) ≤ frozenSmallCoefficientProduct C t₀ :=
    Nat.le_of_dvd (frozenSmallCoefficientProduct_pos C t₀) hAdvd
  refine ⟨a, b, ha, hb, hrough, hvalue, hAdvd, ?_, ?_⟩
  · calc
      (C.frozen t₀).nNat t <
          m * ((∏ i, a i) * ∏ i, b i) := by simpa [← hvalue] using hlower
      _ = (m * ∏ i, a i) * ∏ i, b i := by rw [mul_assoc]
      _ ≤ (m * frozenSmallCoefficientProduct C t₀) * ∏ i, b i := by
        gcongr
      _ = m * frozenSmallCoefficientProduct C t₀ * ∏ i, b i := rfl
  · simpa [← hvalue] using hupper

end Erdos387
