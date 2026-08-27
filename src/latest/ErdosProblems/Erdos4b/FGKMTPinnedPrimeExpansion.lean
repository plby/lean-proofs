/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedDivisorWeight
import ErdosProblems.Erdos4b.FGKMTPrimePreSieveNormalization

/-!
# Exact finite expansion of the pinned prime mass

The actual weight, support and presieve are retained. For each allowed
residue and divisor pair, the remaining coefficient is the literal
number of primes in the interval satisfying those divisibility conditions.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def commonPinnedPrimeSet (A B : ℕ) : Finset ℕ := (Finset.Ioc A B).filter Nat.Prime

theorem mem_commonPinnedPrimeSet {A B P : ℕ} :
    P ∈ commonPinnedPrimeSet A B ↔ A < P ∧ P ≤ B ∧ P.Prime := by
  simp only [commonPinnedPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
  tauto

def commonPinnedPrimeMass (m W M R Q A B : ℕ) (y : ℝ)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) : ℝ :=
  ∑ P ∈ commonPinnedPrimeSet A B,
    commonPrimeSieveWeight (m + 1) W M R y h P ((Q : ℤ) - (h j : ℤ) * P)

def commonPinnedDivisorCondition (m Q : ℕ) (p : α → ℕ)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) (d : α → Option (Fin m)) (P : ℕ) : Prop :=
  ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣
    (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P

open scoped Classical in
def commonPinnedPairPrimeCount (m W Q A B v : ℕ) (p : α → ℕ)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) (d e : α → Option (Fin m)) : ℕ :=
  ((commonPinnedPrimeSet A B).filter fun P => P ≡ v [MOD W] ∧
    commonPinnedDivisorCondition m Q p h j d P ∧
      commonPinnedDivisorCondition m Q p h j e P).card

theorem commonPinnedDivisorWeight_eq_quadratic (m R : ℕ) (p : α → ℕ)
    (j : Fin (m + 1)) (forms : Fin m → ℤ) :
    commonPinnedDivisorWeight m R p j forms =
      ∑ d : α → Option (Fin m), ∑ e : α → Option (Fin m),
        if (∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i) ∧
            (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ forms i) then
          commonPinnedCoefficient m R p j d * commonPinnedCoefficient m R p j e
        else 0 := by
  classical
  unfold commonPinnedDivisorWeight
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hd : ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i <;>
    by_cases he : ∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ forms i <;> simp [hd, he]

theorem prime_coprime_presieve_of_mem {A B W P : ℕ}
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ W → q ≤ A) (hP : P ∈ commonPinnedPrimeSet A B) :
    P.Coprime W := by
  obtain ⟨hAP, _hPB, hp⟩ := mem_commonPinnedPrimeSet.mp hP
  exact hp.coprime_iff_not_dvd.mpr (fun hdiv => (not_le_of_gt hAP) (hsmall P hp hdiv))

theorem commonPinned_support_of_mem {m A B Q P : ℕ} {y : ℝ}
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (hQ : (Q : ℝ) ≤ y) (hB : (h j : ℝ) * B ≤ y) (hP : P ∈ commonPinnedPrimeSet A B) :
    |(((Q : ℤ) - (h j : ℤ) * P : ℤ) : ℝ)| ≤ y := by
  have hPB : (P : ℝ) ≤ B := by exact_mod_cast (mem_commonPinnedPrimeSet.mp hP).2.1
  have hprod : (h j : ℝ) * P ≤ y :=
    (mul_le_mul_of_nonneg_left hPB (Nat.cast_nonneg _)).trans hB
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) Q,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) (h j)) (Nat.cast_nonneg (α := ℝ) P)]

open scoped Classical in
theorem commonPrimeSieveWeight_pin_eq_residue_sum {m W M R P Q : ℕ}
    (hW : 0 < W) (hQ : Q.Prime) (hRQ : R < Q) (hcop : P.Coprime W)
    (y : ℝ) (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (hsupport : |(((Q : ℤ) - (h j : ℤ) * P : ℤ) : ℝ)| ≤ y) :
    commonPrimeSieveWeight (m + 1) W M R y h P ((Q : ℤ) - (h j : ℤ) * P) =
      ∑ v ∈ primePreSieveResidues W Q (fun i => (h i : ℤ)) j,
        if P ≡ v [MOD W] then
          commonPinnedDivisorWeight m R (fun q : commonPrimeUniverse M R => q.val) j
            (fun i => (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P)
        else 0 := by
  rw [commonPrimeSieveWeight_at_prime_pin hQ hRQ,
    sum_primePreSieve_residue_indicator hW]
  unfold primePreSieveCondition
  simp only [hsupport, true_and]
  by_cases hgood : (∏ i, ((Q : ℤ) - (h j : ℤ) * P + (h i : ℤ) * P).natAbs).Coprime W
  · rw [if_pos hgood, if_pos ⟨hcop, hgood⟩]
  · rw [if_neg hgood, if_neg (fun hh => hgood hh.2)]

theorem commonPinnedPrimeMass_eq_pair_counts {m W M R Q A B : ℕ} {y : ℝ}
    (hW : 0 < W) (hQ : Q.Prime) (hRQ : R < Q)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ W → q ≤ A)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (hQy : (Q : ℝ) ≤ y) (hBy : (h j : ℝ) * B ≤ y) :
    commonPinnedPrimeMass m W M R Q A B y h j =
      ∑ v ∈ primePreSieveResidues W Q (fun i => (h i : ℤ)) j,
        ∑ d : commonPrimeUniverse M R → Option (Fin m),
          ∑ e : commonPrimeUniverse M R → Option (Fin m),
            commonPinnedCoefficient m R (fun q => q.val) j d *
              commonPinnedCoefficient m R (fun q => q.val) j e *
                commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e := by
  classical
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let weight := fun P => commonPinnedDivisorWeight m R p j
    (fun i => (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P)
  have hweight : commonPinnedPrimeMass m W M R Q A B y h j =
      ∑ P ∈ commonPinnedPrimeSet A B,
        ∑ v ∈ primePreSieveResidues W Q (fun i => (h i : ℤ)) j,
          if P ≡ v [MOD W] then weight P else 0 := by
    apply Finset.sum_congr rfl
    intro P hP
    exact commonPrimeSieveWeight_pin_eq_residue_sum hW hQ hRQ
      (prime_coprime_presieve_of_mem hsmall hP) y h j
      (commonPinned_support_of_mem h j hQy hBy hP)
  rw [hweight, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  have hpoint (P : ℕ) : (if P ≡ v [MOD W] then weight P else 0) =
      ∑ d : commonPrimeUniverse M R → Option (Fin m),
        ∑ e : commonPrimeUniverse M R → Option (Fin m),
          if P ≡ v [MOD W] ∧ commonPinnedDivisorCondition m Q p h j d P ∧
              commonPinnedDivisorCondition m Q p h j e P then
            commonPinnedCoefficient m R p j d * commonPinnedCoefficient m R p j e
          else 0 := by
    by_cases hc : P ≡ v [MOD W]
    · simp only [hc, if_true, true_and, weight, commonPinnedDivisorCondition,
        commonPinnedDivisorWeight_eq_quadratic]
    · simp [hc]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, commonPinnedPairPrimeCount, p]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedPrimeMass_eq_pair_counts
#print axioms Erdos4b.FGKMT.commonPrimeSieveWeight_pin_eq_residue_sum
