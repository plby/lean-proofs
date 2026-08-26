import ErdosProblems.Erdos394.LargePrimePart
import ErdosProblems.Erdos394.PrimeSubset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic of the medium-prime decomposition `n = m q`
-/

open Nat Finset

namespace Erdos394

/-- No prime from `P` occurs to second order in `n`. -/
def noSquaredPrime (P : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ P, ¬p * p ∣ n

/-- The selected-prime set is always a subset of the ambient prime set. -/
theorem badPrimeSet_subset (P : Finset ℕ) (n : ℕ) :
    badPrimeSet P n ⊆ P := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- The selected prime product divides the original integer. -/
theorem primePart_dvd (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (n : ℕ) : primePart P n ∣ n := by
  unfold primePart
  have h := (subset_badPrimeSet_iff_prod_dvd
    (P := P) (T := badPrimeSet P n) hprime n).mp
      (show badPrimeSet P n ⊆ badPrimeSet P n from Finset.Subset.rfl)
  exact h.2

/-- The selected prime part is positive. -/
theorem primePart_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (n : ℕ) : 0 < primePart P n := by
  unfold primePart
  apply Finset.prod_pos
  intro p hp
  exact (hprime p ((badPrimeSet_subset P n) hp)).pos

/-- The product notation agrees with `primeProduct` on the selected set. -/
theorem primePart_eq_primeProduct (P : Finset ℕ) (n : ℕ) :
    primePart P n = primeProduct (badPrimeSet P n) := rfl

/-- Exact quotient reconstruction. -/
theorem div_primePart_mul_primePart (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (n : ℕ) :
    n / primePart P n * primePart P n = n :=
  Nat.div_mul_cancel (primePart_dvd P hprime n)

/-- The quotient by the selected prime part is positive for positive `n`. -/
theorem div_primePart_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : 0 < n) : 0 < n / primePart P n := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hn (primePart_dvd P hprime n)
  · exact primePart_pos P hprime n

/-- With no selected prime square, the quotient and selected prime part are
coprime. -/
theorem div_primePart_coprime (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n)
    (hno : noSquaredPrime P n) :
    (n / primePart P n).Coprime (primePart P n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hpprime, hpd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpm : p ∣ n / primePart P n := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ primePart P n := hpd.trans (Nat.gcd_dvd_right _ _)
  have hqne : primePart P n ≠ 0 := (primePart_pos P hprime n).ne'
  have hpT : p ∈ badPrimeSet P n := by
    have hpf : (primePart P n).primeFactors = badPrimeSet P n := by
      rw [primePart_eq_primeProduct]
      exact primeFactors_primeProduct (badPrimeSet P n)
        (fun r hr ↦ hprime r ((badPrimeSet_subset P n) hr))
    rw [← hpf]
    exact hpprime.mem_primeFactors hpq hqne
  have hpP : p ∈ P := badPrimeSet_subset P n hpT
  apply hno p hpP
  have hmul : p * p ∣ (n / primePart P n) * primePart P n :=
    Nat.mul_dvd_mul hpm hpq
  rwa [div_primePart_mul_primePart P hprime n] at hmul

/-- The quotient is free of every ambient prime not selected into `q`. -/
theorem badPrimeSet_sdiff_div_primePart_eq_empty
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n) :
    badPrimeSet (P \ badPrimeSet P n) (n / primePart P n) = ∅ := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpPT := Finset.mem_sdiff.mp hp'.1
    exfalso
    apply hpPT.2
    apply Finset.mem_filter.mpr
    refine ⟨hpPT.1, ?_⟩
    have hm_dvd_n : n / primePart P n ∣ n := by
      use primePart P n
      exact (div_primePart_mul_primePart P hprime n).symm
    exact hp'.2.trans hm_dvd_n
  · intro hp
    simp at hp

/-- Complete structural package for the unique medium-prime decomposition. -/
theorem mediumPrime_decomposition
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) {n : ℕ}
    (hn : 0 < n) (hno : noSquaredPrime P n) :
    let T := badPrimeSet P n
    let q := primePart P n
    let m := n / q
    T ⊆ P ∧ 0 < q ∧ 0 < m ∧ m * q = n ∧ m.Coprime q ∧
      badPrimeSet (P \ T) m = ∅ := by
  dsimp
  exact ⟨badPrimeSet_subset P n, primePart_pos P hprime n,
    div_primePart_pos P hprime hn, div_primePart_mul_primePart P hprime n,
    div_primePart_coprime P hprime hn hno,
    badPrimeSet_sdiff_div_primePart_eq_empty P hprime hn⟩

end Erdos394
