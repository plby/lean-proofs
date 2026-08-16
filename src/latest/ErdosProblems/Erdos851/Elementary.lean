import ErdosProblems.Erdos851.Basic

/-!
# Elementary tools for Erdős problem 851

This file contains the finite and density-theoretic part of the proof.  The
analytic sieve estimates can be supplied later as hypotheses to these lemmas.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos851

/-- The integer points in the dyadic shell `(X, 2 * X]`. -/
def dyadicInterval (X : ℕ) : Finset ℕ := Finset.Ioc X (2 * X)

/-- The number of candidates from `J` accepted at `a`. -/
def candidateCount {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (accepts : ℕ → ι → Prop) [DecidableRel accepts]
    (a : ℕ) : ℕ :=
  (J.filter (accepts a)).card

/-- The primes strictly between two cutoffs. -/
def mediumPrimes (z Y : ℕ) : Finset ℕ :=
  (Finset.Ioo z Y).filter Nat.Prime

/-- Product of the primes strictly between two cutoffs. -/
def mediumPrimeProduct (z Y : ℕ) : ℕ :=
  (mediumPrimes z Y).prod id

/-- The primes at most `z`. -/
def primesUpTo (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

/-- Prime factors of `n` which are at least `Y`. -/
def largePrimeFactors (Y n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => Y ≤ p

/-- The product of the large distinct prime factors bounds a power of their
cutoff. -/
theorem pow_card_largePrimeFactors_le {Y n : ℕ} (hn : n ≠ 0) :
    Y ^ (largePrimeFactors Y n).card ≤ n := by
  let s := largePrimeFactors Y n
  have hs : s ⊆ n.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hpow : Y ^ s.card ≤ ∏ p ∈ s, p :=
    Finset.pow_card_le_prod s id Y (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2)
  have hprodDvd : (∏ p ∈ s, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset s n.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd n)
  exact hpow.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprodDvd)

/-- A size bound controls the number of prime factors above a cutoff. -/
theorem card_largePrimeFactors_le {Y n L : ℕ}
    (hY : 1 < Y) (hn : n ≠ 0) (hnPow : n < Y ^ (L + 1)) :
    (largePrimeFactors Y n).card ≤ L := by
  by_contra h
  have hcard : L + 1 ≤ (largePrimeFactors Y n).card := by omega
  have hpow : Y ^ (L + 1) ≤ Y ^ (largePrimeFactors Y n).card :=
    Nat.pow_le_pow_right hY.le hcard
  exact (not_lt_of_ge (hpow.trans (pow_card_largePrimeFactors_le hn))) hnPow

/-- Coprimality to the medium-prime product says that each prime factor lies
on one side of the excluded interval. -/
theorem primeFactor_le_or_ge_of_coprime_medium
    {m z Y p : ℕ} (hcop : Nat.Coprime m (mediumPrimeProduct z Y))
    (hp : p ∈ m.primeFactors) : p ≤ z ∨ Y ≤ p := by
  by_contra h
  push Not at h
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpMedium : p ∈ mediumPrimes z Y := by
    simp [mediumPrimes, h.1, h.2, hpPrime]
  have hpProd : p ∣ mediumPrimeProduct z Y := by
    exact Finset.dvd_prod_of_mem id hpMedium
  have hpM : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hpGcd : p ∣ Nat.gcd m (mediumPrimeProduct z Y) :=
    Nat.dvd_gcd hpM hpProd
  rw [hcop] at hpGcd
  exact hpPrime.not_dvd_one hpGcd

/-- A positive integer avoiding all medium primes has only boundedly many
distinct prime factors once the large factors are bounded by size. -/
theorem primeFactors_card_le_of_coprime_medium
    {m z Y L : ℕ} (hY : 1 < Y) (hm : m ≠ 0)
    (hmPow : m < Y ^ (L + 1))
    (hcop : Nat.Coprime m (mediumPrimeProduct z Y)) :
    m.primeFactors.card ≤ (primesUpTo z).card + L := by
  let small := m.primeFactors.filter fun p => p ≤ z
  let large := largePrimeFactors Y m
  have hcover : m.primeFactors ⊆ small ∪ large := by
    intro p hp
    rcases primeFactor_le_or_ge_of_coprime_medium hcop hp with hpz | hYp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hpz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hYp⟩)
  have hsmall : small ⊆ primesUpTo z := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.prime_of_mem_primeFactors hp'.1⟩
  calc
    m.primeFactors.card ≤ (small ∪ large).card := Finset.card_le_card hcover
    _ ≤ small.card + large.card := Finset.card_union_le _ _
    _ ≤ (primesUpTo z).card + L := Nat.add_le_add
      (Finset.card_le_card hsmall)
      (card_largePrimeFactors_le hY hm hmPow)

/-- The rough-residual certificate in the form used on a dyadic interval. -/
theorem rough_residual_primeFactors_card_le
    {a h z Y L : ℕ} (hha : h < a) (hY : 1 < Y)
    (hsize : a - h < Y ^ (L + 1))
    (hcop : Nat.Coprime (a - h) (mediumPrimeProduct z Y)) :
    (a - h).primeFactors.card ≤ (primesUpTo z).card + L := by
  exact primeFactors_card_le_of_coprime_medium hY
    (Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hha))
    hsize hcop

end Erdos851
