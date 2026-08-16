/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.LocalEulerProducts
import ErdosProblems.Erdos851.RomanoffConvergence

/-!
# Expansion of the truncated singular product

The Euler product `singularFactor h z y` expands over the squarefree products
of primes in the sieve interval `(z,y]`.  This file records the expansion in
the form needed when the factor is averaged over the difference `h`.
-/

open scoped BigOperators

namespace Erdos851

/-- All products of subsets of the primes in `(z,y]`.  The empty subset
contributes `1`. -/
def singularPrimeProducts (z y : ℕ) : Finset ℕ :=
  (sievePrimes z y).powerset.image fun t ↦ ∏ p ∈ t, p

theorem mem_singularPrimeProducts {q z y : ℕ} :
    q ∈ singularPrimeProducts z y ↔
      ∃ t : Finset ℕ, t ⊆ sievePrimes z y ∧ (∏ p ∈ t, p) = q := by
  classical
  simp only [singularPrimeProducts, Finset.mem_image, Finset.mem_powerset]

private theorem primeProduct_injOn_powerset (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun t : Finset ℕ ↦ ∏ p ∈ t, p) P.powerset := by
  intro t ht u hu htu
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp ↦
    hP p (Finset.mem_powerset.mp ht hp)
  have huPrime : ∀ p ∈ u, p.Prime := fun p hp ↦
    hP p (Finset.mem_powerset.mp hu hp)
  calc
    t = (∏ p ∈ t, p).primeFactors := (Nat.primeFactors_prod htPrime).symm
    _ = (∏ p ∈ u, p).primeFactors := congrArg Nat.primeFactors htu
    _ = u := Nat.primeFactors_prod huPrime

private theorem squarefree_primeProduct {t : Finset ℕ}
    (ht : ∀ p ∈ t, p.Prime) : Squarefree (∏ p ∈ t, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp ↦ (ht p hp).squarefree
  intro p hp q hq hpq
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq

private theorem odd_primeProduct {t : Finset ℕ}
    (ht : ∀ p ∈ t, Odd p) : Odd (∏ p ∈ t, p) := by
  induction t using Finset.induction with
  | empty => exact odd_one
  | @insert p t hp ih =>
      rw [Finset.prod_insert hp]
      exact (ht p (by simp)).mul (ih fun q hq ↦ ht q (by simp [hq]))

/-- Every subset product is squarefree. -/
theorem squarefree_of_mem_singularPrimeProducts {q z y : ℕ}
    (hq : q ∈ singularPrimeProducts z y) : Squarefree q := by
  obtain ⟨t, ht, rfl⟩ := mem_singularPrimeProducts.mp hq
  apply squarefree_primeProduct
  intro p hp
  exact (mem_sievePrimes.mp (ht hp)).2.2

/-- Above the prime `2`, every subset product is odd. -/
theorem odd_of_mem_singularPrimeProducts {q z y : ℕ} (hz : 2 ≤ z)
    (hq : q ∈ singularPrimeProducts z y) : Odd q := by
  obtain ⟨t, ht, rfl⟩ := mem_singularPrimeProducts.mp hq
  apply odd_primeProduct
  intro p hp
  have hp' := mem_sievePrimes.mp (ht hp)
  exact hp'.2.2.odd_of_ne_two (by omega)

/-- The subset products in the relevant sieve range are Romanoff moduli. -/
theorem isRomanoffModulus_of_mem_singularPrimeProducts {q z y : ℕ}
    (hz : 2 ≤ z) (hq : q ∈ singularPrimeProducts z y) :
    IsRomanoffModulus q :=
  ⟨squarefree_of_mem_singularPrimeProducts hq,
    odd_of_mem_singularPrimeProducts hz hq⟩

/-- Every nonempty subset product is larger than the lower sieve cutoff. -/
theorem z_lt_of_mem_singularPrimeProducts_of_ne_one {q z y : ℕ}
    (hq : q ∈ singularPrimeProducts z y) (hq1 : q ≠ 1) : z < q := by
  obtain ⟨t, ht, hprod⟩ := mem_singularPrimeProducts.mp hq
  have htne : t.Nonempty := by
    by_contra h
    have htEmpty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst t
    simp at hprod
    exact hq1 hprod.symm
  obtain ⟨p, hp⟩ := htne
  have hpSieve := mem_sievePrimes.mp (ht hp)
  have hprodPos : 0 < ∏ r ∈ t, r := by
    apply Finset.prod_pos
    intro r hr
    exact (mem_sievePrimes.mp (ht hr)).2.2.pos
  have hpLe : p ≤ ∏ r ∈ t, r :=
    Nat.le_of_dvd hprodPos (Finset.dvd_prod_of_mem id hp)
  rw [← hprod]
  exact hpSieve.1.trans_le hpLe

private theorem romanoffCoeff_primeProduct {t : Finset ℕ} {z y : ℕ}
    (hz : 2 ≤ z) (ht : t ⊆ sievePrimes z y) :
    romanoffCoeff (∏ p ∈ t, p) =
      ∏ p ∈ t, (1 / ((p : ℝ) - 1)) := by
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp ↦
    (mem_sievePrimes.mp (ht hp)).2.2
  have htOdd : ∀ p ∈ t, Odd p := fun p hp ↦ by
    have hp' := mem_sievePrimes.mp (ht hp)
    exact hp'.2.2.odd_of_ne_two (by omega)
  have hprodPos : 0 < ∏ p ∈ t, p :=
    Finset.prod_pos fun p hp ↦ (htPrime p hp).pos
  have hmod : IsRomanoffModulus (∏ p ∈ t, p) :=
    ⟨squarefree_primeProduct htPrime, odd_primeProduct htOdd⟩
  have htotient :
      (∏ p ∈ t, p).totient = ∏ p ∈ t, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod htPrime,
      Nat.div_self hprodPos, one_mul]
  rw [romanoffCoeff_eq_inv_totient hmod, htotient, Nat.cast_prod,
    one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (htPrime p hp).one_le]
  simp only [Nat.cast_one, one_div]

/-- Exact expansion of the truncated singular Euler product into Romanoff
coefficients. -/
theorem singularFactor_eq_sum_romanoffCoeff (h z y : ℕ) (hz : 2 ≤ z) :
    singularFactor h z y =
      ∑ q ∈ singularPrimeProducts z y with q ∣ h, romanoffCoeff q := by
  classical
  let P := sievePrimes z y
  let A := P.filter fun p ↦ p ∣ h
  let prodPrimes : Finset ℕ → ℕ := fun t ↦ ∏ p ∈ t, p
  have hPPrime : ∀ p ∈ P, p.Prime := fun p hp ↦
    (mem_sievePrimes.mp hp).2.2
  have hAPrime : ∀ p ∈ A, p.Prime := fun p hp ↦
    hPPrime p (Finset.mem_filter.mp hp).1
  have hinj : Set.InjOn prodPrimes A.powerset := by
    exact primeProduct_injOn_powerset A hAPrime
  have himage : A.powerset.image prodPrimes =
      (singularPrimeProducts z y).filter fun q ↦ q ∣ h := by
    ext q
    constructor
    · intro hq
      obtain ⟨t, htA, rfl⟩ := Finset.mem_image.mp hq
      have htASub : t ⊆ A := Finset.mem_powerset.mp htA
      have htPSub : t ⊆ P := fun p hp ↦
        (Finset.mem_filter.mp (htASub hp)).1
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_singularPrimeProducts.mpr
        exact ⟨t, htPSub, rfl⟩
      · apply Finset.prod_primes_dvd h
        · intro p hp
          exact (hAPrime p (htASub hp)).prime
        · intro p hp
          exact (Finset.mem_filter.mp (htASub hp)).2
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      obtain ⟨t, htPSub, hprod⟩ := mem_singularPrimeProducts.mp hq'.1
      subst q
      apply Finset.mem_image.mpr
      refine ⟨t, Finset.mem_powerset.mpr ?_, rfl⟩
      intro p hp
      apply Finset.mem_filter.mpr
      exact ⟨htPSub hp, (Finset.dvd_prod_of_mem id hp).trans hq'.2⟩
  calc
    singularFactor h z y =
        ∏ p ∈ A, (p : ℝ) / ((p : ℝ) - 1) := by
      unfold singularFactor
      exact (Finset.prod_filter (s := P) (fun p ↦ p ∣ h)
        (fun p ↦ (p : ℝ) / ((p : ℝ) - 1))).symm
    _ = ∏ p ∈ A, (1 + 1 / ((p : ℝ) - 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (hAPrime p hp).one_lt
      have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
      calc
        (p : ℝ) / ((p : ℝ) - 1) =
            (((p : ℝ) - 1) + 1) / ((p : ℝ) - 1) := by
          rw [sub_add_cancel]
        _ = ((p : ℝ) - 1) / ((p : ℝ) - 1) +
              1 / ((p : ℝ) - 1) := by rw [add_div]
        _ = 1 + 1 / ((p : ℝ) - 1) := by rw [div_self hne]
    _ = ∑ t ∈ A.powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1)) := by
      exact Finset.prod_one_add A
    _ = ∑ q ∈ singularPrimeProducts z y with q ∣ h,
          romanoffCoeff q := by
      rw [← himage, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro t ht
      exact (romanoffCoeff_primeProduct hz
        (fun p hp ↦ (Finset.mem_filter.mp
          ((Finset.mem_powerset.mp ht) hp)).1)).symm

end Erdos851
