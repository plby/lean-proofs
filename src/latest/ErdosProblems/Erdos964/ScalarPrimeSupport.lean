import ErdosProblems.Erdos964.AffinePrimeRoots
import ErdosProblems.Erdos964.SelbergDimension

/-!
# Prime support for the scalar sieve

The finite support contains exactly the primes up to the radius which
do not divide the normalization modulus. Below the radius, its divisors
are exactly the squarefree integers coprime to that fixed modulus.
-/

namespace Erdos964

open scoped BigOperators

def scalarSievePrimeProduct (M R : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primesLE R).filter (fun p => ¬ p ∣ M), p

theorem scalarSievePrimeProduct_squarefree (M R : ℕ) :
    Squarefree (scalarSievePrimeProduct M R) := by
  apply (squarefree_primorial R).squarefree_of_dvd
  rw [scalarSievePrimeProduct, primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem prime_dvd_scalarSievePrimeProduct (M R p : ℕ) (hp : p.Prime) :
    p ∣ scalarSievePrimeProduct M R ↔ p ≤ R ∧ ¬ p ∣ M := by
  unfold scalarSievePrimeProduct
  constructor
  · intro hpP
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpP
    have hq' := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primesLE hq'.1
    have hpqeq : p = q := (Nat.dvd_prime hqprime).mp hpq |>.resolve_left hp.ne_one
    subst q
    exact ⟨Nat.le_of_mem_primesLE hq'.1, hq'.2⟩
  · rintro ⟨hpR, hpM⟩
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpR, hp⟩, hpM⟩)

theorem scalarSievePrimeProduct_coprime (M R : ℕ) :
    (scalarSievePrimeProduct M R).Coprime M := by
  unfold scalarSievePrimeProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact (Nat.prime_of_mem_primesLE hp'.1).coprime_iff_not_dvd.mpr hp'.2

theorem dvd_scalarSievePrimeProduct_iff (M R u : ℕ) (huR : u ≤ R) :
    u ∣ scalarSievePrimeProduct M R ↔ Squarefree u ∧ u.Coprime M := by
  constructor
  · intro hu
    exact ⟨(scalarSievePrimeProduct_squarefree M R).squarefree_of_dvd hu,
      (scalarSievePrimeProduct_coprime M R).coprime_dvd_left hu⟩
  · rintro ⟨hsq, hcop⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply (Nat.prod_primeFactors_dvd_iff (scalarSievePrimeProduct_squarefree M R).ne_zero).mpr
    intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have hpu := Nat.dvd_of_mem_primeFactors hpMem
    apply Nat.mem_primeFactors.mpr
    refine ⟨hp, ?_, (scalarSievePrimeProduct_squarefree M R).ne_zero⟩
    apply (prime_dvd_scalarSievePrimeProduct M R p hp).mpr
    refine ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) hpu).trans huR, ?_⟩
    exact hp.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hpu)

theorem scalarSievePrimeProduct_good (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (R p : ℕ) (hp : p.Prime)
    (hpP : p ∣ scalarSievePrimeProduct (affineNormalizationModulus A B) R) : 3 < p := by
  have hpM := (prime_dvd_scalarSievePrimeProduct _ R p hp).mp hpP |>.2
  by_contra h
  exact hpM (small_prime_dvd_affine_normalization A B hA hne hadm p hp (by omega))

theorem scalarSievePrimeProduct_divisors_below (M R : ℕ) :
    (scalarSievePrimeProduct M R).divisors.filter (fun u => u < R) =
      (Finset.Ico 1 R).filter (fun u => Squarefree u ∧ u.Coprime M) := by
  classical
  ext u
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hu, _⟩, huR⟩
    have hdata := (dvd_scalarSievePrimeProduct_iff M R u huR.le).mp hu
    exact ⟨⟨Nat.pos_of_ne_zero hdata.1.ne_zero, huR⟩, hdata⟩
  · rintro ⟨⟨_, huR⟩, hsq, hcop⟩
    exact ⟨⟨(dvd_scalarSievePrimeProduct_iff M R u huR.le).mpr ⟨hsq, hcop⟩,
      (scalarSievePrimeProduct_squarefree M R).ne_zero⟩, huR⟩

theorem sum_scalarSievePrimeProduct_divisors_eq_fixed_modulus_sum (M R : ℕ)
    (F : ℕ → ℝ) (hcut : ∀ u, R ≤ u → F u = 0) :
    (∑ u ∈ (scalarSievePrimeProduct M R).divisors, F u) =
      ∑ u ∈ (Finset.Ico 1 R).filter (fun u => Squarefree u ∧ u.Coprime M), F u := by
  rw [← scalarSievePrimeProduct_divisors_below, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases huR : u < R
  · rw [if_pos huR]
  · rw [if_neg huR, hcut u (Nat.le_of_not_gt huR)]

end Erdos964
