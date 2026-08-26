import ErdosProblems.Erdos69.RoughSizeBounds

/-!
# Adding collision primes without changing dilation valuations

Only prime factors not already in the product of the dilations are added.
Consequently division by any one dilation leaves a coprime progression step.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def newPrimeFactors (A D : ℕ) : Finset ℕ := D.primeFactors.filter (fun p ↦ ¬p ∣ A)

def newPrimeProduct (A D : ℕ) : ℕ := ∏ p ∈ newPrimeFactors A D, p

def augmentedModulus (A D : ℕ) : ℕ := A * newPrimeProduct A D

theorem newPrimeProduct_pos (A D : ℕ) : 0 < newPrimeProduct A D := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos

theorem newPrimeProduct_dvd (A D : ℕ) : newPrimeProduct A D ∣ D := by
  apply dvd_trans _ (Nat.prod_primeFactors_dvd D)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem newPrimeProduct_coprime (A D : ℕ) : A.Coprime (newPrimeProduct A D) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpD, hpA⟩ := Finset.mem_filter.mp hp
  exact (Nat.Prime.coprime_iff_not_dvd (Nat.mem_primeFactors.mp hpD).1).mpr hpA |>.symm

theorem augmentedModulus_pos {A D : ℕ} (hA : 0 < A) : 0 < augmentedModulus A D :=
  Nat.mul_pos hA (newPrimeProduct_pos A D)

theorem dvd_augmentedModulus (A D : ℕ) : A ∣ augmentedModulus A D := dvd_mul_right _ _

theorem prime_dvd_augmentedModulus {A D p : ℕ} (hD : D ≠ 0) (hp : p.Prime)
    (hpD : p ∣ D) : p ∣ augmentedModulus A D := by
  by_cases hpA : p ∣ A
  · exact hpA.trans (dvd_augmentedModulus A D)
  · apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, hpD, hD⟩, hpA⟩)

theorem log_augmentedModulus_le {A D : ℕ} (hA : 0 < A) (hD : 0 < D) :
    Real.log (augmentedModulus A D : ℝ) ≤ Real.log A + Real.log D := by
  have hR := newPrimeProduct_pos A D
  have hle := Nat.le_of_dvd hD (newPrimeProduct_dvd A D)
  rw [augmentedModulus, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  gcongr

theorem coprime_augmentedModulus_quotient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hc : Pairwise (fun i j ↦ (a i).Coprime (a j))) (D : ℕ) (i : ι) :
    (augmentedModulus (∏ j, a j) D / a i).Coprime (a i) := by
  let A := ∏ j, a j
  have hprod : A = a i * ∏ j ∈ Finset.univ.erase i, a j := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hadvd : a i ∣ A := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hr : (newPrimeProduct A D).Coprime (a i) :=
    (newPrimeProduct_coprime A D).symm.of_dvd_right hadvd
  have hcprod : (∏ j ∈ Finset.univ.erase i, a j).Coprime (a i) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro j hj
    exact hc (Finset.mem_erase.mp hj).1
  change (A * newPrimeProduct A D / a i).Coprime (a i)
  nth_rw 1 [hprod]
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (ha i)]
  exact hcprod.mul_left hr

end Erdos69.Elementary
