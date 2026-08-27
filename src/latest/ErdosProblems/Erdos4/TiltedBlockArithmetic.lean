import ErdosProblems.Erdos4.TiltedGlobalCorrelation

/-! Prime support, squarefreeness, and size of the common block product. -/

open scoped BigOperators

namespace Erdos4.Tilted

theorem primeFactors_prod_subset (T S : Finset ℕ)
    (hpos : ∀ n ∈ T, 0 < n) (hfactors : ∀ n ∈ T, n.primeFactors ⊆ S) :
    (∏ n ∈ T, n).primeFactors ⊆ S := by
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpdiv := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨n, hn, hpn⟩ := ((Nat.prime_iff.mp hpprime).dvd_finsetProd_iff (fun n : ℕ => n)).mp hpdiv
  exact hfactors n hn (Nat.mem_primeFactors.mpr ⟨hpprime, hpn, (hpos n hn).ne'⟩)

theorem blockGcd_squarefree (T U : Finset ℕ) (hT : Squarefree (∏ n ∈ T, n)) :
    Squarefree (blockGcd T U) :=
  hT.squarefree_of_dvd (Nat.gcd_dvd_left _ _)

theorem blockGcd_factors_subset (T U S : Finset ℕ)
    (hpos : ∀ n ∈ T, 0 < n) (hfactors : ∀ n ∈ T, n.primeFactors ⊆ S) :
    (blockGcd T U).primeFactors ⊆ S := by
  have hprod : (∏ n ∈ T, n) ≠ 0 := (Finset.prod_pos hpos).ne'
  exact (Nat.primeFactors_mono (Nat.gcd_dvd_left _ _) hprod).trans
    (primeFactors_prod_subset T S hpos hfactors)

theorem blockGcd_le_pow (T U : Finset ℕ) {Y K : ℕ} (hY : 1 ≤ Y)
    (hpos : ∀ n ∈ T, 0 < n) (hbound : ∀ n ∈ T, n ≤ Y) (hcard : T.card ≤ K) :
    blockGcd T U ≤ Y ^ K := by
  have hprod : 0 < ∏ n ∈ T, n := Finset.prod_pos hpos
  calc
    _ ≤ ∏ n ∈ T, n := Nat.gcd_le_left _ hprod
    _ ≤ ∏ _n ∈ T, Y := Finset.prod_le_prod' hbound
    _ = Y ^ T.card := Finset.prod_const Y
    _ ≤ _ := Nat.pow_le_pow_right hY hcard

end Erdos4.Tilted
