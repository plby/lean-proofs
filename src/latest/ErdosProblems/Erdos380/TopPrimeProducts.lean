import ErdosProblems.Erdos380.PrimeProducts
import ErdosProblems.Erdos380.Intervals
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Uniqueness after removing a fixed number of largest prime factors

If an integer is a product of `k` primes, all larger than every prime
factor of its remaining cofactor, then the cofactor is uniquely determined.
The ordered tuple is determined up to permutation.
-/

open scoped BigOperators

namespace Erdos380

lemma prime_tuple_product_eq_of_dvd {k : ℕ} {f g : Fin k → ℕ}
    (hf : ∀ i, (f i).Prime) (hg : ∀ i, (g i).Prime)
    (hd : (∏ i, f i) ∣ ∏ i, g i) : (∏ i, f i) = ∏ i, g i := by
  have hf0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hf i).ne_zero
  have hg0 : (∏ i, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hg i).ne_zero
  have hfl : (List.ofFn f).Perm (∏ i, f i).primeFactorsList :=
    Nat.primeFactorsList_unique List.prod_ofFn (List.forall_mem_ofFn_iff.mpr hf)
  have hgl : (List.ofFn g).Perm (∏ i, g i).primeFactorsList :=
    Nat.primeFactorsList_unique List.prod_ofFn (List.forall_mem_ofFn_iff.mpr hg)
  have hsub := Nat.primeFactorsList_sublist_of_dvd hd hg0
  have hlen : (∏ i, f i).primeFactorsList.length = (∏ i, g i).primeFactorsList.length := by
    have hfl' := hfl.length_eq
    have hgl' := hgl.length_eq
    simp only [List.length_ofFn] at hfl' hgl'
    exact hfl'.symm.trans hgl'
  have heq := hsub.eq_of_length hlen
  have hprod := congrArg List.prod heq
  simpa only [Nat.prod_primeFactorsList hf0, Nat.prod_primeFactorsList hg0] using hprod

lemma top_prime_product_cofactor_eq_of_le {k b c : ℕ} {f g : Fin k → ℕ}
    (hb : 0 < b) (hf : ∀ i, (f i).Prime) (hg : ∀ i, (g i).Prime)
    (hbc : largestPrimeFactor b ≤ largestPrimeFactor c)
    (hgc : ∀ i, largestPrimeFactor c < g i)
    (hprod : (∏ i, f i) * b = (∏ i, g i) * c) : b = c := by
  have hcop : Nat.Coprime (∏ i, g i) b := by
    apply Nat.coprime_fintype_prod_left_iff.mpr
    intro i
    apply (hg i).coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le_of_gt (hgc i)) ((prime_le_largestPrimeFactor hb.ne' (hg i) hd).trans hbc)
  have hd : (∏ i, g i) ∣ (∏ i, f i) * b := by
    rw [hprod]
    exact dvd_mul_right _ _
  have hdiv : (∏ i, g i) ∣ ∏ i, f i := hcop.dvd_of_dvd_mul_right hd
  have heq := prime_tuple_product_eq_of_dvd hg hf hdiv
  rw [heq] at hprod
  exact Nat.eq_of_mul_eq_mul_left (Finset.prod_pos fun i _ => (hf i).pos) hprod

theorem top_prime_product_cofactor_unique {k b c : ℕ} {f g : Fin k → ℕ}
    (hb : 0 < b) (hc : 0 < c) (hf : ∀ i, (f i).Prime) (hg : ∀ i, (g i).Prime)
    (hfb : ∀ i, largestPrimeFactor b < f i) (hgc : ∀ i, largestPrimeFactor c < g i)
    (hprod : (∏ i, f i) * b = (∏ i, g i) * c) :
    b = c ∧ (List.ofFn f).Perm (List.ofFn g) := by
  have hbc : b = c := by
    rcases le_total (largestPrimeFactor b) (largestPrimeFactor c) with h | h
    · exact top_prime_product_cofactor_eq_of_le hb hf hg h hgc hprod
    · exact (top_prime_product_cofactor_eq_of_le hc hg hf h hfb hprod.symm).symm
  refine ⟨hbc, ?_⟩
  have hfg : (∏ i, f i) = ∏ i, g i := by
    rw [hbc] at hprod
    exact Nat.eq_of_mul_eq_mul_right hc hprod
  exact (Nat.primeFactorsList_unique
    (by simpa only [List.prod_ofFn] using hfg) (List.forall_mem_ofFn_iff.mpr hf)).trans
    (Nat.primeFactorsList_unique List.prod_ofFn (List.forall_mem_ofFn_iff.mpr hg)).symm

end Erdos380
