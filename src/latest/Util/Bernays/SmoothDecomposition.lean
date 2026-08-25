import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# Unique separation of a positive integer into its finite-prime and coprime parts
-/

open scoped Classical

namespace Bernays

def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ := (n.primeFactorsList.filter (· ∈ P)).prod

def avoidingPart (P : Finset ℕ) (n : ℕ) : ℕ := (n.primeFactorsList.filter (· ∉ P)).prod

theorem smoothPart_mem (P : Finset ℕ) (n : ℕ) : smoothPart P n ∈ Nat.factoredNumbers P :=
  Nat.prod_mem_factoredNumbers P n

theorem avoidingPart_pos (P : Finset ℕ) (n : ℕ) : 0 < avoidingPart P n := by
  apply Nat.pos_of_ne_zero
  apply List.prod_ne_zero
  intro h
  have hprime := Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter h)
  exact Nat.not_prime_zero hprime

theorem smoothPart_mul_avoidingPart (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothPart P n * avoidingPart P n = n := by
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun p : ℕ => p ∈ P) id n.primeFactorsList
  simpa only [smoothPart, avoidingPart, List.map_id, Nat.prod_primeFactorsList hn] using h

theorem avoidingPart_not_dvd (P : Finset ℕ) (n : ℕ) {p : ℕ} (hp : p.Prime) (hP : p ∈ P) :
    ¬ p ∣ avoidingPart P n := by
  intro hdvd
  have hmem := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hdvd
  have hnot : p ∉ P := by
    simpa only [decide_eq_true_eq] using List.of_mem_filter hmem
  exact hnot hP

theorem factored_coprime_of_avoiding {P : Finset ℕ} {m k : ℕ}
    (hm : m ∈ Nat.factoredNumbers P) (hk : ∀ p ∈ P, p.Prime → ¬ p ∣ k) : m.Coprime k := by
  by_contra h
  obtain ⟨p, hp, hpm, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hk p (Nat.mem_factoredNumbers'.mp hm p hp hpm) hp hpk

theorem smooth_decomposition_unique {P : Finset ℕ} {m k m' k' : ℕ}
    (hm : m ∈ Nat.factoredNumbers P) (hm' : m' ∈ Nat.factoredNumbers P)
    (hk : ∀ p ∈ P, p.Prime → ¬ p ∣ k) (hk' : ∀ p ∈ P, p.Prime → ¬ p ∣ k')
    (heq : m * k = m' * k') : m = m' ∧ k = k' := by
  have hc := factored_coprime_of_avoiding hm hk'
  have hc' := factored_coprime_of_avoiding hm' hk
  have hdiv : m ∣ m' := hc.dvd_mul_right.mp (heq ▸ dvd_mul_right m k)
  have hdiv' : m' ∣ m := hc'.dvd_mul_right.mp (heq.symm ▸ dvd_mul_right m' k')
  have heqm : m = m' := Nat.dvd_antisymm hdiv hdiv'
  refine ⟨heqm, ?_⟩
  rw [← heqm] at heq
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hm.1) heq

theorem avoidingPart_coprime {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    (avoidingPart M.primeFactors n).Coprime M := by
  by_contra h
  obtain ⟨p, hp, hpk, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact avoidingPart_not_dvd M.primeFactors n hp (Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩) hpk

theorem factored_coprime_of_coprime_level {M m k : ℕ}
    (hm : m ∈ Nat.factoredNumbers M.primeFactors) (hk : k.Coprime M) : m.Coprime k := by
  apply factored_coprime_of_avoiding hm
  intro p hp hprime hpk
  have hpM := (Nat.mem_primeFactors.mp hp).2.1
  exact hprime.not_dvd_one (hk.gcd_eq_one ▸ Nat.dvd_gcd hpk hpM)

end Bernays
