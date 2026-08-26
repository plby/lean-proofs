/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientIncidence

/-!
# The exact totient denominator with one forced prime

At the forced prime the denominator is `p - 1` even for the empty
coefficient state. At every other prime it is present exactly when
the reconstructed divisor tuple occupies that prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem prime_dvd_reconstructed_flat_lcm_iff
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (p : P) :
    p.val ∣ (Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
      (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2) ↔ c p ≠ none := by
  rw [lcm_doubledPrimeChoiceDivisor P hP,
    prime_dvd_primeFinsetProduct_iff _
      (fun q hq ↦ hP q (selectedCutoffPrimes_subset P c _ hq)) (hP p p.property),
    mem_selectedCutoffPrimes P c (· ≠ none) p]

open Classical in
theorem totient_lcm_reconstructed_forced_prime
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (p : P) :
    (Nat.totient (Nat.lcm
      ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
        (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2)) p.val) : ℂ) =
      ((p.val : ℂ) - 1) * ∏ r ∈ (Finset.univ : Finset P).erase p,
        if c r = none then 1 else ((r.val : ℂ) - 1) := by
  classical
  let Q := (Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
    (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2)
  let f (r : P) : ℂ := if c r = none then 1 else ((r.val : ℂ) - 1)
  have hφ : (Nat.totient Q : ℂ) = ∏ r : P, f r := totient_lcm_doubledPrimeChoiceDivisor P hP c
  have hprod := Finset.mul_prod_erase (Finset.univ : Finset P) f (Finset.mem_univ p)
  change (Nat.totient (Nat.lcm Q p.val) : ℂ) = ((p.val : ℂ) - 1) *
    ∏ r ∈ (Finset.univ : Finset P).erase p, f r
  by_cases hc : c p = none
  · have hpQ : ¬p.val ∣ Q := by
      rw [prime_dvd_reconstructed_flat_lcm_iff P hP c p]
      exact not_not.mpr hc
    have hcop : Q.Coprime p.val := ((hP p p.property).coprime_iff_not_dvd.mpr hpQ).symm
    rw [hcop.lcm_eq_mul, Nat.totient_mul hcop, Nat.totient_prime (hP p p.property)]
    push_cast
    rw [hφ, ← hprod]
    have hpcast : ((p.val - 1 : ℕ) : ℂ) = (p.val : ℂ) - 1 := by
      simp only [Nat.cast_sub (hP p p.property).one_lt.le, Nat.cast_one]
    rw [hpcast]
    simp only [f, if_pos hc, one_mul]
    ring
  · have hpQ : p.val ∣ Q := (prime_dvd_reconstructed_flat_lcm_iff P hP c p).mpr hc
    rw [Nat.lcm_eq_left hpQ, hφ, ← hprod]
    simp only [f, if_neg hc]

open Classical in
theorem totient_lcm_reconstructed_forced_prime_product
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : P → DoubledPrimeChoice ι) (p : P) :
    (Nat.totient (Nat.lcm
      ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
        (fun ib ↦ doubledPrimeChoiceDivisor P c ib.1 ib.2)) p.val) : ℂ) =
      ∏ r : P, if r = p ∨ c r ≠ none then ((r.val : ℂ) - 1) else 1 := by
  rw [totient_lcm_reconstructed_forced_prime P hP c p,
    ← Finset.mul_prod_erase (Finset.univ : Finset P)
      (fun r : P ↦ if r = p ∨ c r ≠ none then ((r.val : ℂ) - 1) else 1)
      (Finset.mem_univ p)]
  simp only [true_or, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  have hrp := (Finset.mem_erase.mp hr).1
  simp only [hrp, false_or, ite_not]

end

end Erdos4b
