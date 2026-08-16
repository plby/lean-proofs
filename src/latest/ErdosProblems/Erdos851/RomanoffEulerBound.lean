/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

/-!
# A divisor Euler-product bound for Erdős problem 851

An odd squarefree divisor of a positive integer `D` is determined by a subset
of `D.primeFactors`.  Euler's product formula therefore bounds the sum of the
reciprocals of the totients of any finite collection of such divisors by the
full Euler product over `D.primeFactors`.
-/

open scoped BigOperators

namespace Erdos851

private theorem totient_eq_primeFactors_sub_one_prod {q : ℕ}
    (hq : Squarefree q) :
    q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree hq]
  rw [Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]

private theorem inv_totient_eq_primeFactors_prod {q : ℕ}
    (hq : Squarefree q) :
    1 / (q.totient : ℝ) =
      ∏ p ∈ q.primeFactors, (1 / ((p : ℝ) - 1)) := by
  rw [totient_eq_primeFactors_sub_one_prod hq, Nat.cast_prod]
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
  simp only [Nat.cast_one, one_div]

/-- If every member of `S` is an odd squarefree divisor of the positive
integer `D`, then the reciprocal-totient sum over `S` is at most the complete
Euler product over the prime factors of `D`.

The oddness hypothesis records the application to Romanoff's series.  The
finite combinatorial estimate itself only uses squarefreeness and divisibility.
-/
theorem sum_inv_totient_le_primeFactors_product {D : ℕ} (hD : 0 < D)
    (S : Finset ℕ)
    (hS : ∀ q ∈ S, Odd q ∧ Squarefree q ∧ q ∣ D) :
    (∑ q ∈ S, 1 / (q.totient : ℝ)) ≤
      ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  let weight : Finset ℕ → ℝ := fun t ↦
    ∏ p ∈ t, (1 / ((p : ℝ) - 1))
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro q hq r hr hqr
    rw [← Nat.prod_primeFactors_of_squarefree (hS q hq).2.1,
      ← Nat.prod_primeFactors_of_squarefree (hS r hr).2.1, hqr]
  have hsub : S.image Nat.primeFactors ⊆ D.primeFactors.powerset := by
    intro t ht
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (hS q hqS).2.2 hD.ne'
  have hweight_nonneg : ∀ t ∈ D.primeFactors.powerset, 0 ≤ weight t := by
    intro t ht
    apply Finset.prod_nonneg
    intro p hp
    have hpD : p ∈ D.primeFactors := (Finset.mem_powerset.mp ht) hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpD).one_lt
    positivity
  calc
    (∑ q ∈ S, 1 / (q.totient : ℝ)) =
        ∑ t ∈ S.image Nat.primeFactors, weight t := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro q hq
      exact inv_totient_eq_primeFactors_prod (hS q hq).2.1
    _ ≤ ∑ t ∈ D.primeFactors.powerset, weight t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun t ht _htImage ↦ hweight_nonneg t ht)
    _ = ∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
      simpa only [weight] using
        (Finset.prod_one_add (R := ℝ) D.primeFactors
          (f := fun p : ℕ ↦ 1 / ((p : ℝ) - 1))).symm
    _ = ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : (1 : ℝ) < p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
      calc
        1 + 1 / ((p : ℝ) - 1) =
            ((p : ℝ) - 1) / ((p : ℝ) - 1) +
              1 / ((p : ℝ) - 1) := by rw [div_self hne]
        _ = (((p : ℝ) - 1) + 1) / ((p : ℝ) - 1) := by
          rw [add_div]
        _ = (p : ℝ) / ((p : ℝ) - 1) := by
          rw [sub_add_cancel]

end Erdos851
