/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.RomanoffSeries
import ErdosProblems.Erdos851.RomanoffEulerBound
import ErdosProblems.Erdos851.RomanoffProductBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# A finite container for the initial Romanoff sum

If the order of `2` modulo an odd integer `q` is at most `X`, then `q`
divides the single integer

`D_X = ∏_{1 ≤ r ≤ X} (2^r - 1)`.

This file records that elementary observation and the polynomial bound
`ω(D_X) ≤ X²`.  Thus any estimate for squarefree divisors of one fixed
integer can be applied uniformly to all moduli in the initial segment of the
Romanoff series.
-/

open scoped BigOperators

namespace Erdos851

noncomputable local instance instDecidableIsRomanoffModulusPartial (q : ℕ) :
    Decidable (IsRomanoffModulus q) := Classical.propDecidable _

/-- The product which contains every odd modulus whose order of two is at
most `X`. -/
def romanoffOrderProduct (X : ℕ) : ℕ :=
  ∏ r ∈ Finset.Icc 1 X, (2 ^ r - 1)

/-- Every factor occurring in `romanoffOrderProduct` is positive. -/
theorem romanoffOrderProduct_pos (X : ℕ) :
    0 < romanoffOrderProduct X := by
  unfold romanoffOrderProduct
  apply Finset.prod_pos
  intro r hr
  have hr1 : 0 < r := by
    have := (Finset.mem_Icc.mp hr).1
    omega
  exact Nat.sub_pos_iff_lt.mpr
    (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) hr1.ne')

/-- An odd modulus of order at most `X` divides the universal product
`romanoffOrderProduct X`.  Squarefreeness is deliberately not needed here. -/
theorem dvd_romanoffOrderProduct_of_twoOrder_le {q X : ℕ}
    (hq : Odd q) (hord : twoOrder q ≤ X) :
    q ∣ romanoffOrderProduct X := by
  have hordPos : 0 < twoOrder q := twoOrder_pos hq
  have hmem : twoOrder q ∈ Finset.Icc 1 X := by
    exact Finset.mem_Icc.mpr ⟨hordPos, hord⟩
  have hfactor : q ∣ 2 ^ twoOrder q - 1 :=
    twoOrder_dvd_iff_dvd_two_pow_sub_one.mp (dvd_refl _)
  exact hfactor.trans (Finset.dvd_prod_of_mem
    (fun r : ℕ ↦ 2 ^ r - 1) hmem)

/-- The exponents in the definition of `romanoffOrderProduct` have total at
most `X²`.  The deliberately coarse square bound is convenient downstream. -/
theorem sum_Icc_one_le_sq (X : ℕ) :
    (∑ r ∈ Finset.Icc 1 X, r) ≤ X ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 X, r) ≤
        ∑ _r ∈ Finset.Icc 1 X, X := by
      apply Finset.sum_le_sum
      intro r hr
      exact (Finset.mem_Icc.mp hr).2
    _ = (Finset.Icc 1 X).card * X := by simp
    _ ≤ X * X := by
      gcongr
      simp
    _ = X ^ 2 := by simp [pow_two]

/-- The universal product is at most `2^(X²)`. -/
theorem romanoffOrderProduct_le_two_pow_sq (X : ℕ) :
    romanoffOrderProduct X ≤ 2 ^ (X ^ 2) := by
  calc
    romanoffOrderProduct X =
        ∏ r ∈ Finset.Icc 1 X, (2 ^ r - 1) := rfl
    _ ≤ ∏ r ∈ Finset.Icc 1 X, 2 ^ r := by
      gcongr with r hr
      exact Nat.sub_le _ _
    _ = 2 ^ (∑ r ∈ Finset.Icc 1 X, r) := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ (X ^ 2) := by
      exact Nat.pow_le_pow_right (by norm_num) (sum_Icc_one_le_sq X)

/-- A positive integer has at least `2^ω(n)` elements in the product of
its distinct prime factors. -/
theorem two_pow_primeFactors_card_le {n : ℕ} (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n := by
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      apply Finset.pow_card_le_prod
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- The universal product has only polynomially many distinct prime
divisors. -/
theorem romanoffOrderProduct_primeFactors_card_le_sq (X : ℕ) :
    (romanoffOrderProduct X).primeFactors.card ≤ X ^ 2 := by
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
  exact (two_pow_primeFactors_card_le (romanoffOrderProduct_pos X)).trans
    (romanoffOrderProduct_le_two_pow_sq X)

/-- The universal order product is odd. -/
theorem romanoffOrderProduct_odd (X : ℕ) : Odd (romanoffOrderProduct X) := by
  unfold romanoffOrderProduct
  apply Finset.prod_induction (fun r : ℕ ↦ 2 ^ r - 1) Odd
  · intro a b ha hb
    exact ha.mul hb
  · exact odd_one
  · intro r hr
    have hrPos : 0 < r := by
      have := (Finset.mem_Icc.mp hr).1
      omega
    have heven : Even (2 ^ r) := even_two.pow_of_ne_zero hrPos.ne'
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) heven odd_one

/-- When the universal product has a prime divisor, the elementary finite
Euler-product estimate is controlled by `X⁴`.  The empty-prime-factor edge
case is kept separate because its Euler product equals one. -/
theorem romanoffOrderProduct_eulerProduct_fifth_le_sq
    (X : ℕ) (hne : (romanoffOrderProduct X).primeFactors.Nonempty) :
    (∏ p ∈ (romanoffOrderProduct X).primeFactors,
        (p : ℝ) / ((p : ℝ) - 1)) ^ 5 ≤
      8 * (((X ^ 2 : ℕ) : ℝ) ^ 2) := by
  have hprimeOdd : ∀ p ∈ (romanoffOrderProduct X).primeFactors,
      p.Prime ∧ Odd p := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    apply Nat.not_even_iff_odd.mp
    intro hpEven
    have htwoP : 2 ∣ p := even_iff_two_dvd.mp hpEven
    have htwoD : 2 ∣ romanoffOrderProduct X :=
      htwoP.trans (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.not_even_iff_odd.mpr (romanoffOrderProduct_odd X))
      (even_iff_two_dvd.mpr htwoD)
  calc
    (∏ p ∈ (romanoffOrderProduct X).primeFactors,
        (p : ℝ) / ((p : ℝ) - 1)) ^ 5 ≤
        8 * (((romanoffOrderProduct X).primeFactors.card : ℕ) : ℝ) ^ 2 :=
      oddPrimeProduct_fifth_le _ hne hprimeOdd
    _ ≤ 8 * (((X ^ 2 : ℕ) : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast romanoffOrderProduct_primeFactors_card_le_sq X

/-- Odd squarefree divisors of the universal product.  The divisor `1` is
retained, matching the totalized convention used by `romanoffCoeff`. -/
noncomputable def romanoffOrderDivisors (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (romanoffOrderProduct X).divisors.filter fun q ↦
      IsRomanoffModulus q

/-- Every odd squarefree modulus of order at most `X` occurs in
`romanoffOrderDivisors X`. -/
theorem mem_romanoffOrderDivisors_of_twoOrder_le {q X : ℕ}
    (hq : IsRomanoffModulus q) (hord : twoOrder q ≤ X) :
    q ∈ romanoffOrderDivisors X := by
  classical
  unfold romanoffOrderDivisors
  rw [Finset.mem_filter]
  refine ⟨Nat.mem_divisors.mpr ⟨?_, (romanoffOrderProduct_pos X).ne'⟩,
    hq⟩
  exact dvd_romanoffOrderProduct_of_twoOrder_le hq.2 hord

/-- The order-bounded moduli used by `RomanoffSeries` are all divisors of the
single universal product. -/
theorem romanoffModuliUpToOrder_subset_orderDivisors (X : ℕ) :
    romanoffModuliUpToOrder X ⊆ romanoffOrderDivisors X := by
  intro q hq
  rw [mem_romanoffModuliUpToOrder_iff] at hq
  exact mem_romanoffOrderDivisors_of_twoOrder_le hq.1 hq.2

/-- Consequently the finite cumulative Romanoff coefficient is bounded by a
squarefree-divisor sum of one fixed integer. -/
theorem sum_romanoffCoeff_moduli_le_sum_orderDivisors (X : ℕ) :
    (∑ q ∈ romanoffModuliUpToOrder X, romanoffCoeff q) ≤
      ∑ q ∈ romanoffOrderDivisors X, 1 / (q.totient : ℝ) := by
  calc
    (∑ q ∈ romanoffModuliUpToOrder X, romanoffCoeff q) =
        ∑ q ∈ romanoffModuliUpToOrder X, 1 / (q.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply romanoffCoeff_eq_inv_totient
      exact (mem_romanoffModuliUpToOrder_iff.mp hq).1
    _ ≤ ∑ q ∈ romanoffOrderDivisors X, 1 / (q.totient : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (romanoffModuliUpToOrder_subset_orderDivisors X)
      intro q hq _hqNot
      positivity

/-- The divisor sum in the cumulative Romanoff bound is at most the full
squarefree-divisor Euler product. -/
theorem sum_orderDivisors_inv_totient_le_product (X : ℕ) :
    (∑ q ∈ romanoffOrderDivisors X, 1 / (q.totient : ℝ)) ≤
      ∏ p ∈ (romanoffOrderProduct X).primeFactors,
        (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  apply sum_inv_totient_le_primeFactors_product
    (romanoffOrderProduct_pos X)
  intro q hq
  change q ∈ (romanoffOrderProduct X).divisors.filter IsRomanoffModulus at hq
  rw [Finset.mem_filter] at hq
  exact ⟨hq.2.2, hq.2.1, (Nat.mem_divisors.mp hq.1).1⟩

/-- Combined finite bound: every coefficient of order at most `X` is
controlled by the prime Euler product of `romanoffOrderProduct X`. -/
theorem sum_romanoffCoeff_moduli_le_product (X : ℕ) :
    (∑ q ∈ romanoffModuliUpToOrder X, romanoffCoeff q) ≤
      ∏ p ∈ (romanoffOrderProduct X).primeFactors,
        (p : ℝ) / ((p : ℝ) - 1) := by
  exact (sum_romanoffCoeff_moduli_le_sum_orderDivisors X).trans
    (sum_orderDivisors_inv_totient_le_product X)

/-- The elementary size bound `q < 2^X` for a nontrivial odd modulus whose
order is at most `X`. -/
theorem lt_two_pow_of_twoOrder_le {q X : ℕ}
    (hqOdd : Odd q) (_hq1 : 1 < q) (hord : twoOrder q ≤ X) :
    q < 2 ^ X := by
  exact (lt_two_pow_twoOrder hqOdd).trans_le
    (Nat.pow_le_pow_right (by norm_num) hord)

end Erdos851
