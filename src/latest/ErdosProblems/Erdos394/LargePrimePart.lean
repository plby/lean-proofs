import ErdosProblems.Erdos394.PrimeBrun
import ErdosProblems.Erdos394.SymmetricTail
import ErdosProblems.Erdos394.Structural

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Union bounds for integers divisible by many primes
-/

open Nat Finset

namespace Erdos394

/-- Positive multiples of `d` not exceeding `X`. -/
def positiveMultiplesUpTo (X d : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n ↦ n ≠ 0 ∧ d ∣ n)

@[simp]
theorem card_positiveMultiplesUpTo (X d : ℕ) :
    (positiveMultiplesUpTo X d).card = X / d := by
  simpa [positiveMultiplesUpTo, Nat.succ_eq_add_one] using Nat.card_multiples' X d

/-- Positive integers up to `X` divisible by at least `r` primes from `P`. -/
def manyPrimeDivisors (P : Finset ℕ) (r X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ r ≤ (badPrimeSet P n).card)

/-- Every integer with at least `r` bad primes belongs to the union of the
multiples of the products of the `r`-subsets. -/
theorem manyPrimeDivisors_subset_biUnion
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    manyPrimeDivisors P r X ⊆
      (P.powersetCard r).biUnion
        (fun T ↦ positiveMultiplesUpTo X (∏ p ∈ T, p)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨T, hTbad, hcard⟩ :=
    Finset.exists_subset_card_eq hn'.2.2
  have hTP : T ⊆ P := hTbad.trans (by
    intro p hp
    exact (Finset.mem_filter.mp hp).1)
  have hprod : (∏ p ∈ T, p) ∣ n :=
    (subset_badPrimeSet_iff_prod_dvd hprime n).mp hTbad |>.2
  apply Finset.mem_biUnion.mpr
  refine ⟨T, Finset.mem_powersetCard.mpr ⟨hTP, hcard⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1, hprod⟩

/-- The elementary union bound before applying the factorial estimate. -/
theorem card_manyPrimeDivisors_le_mul_elementarySum
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    ((manyPrimeDivisors P r X).card : ℝ) ≤
      (X : ℝ) * elementarySum P (fun p ↦ 1 / (p : ℝ)) r := by
  have hcardNat : (manyPrimeDivisors P r X).card ≤
      ∑ T ∈ P.powersetCard r, X / (∏ p ∈ T, p) := by
    calc
      (manyPrimeDivisors P r X).card ≤
          ((P.powersetCard r).biUnion
            (fun T ↦ positiveMultiplesUpTo X (∏ p ∈ T, p))).card :=
        Finset.card_le_card (manyPrimeDivisors_subset_biUnion P hprime r X)
      _ ≤ ∑ T ∈ P.powersetCard r,
          (positiveMultiplesUpTo X (∏ p ∈ T, p)).card :=
        Finset.card_biUnion_le
      _ = ∑ T ∈ P.powersetCard r, X / (∏ p ∈ T, p) := by
        apply Finset.sum_congr rfl
        intro T _
        rw [card_positiveMultiplesUpTo]
  calc
    ((manyPrimeDivisors P r X).card : ℝ) ≤
        ∑ T ∈ P.powersetCard r,
          ((X / (∏ p ∈ T, p) : ℕ) : ℝ) := by exact_mod_cast hcardNat
    _ ≤ ∑ T ∈ P.powersetCard r,
          (X : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro T hT
      exact Nat.cast_div_le
    _ = (X : ℝ) * elementarySum P (fun p ↦ 1 / (p : ℝ)) r := by
      unfold elementarySum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      calc
        (X : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) =
            (X : ℝ) * (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) := by ring
        _ = (X : ℝ) * ∏ p ∈ T, (1 / (p : ℝ)) := by
          rw [one_div_cast_prod_eq_prod_one_div]

/-- The squarefree product of the bad primes selected from `P`. -/
def primePart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ badPrimeSet P n, p

/-- If all primes in `P` are at most `y`, then the selected prime part is at
most `y` to the number of selected primes. -/
theorem primePart_le_pow_card (P : Finset ℕ) {y n : ℕ}
    (hPy : ∀ p ∈ P, p ≤ y) :
    primePart P n ≤ y ^ (badPrimeSet P n).card := by
  unfold primePart
  calc
    (∏ p ∈ badPrimeSet P n, p) ≤
        ∏ _p ∈ badPrimeSet P n, y := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        exact hPy p (Finset.mem_filter.mp hp).1
    _ = y ^ (badPrimeSet P n).card := by simp

/-- Positive integers up to `X` whose selected prime part exceeds `y^R`. -/
def largePrimePart (P : Finset ℕ) (R X y : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter
    (fun n ↦ n ≠ 0 ∧ y ^ R < primePart P n)

/-- A prime part larger than `y^R` forces at least `R+1` selected primes. -/
theorem largePrimePart_subset_manyPrimeDivisors
    (P : Finset ℕ) {R X y : ℕ} (hy : 0 < y)
    (hPy : ∀ p ∈ P, p ≤ y) :
    largePrimePart P R X y ⊆ manyPrimeDivisors P (R + 1) X := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hn'.1, hn'.2.1, ?_⟩
  have hpart := primePart_le_pow_card P (n := n) hPy
  by_contra hcard
  have hcardle : (badPrimeSet P n).card ≤ R := by omega
  have hpow : y ^ (badPrimeSet P n).card ≤ y ^ R :=
    Nat.pow_le_pow_right hy hcardle
  omega

/-- Factorial-form union bound for having at least `r` distinct prime
divisors from `P`. -/
theorem card_manyPrimeDivisors_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (r X : ℕ) :
    ((manyPrimeDivisors P r X).card : ℝ) ≤
      (X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ r / (r.factorial : ℝ)) := by
  have hbase := card_manyPrimeDivisors_le_mul_elementarySum P hprime r X
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hfac := factorial_mul_elementarySum_le_pow_sum
    P (fun p ↦ 1 / (p : ℝ)) hx0 r
  have he : elementarySum P (fun p ↦ 1 / (p : ℝ)) r ≤
      (∑ p ∈ P, (1 / (p : ℝ))) ^ r / (r.factorial : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- Factorial-tail bound for the number of integers whose selected prime part
exceeds `y^R`. -/
theorem card_largePrimePart_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {R X y : ℕ} (hy : 0 < y) (hPy : ∀ p ∈ P, p ≤ y) :
    ((largePrimePart P R X y).card : ℝ) ≤
      (X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by
  have hsub : ((largePrimePart P R X y).card : ℝ) ≤
      ((manyPrimeDivisors P (R + 1) X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (largePrimePart_subset_manyPrimeDivisors P hy hPy)
  exact hsub.trans
    (card_manyPrimeDivisors_le_factorial_tail P hprime (R + 1) X)

/-- The trivial bound `t₂(n)≤n` turns the large-prime-part census into its
contribution to the target sum. -/
theorem sum_t_two_largePrimePart_le_factorial_tail
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {R X y : ℕ} (hy : 0 < y) (hPy : ∀ p ∈ P, p ≤ y) :
    (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
      (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by
  have hpoint : ∀ n ∈ largePrimePart P R X y, (t 2 n : ℝ) ≤ (X : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn'.2.1
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp hn'.1
      omega
    exact_mod_cast (t_le_self (by norm_num : 0 < 2) hnpos).trans hnX
  have hsum : (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
      (X : ℝ) * (largePrimePart P R X y).card := by
    calc
      (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
          ∑ _n ∈ largePrimePart P R X y, (X : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (X : ℝ) * (largePrimePart P R X y).card := by
        simp [mul_comm]
  have hcard := card_largePrimePart_le_factorial_tail P hprime
    (R := R) (X := X) (y := y) hy hPy
  calc
    (∑ n ∈ largePrimePart P R X y, (t 2 n : ℝ)) ≤
        (X : ℝ) * (largePrimePart P R X y).card := hsum
    _ ≤ (X : ℝ) * ((X : ℝ) *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (X : ℝ) ^ 2 *
        ((∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ)) := by ring

end Erdos394
