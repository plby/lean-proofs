import ErdosProblems.Erdos964.SelbergDiagonal

/-!
# The scalar dimension weights in the GGPY sieve

For local density `k/p`, the exact diagonal weight is the multiplicative
function with prime value `k/(p-k)`, denoted `1/f₁` in the paper.
-/

namespace Erdos964

open scoped BigOperators

noncomputable def dimensionSelbergWeight (k : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (k : ℝ) / ((p : ℝ) - k))

/-- The transformed second-moment weight `1/f₁*`: its dimension is
`k-1`, but the denominator is still `p-k`. -/
noncomputable def semiprimeSelbergWeight (k : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => ((k : ℝ) - 1) / ((p : ℝ) - k))

theorem semiprimeSelbergWeight_multiplicative (k : ℕ) :
    (semiprimeSelbergWeight k).IsMultiplicative := by
  unfold semiprimeSelbergWeight
  arith_mult

theorem dimensionSelbergWeight_multiplicative (k : ℕ) :
    (dimensionSelbergWeight k).IsMultiplicative := by
  unfold dimensionSelbergWeight
  arith_mult

theorem dimensionSelbergWeight_apply (k n : ℕ) (hn : n ≠ 0) :
    dimensionSelbergWeight k n = ∏ p ∈ n.primeFactors, (k : ℝ) / ((p : ℝ) - k) :=
  ArithmeticFunction.prodPrimeFactors_apply hn

theorem selberg_nu_eq_dimension_density (s : BoundingSieve) (k : ℕ)
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (k : ℝ) / p)
    (d : ℕ) (hd : d ∣ s.prodPrimes) :
    s.nu d = (k : ℝ) ^ d.primeFactors.card / d := by
  have hprod : (∏ p ∈ d.primeFactors, (p : ℝ)) = d := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.prod_primeFactors_of_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hd))
    simpa only [Nat.cast_prod] using h
  rw [← BoundingSieve.prod_primeFactors_nu hd]
  calc
    _ = ∏ p ∈ d.primeFactors, (k : ℝ) / p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hdensity p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hd)
    _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const, hprod]

theorem selbergTerms_eq_dimensionWeight (s : BoundingSieve) (k : ℕ)
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (k : ℝ) / p)
    (d : ℕ) (hd : d ∣ s.prodPrimes) :
    s.selbergTerms d = dimensionSelbergWeight k d := by
  have hdne := (s.prodPrimes_squarefree.squarefree_of_dvd hd).ne_zero
  rw [BoundingSieve.selbergTerms_apply, dimensionSelbergWeight_apply k d hdne,
    ← BoundingSieve.prod_primeFactors_nu hd, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hkp : (k : ℝ) < p := by
    have hlt := s.nu_lt_one_of_prime p hpprime hpP
    rw [hdensity p hpprime hpP] at hlt
    exact (div_lt_one hpR).mp hlt
  have hdiff : (p : ℝ) - k ≠ 0 := (sub_pos.mpr hkp).ne'
  rw [hdensity p hpprime hpP]
  field_simp

theorem scalarSelbergCoefficient_dimension_diagonal (s : BoundingSieve) (k : ℕ)
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (k : ℝ) / p)
    (y : ℕ → ℝ) :
    s.mainSum (BoundingSieve.lambdaSquared (scalarSelbergCoefficient s y)) =
      ∑ r ∈ s.prodPrimes.divisors, dimensionSelbergWeight k r * (y r) ^ 2 := by
  rw [scalarSelbergCoefficient_diagonal]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selbergTerms_eq_dimensionWeight s k hdensity r (Nat.dvd_of_mem_divisors hr)]

theorem selbergTerms_eq_semiprimeWeight (s : BoundingSieve) (k : ℕ)
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes →
      s.nu p = ((k : ℝ) - 1) / ((p : ℝ) - 1))
    (d : ℕ) (hd : d ∣ s.prodPrimes) :
    s.selbergTerms d = semiprimeSelbergWeight k d := by
  have hdne := (s.prodPrimes_squarefree.squarefree_of_dvd hd).ne_zero
  rw [BoundingSieve.selbergTerms_apply, semiprimeSelbergWeight,
    ArithmeticFunction.prodPrimeFactors_apply hdne,
    ← BoundingSieve.prod_primeFactors_nu hd, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
  have hden : (0 : ℝ) < p - 1 := by linarith
  have hkp : (k : ℝ) < p := by
    have hlt := s.nu_lt_one_of_prime p hpprime hpP
    rw [hdensity p hpprime hpP] at hlt
    have := (div_lt_one hden).mp hlt
    linarith
  have hdiff : (p : ℝ) - k ≠ 0 := (sub_pos.mpr hkp).ne'
  rw [hdensity p hpprime hpP]
  have hid : 1 - ((k : ℝ) - 1) / ((p : ℝ) - 1) =
      ((p : ℝ) - k) / ((p : ℝ) - 1) := by
    field_simp
    ring
  rw [hid, inv_div]
  field_simp

end Erdos964
