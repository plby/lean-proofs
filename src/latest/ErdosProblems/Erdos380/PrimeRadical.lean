import ErdosProblems.Erdos380.SmallPrimeMoments

/-! # Square divisors and the logarithmic mass of distinct prime factors -/

open scoped BigOperators

namespace Erdos380

def primeRadical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma primeRadical_pos (n : ℕ) : 0 < primeRadical n :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma primeRadical_dvd (n : ℕ) : primeRadical n ∣ n := Nat.prod_primeFactors_dvd n

lemma squarefree_le_primeRadical_of_dvd {a n : ℕ}
    (ha : Squarefree a) (hn : 0 < n) (han : a ∣ n) : a ≤ primeRadical n := by
  have hsubset : a.primeFactors ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans han, hn.ne'⟩
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  apply Nat.le_of_dvd (primeRadical_pos n)
  exact Finset.prod_dvd_prod_of_subset _ _ id hsubset

/-- If every square divisor has square root below `D`, the radical loses
at most the factor `D²`. -/
theorem le_square_cutoff_mul_primeRadical {n D : ℕ} (hn : 0 < n)
    (hD : ∀ d : ℕ, d ^ 2 ∣ n → d ≤ D) : n ≤ D ^ 2 * primeRadical n := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hadvd : a ∣ n := by rw [← hab]; exact dvd_mul_left _ _
  have hbdiv : b ^ 2 ∣ n := by rw [← hab]; exact dvd_mul_right _ _
  calc
    n = b ^ 2 * a := hab.symm
    _ ≤ D ^ 2 * primeRadical n := Nat.mul_le_mul (Nat.pow_le_pow_left (hD b hbdiv) 2)
      (squarefree_le_primeRadical_of_dvd hsq hn hadvd)

lemma log_primeRadical (n : ℕ) :
    Real.log (primeRadical n : ℝ) = ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
  rw [primeRadical, Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem log_le_square_cutoff_add_primeFactors {n D : ℕ}
    (hn : 0 < n) (hDpos : 0 < D) (hD : ∀ d : ℕ, d ^ 2 ∣ n → d ≤ D) :
    Real.log (n : ℝ) ≤ 2 * Real.log (D : ℝ) + ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hradR : (primeRadical n : ℝ) ≠ 0 := by exact_mod_cast (primeRadical_pos n).ne'
  calc
    Real.log (n : ℝ) ≤ Real.log (D ^ 2 * primeRadical n : ℝ) := by
      apply Real.log_le_log hnR
      exact_mod_cast le_square_cutoff_mul_primeRadical hn hD
    _ = _ := by rw [Real.log_mul (pow_ne_zero 2 hDR) hradR, Real.log_pow, log_primeRadical]; norm_num

lemma sum_log_distinct_prime_divisors_le {t : Finset ℕ} {n : ℕ}
    (hn : 0 < n) (ht : ∀ p ∈ t, p.Prime) (hd : ∀ p ∈ t, p ∣ n) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  have hprod : (∏ p ∈ t, p) ∣ n := Finset.prod_primes_dvd n (fun p hp => (ht p hp).prime) hd
  have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp => (ht p hp).pos
  have hcast : (0 : ℝ) < ∏ p ∈ t, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hpos
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (ht p hp).ne_zero)]
  exact Real.log_le_log hcast (by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn hprod)

lemma sum_log_distinct_prime_divisors_int_le {t : Finset ℕ} {h : ℤ}
    (hh : h ≠ 0) (ht : ∀ p ∈ t, p.Prime) (hd : ∀ p ∈ t, (p : ℤ) ∣ h) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (h.natAbs : ℝ) := by
  apply sum_log_distinct_prime_divisors_le (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hh)) ht
  intro p hp
  exact Int.natCast_dvd.mp (hd p hp)

end Erdos380
