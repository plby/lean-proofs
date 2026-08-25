import ErdosProblems.Erdos964.SelbergPrimeRemoval

/-!
# Radius faces in the scalar semiprime kernel

The transformed coefficient vanishes beyond the radius. This gives the
two faces for a smaller prime below the radius and the constant tail for
a prime at or above the radius, as in equations (6.13)--(6.17) of GGPY.
-/

namespace Erdos964

open scoped BigOperators

theorem scalarSemiprimeTransform_prime_difference_split (P R p : ℕ)
    (hp : 0 < p) (y : ℕ → ℝ) (hy : ∀ u, R ≤ u → y u = 0) :
    (∑ r ∈ P.divisors, if p ∣ r then 0 else semiprimeSelbergWeight 3 r *
      (scalarSemiprimeTransform P y r - scalarSemiprimeTransform P y (p * r)) ^ 2) =
      (∑ r ∈ P.divisors.filter (fun r => p * r < R ∧ ¬ p ∣ r),
        semiprimeSelbergWeight 3 r *
          (scalarSemiprimeTransform P y r - scalarSemiprimeTransform P y (p * r)) ^ 2) +
      ∑ r ∈ P.divisors.filter (fun r => r < R ∧ R ≤ p * r ∧ ¬ p ∣ r),
        semiprimeSelbergWeight 3 r * (scalarSemiprimeTransform P y r) ^ 2 := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpdiv : p ∣ r
  · simp [hpdiv]
  · rw [if_neg hpdiv]
    by_cases hpr : p * r < R
    · have hrR : r < R := lt_of_le_of_lt (by nlinarith : r ≤ p * r) hpr
      simp [hpdiv, hpr, hrR, Nat.not_le.mpr hpr]
    · have hRpr : R ≤ p * r := Nat.le_of_not_gt hpr
      rw [scalarSemiprimeTransform_eq_zero_of_radius P R y hy (p * r) hRpr, sub_zero]
      by_cases hrR : r < R
      · simp [hpdiv, hpr, hrR, hRpr]
      · rw [scalarSemiprimeTransform_eq_zero_of_radius P R y hy r (Nat.le_of_not_gt hrR)]
        simp [hpdiv, hpr, hrR]

theorem scalarSelberg_semiprime_kernel_faces (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (R : ℕ) (y : ℕ → ℝ) (hy : ∀ u, R ≤ u → y u = 0) (p : ℕ) (hp : p.Prime) :
    scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y) =
      (∑ r ∈ s.prodPrimes.divisors.filter (fun r => p * r < R ∧ ¬ p ∣ r),
        semiprimeSelbergWeight 3 r *
          (scalarSemiprimeTransform s.prodPrimes y r -
            scalarSemiprimeTransform s.prodPrimes y (p * r)) ^ 2) +
      ∑ r ∈ s.prodPrimes.divisors.filter (fun r => r < R ∧ R ≤ p * r ∧ ¬ p ∣ r),
        semiprimeSelbergWeight 3 r * (scalarSemiprimeTransform s.prodPrimes y r) ^ 2 := by
  rw [scalarSelberg_semiprime_kernel_diagonal_all_primes s t hP hs ht y p hp]
  exact scalarSemiprimeTransform_prime_difference_split s.prodPrimes R p hp.pos y hy

theorem scalarSelberg_semiprime_kernel_large_prime (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (R : ℕ) (y : ℕ → ℝ) (hy : ∀ u, R ≤ u → y u = 0)
    (p : ℕ) (hp : p.Prime) (hpR : R ≤ p) :
    scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y) =
      t.mainSum (BoundingSieve.lambdaSquared (scalarSelbergCoefficient s y)) := by
  rw [scalarSelberg_semiprime_kernel_diagonal_all_primes s t hP hs ht y p hp,
    scalarSelberg_semiprime_diagonal s t hP hs ht y]
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos := Nat.pos_of_mem_divisors hr
  have hRpr : R ≤ p * r := by nlinarith
  rw [scalarSemiprimeTransform_eq_zero_of_radius s.prodPrimes R y hy (p * r) hRpr,
    sub_zero]
  by_cases hpdiv : p ∣ r
  · rw [if_pos hpdiv, scalarSemiprimeTransform_eq_zero_of_radius s.prodPrimes R y hy r
      (hpR.trans (Nat.le_of_dvd hrpos hpdiv))]
    ring
  · exact if_neg hpdiv

end Erdos964
