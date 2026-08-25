import ErdosProblems.Erdos964.AffineScalarCounting
import ErdosProblems.Erdos964.SelbergDimension

/-!
# The exact first arithmetic sum for the scalar GGPY weights

Expanding the square, counting each lcm divisor, and applying the scalar
Selberg diagonalization gives the actual affine first moment. The finite
error is retained explicitly; its asymptotic bound is a later step.
-/

namespace Erdos964

open scoped BigOperators

noncomputable def scalarAffineWeight (A B : Fin 3 → ℕ) (P : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ P.divisors.filter (fun d => d ∣ ∏ i, (A i * n + B i)), w d) ^ 2

theorem scalarAffineWeight_nonneg (A B : Fin 3 → ℕ) (P : ℕ) (w : ℕ → ℝ) (n : ℕ) :
    0 ≤ scalarAffineWeight A B P w n := sq_nonneg _

theorem scalarAffineWeight_eq_pair_indicator (A B : Fin 3 → ℕ) (P : ℕ) (w : ℕ → ℝ) (n : ℕ) :
    scalarAffineWeight A B P w n = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
      if Nat.lcm d e ∣ ∏ i, (A i * n + B i) then w d * w e else 0 := by
  unfold scalarAffineWeight
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ∣ ∏ i, (A i * n + B i)
  · simp only [if_pos hd]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∣ ∏ i, (A i * n + B i)
    · simp only [Nat.lcm_dvd_iff, hd, he, and_self, ite_true]
      ring
    · simp only [Nat.lcm_dvd_iff, hd, he, and_false, ite_false, zero_mul]
  · simp [Nat.lcm_dvd_iff, hd]

theorem scalarAffineS1_eq_pair_count (A B : Fin 3 → ℕ) (P N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico N (2 * N), scalarAffineWeight A B P w n) =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (affineProductMultipleCount A B N (Nat.lcm d e) : ℝ) * (w d * w e) := by
  simp_rw [scalarAffineWeight_eq_pair_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [affineProductMultipleCount, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]

theorem selberg_mainSum_eq_lcm_sum (s : BoundingSieve) (w : ℕ → ℝ) :
    s.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        s.nu (Nat.lcm d e) * (w d * w e) := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hnonzero : s.nu (Nat.gcd d e) ≠ 0 :=
    BoundingSieve.nu_ne_zero ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd))
  rw [s.nu_mult.map_lcm hnonzero]
  ring

theorem normalized_scalarAffineS1_error (A B : Fin 3 → ℕ) (v N : ℕ)
    (s : BoundingSieve) (hsM : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (w : ℕ → ℝ) :
    |(∑ n ∈ Finset.Ico N (2 * N),
        scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) s.prodPrimes w n) -
        (N : ℝ) * s.mainSum (BoundingSieve.lambdaSquared w)| ≤
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card * |w d * w e| := by
  have hpair (d : ℕ) (hd : d ∈ s.prodPrimes.divisors)
      (e : ℕ) (he : e ∈ s.prodPrimes.divisors) :
      |(affineProductMultipleCount (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) N (Nat.lcm d e) : ℝ) -
          (N : ℝ) * s.nu (Nat.lcm d e)| ≤ (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card := by
    have hdiv : Nat.lcm d e ∣ s.prodPrimes :=
      Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
    have hcount := normalized_affineProductMultipleCount_error A B v N (Nat.lcm d e)
      (s.prodPrimes_squarefree.squarefree_of_dvd hdiv) (hsM.coprime_dvd_left hdiv)
    rw [selberg_nu_eq_dimension_density s 3 hdensity _ hdiv]
    norm_num only [Nat.cast_ofNat]
    have hid : (N : ℝ) * ((3 : ℝ) ^ (Nat.lcm d e).primeFactors.card / (Nat.lcm d e : ℝ)) =
        (N : ℝ) / (Nat.lcm d e : ℝ) * (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card := by ring
    rw [hid]
    exact hcount
  rw [scalarAffineS1_eq_pair_count, selberg_mainSum_eq_lcm_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← mul_assoc (N : ℝ), ← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hpair d hd e he) (abs_nonneg _)

theorem normalized_scalarAffineS1_diagonal_error (A B : Fin 3 → ℕ) (v N : ℕ)
    (s : BoundingSieve) (hsM : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (y : ℕ → ℝ) :
    |(∑ n ∈ Finset.Ico N (2 * N),
        scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) s.prodPrimes (scalarSelbergCoefficient s y) n) -
        (N : ℝ) * ∑ r ∈ s.prodPrimes.divisors, dimensionSelbergWeight 3 r * (y r) ^ 2| ≤
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| := by
  have h := normalized_scalarAffineS1_error A B v N s hsM hdensity (scalarSelbergCoefficient s y)
  rw [scalarSelbergCoefficient_dimension_diagonal s 3 hdensity y] at h
  exact h

end Erdos964
