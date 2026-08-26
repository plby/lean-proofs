import ErdosProblems.Erdos421.SelbergWeights

/-! # Finite support of the constructed Selberg weights -/

namespace Erdos421

theorem selbergOptimizedWeight_eq_zero_of_not_dvd (s : BoundingSieve) (D : ℕ)
    {d : ℕ} (hd : ¬d ∣ s.prodPrimes) : selbergOptimizedWeight s D d = 0 := by
  simp only [selbergOptimizedWeight, if_neg hd]

theorem selbergOptimizedWeight_eq_zero_of_gt (s : BoundingSieve) {D d : ℕ}
    (hd : D < d) : selbergOptimizedWeight s D d = 0 := by
  by_cases hdP : d ∣ s.prodPrimes
  · rw [selbergOptimizedWeight, if_pos hdP, upperMobiusTransform, lowerMobiusTransform]
    have hzero : (∑ v ∈ (s.prodPrimes / d).divisorsAntidiagonal,
        (ArithmeticFunction.moebius v.1 : ℝ) * selbergTarget s D (s.prodPrimes / v.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hv2 : v.2 ∣ s.prodPrimes / d :=
        Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)
      have hvpos : 0 < v.2 :=
        Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)
      have hmul : d * v.2 ∣ s.prodPrimes := (Nat.dvd_div_iff_mul_dvd hdP).mp hv2
      have hle : d * v.2 ≤ s.prodPrimes :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (BoundingSieve.prodPrimes_ne_zero (s := s))) hmul
      have hquot : d ≤ s.prodPrimes / v.2 :=
        (Nat.le_div_iff_mul_le hvpos).mpr (by simpa only [mul_comm] using hle)
      rw [selbergTarget, if_neg (by omega), mul_zero]
    rw [hzero, mul_zero]
  · exact selbergOptimizedWeight_eq_zero_of_not_dvd s D hdP

theorem selbergLambdaSquared_eq_zero_of_gt (s : BoundingSieve) {D k : ℕ}
    (hk : D ^ 2 < k) : BoundingSieve.lambdaSquared (selbergOptimizedWeight s D) k = 0 := by
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with hke
  · by_cases hdD : D < d
    · rw [selbergOptimizedWeight_eq_zero_of_gt s hdD, zero_mul]
    · have heD : D < e := by
        by_contra heD
        have hprod : d * e ≤ D ^ 2 := by
          simpa only [pow_two] using Nat.mul_le_mul (by omega : d ≤ D) (by omega : e ≤ D)
        have hlcm := Nat.lcm_le_mul (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
        omega
      rw [selbergOptimizedWeight_eq_zero_of_gt s heD, mul_zero]
  · rfl

theorem selbergLambdaSquared_eq_zero_of_not_dvd (s : BoundingSieve) (D : ℕ) {k : ℕ}
    (hk : ¬k ∣ s.prodPrimes) : BoundingSieve.lambdaSquared (selbergOptimizedWeight s D) k = 0 := by
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with hke
  · by_cases hdP : d ∣ s.prodPrimes
    · have heP : ¬e ∣ s.prodPrimes := by
        intro heP
        apply hk
        rw [hke]
        exact Nat.lcm_dvd hdP heP
      rw [selbergOptimizedWeight_eq_zero_of_not_dvd s D heP, mul_zero]
    · rw [selbergOptimizedWeight_eq_zero_of_not_dvd s D hdP, zero_mul]
  · rfl

end Erdos421
