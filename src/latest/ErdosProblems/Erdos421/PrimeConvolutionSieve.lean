import ErdosProblems.Erdos421.PrimeDivisorConvolution

/-! # Convolving finite divisor bounds with a prime factor -/

namespace Erdos421

theorem primeDivisorConvolution_divisor_sum (P : Finset ℕ) (a : ℕ → ℝ) {Q D : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (ha : ∀ d, D < d → a d = 0) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (Q * D), if m ∣ n then primeDivisorConvolution P a m else 0) =
      ∑ p ∈ P, if p ∣ n then
        (∑ d ∈ Finset.Icc 1 D, if d ∣ n / p then a d else 0) else 0 := by
  have h := primeDivisorConvolution_truncated_action P a
    (fun m ↦ if m ∣ n then 1 else 0) hP ha
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Nat.dvd_div_iff_mul_dvd hpn]
  · rw [if_neg hpn]
    apply Finset.sum_eq_zero
    intro d hd
    have hnot : ¬ p * d ∣ n := fun hpd ↦ hpn ((dvd_mul_right p d).trans hpd)
    rw [if_neg hnot]

theorem primeDivisorConvolution_upper (P : Finset ℕ) (a : ℕ → ℝ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (ha : ∀ d, D < d → a d = 0)
    (hupper : ∀ n, roughIndicator n z ≤ ∑ d ∈ Finset.Icc 1 D, if d ∣ n then a d else 0)
    (n : ℕ) : primeCofactorWeight P z n ≤
      ∑ m ∈ Finset.Icc 1 (Q * D), if m ∣ n then primeDivisorConvolution P a m else 0 := by
  rw [primeDivisorConvolution_divisor_sum P a hP ha]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact hupper (n / p)
  · exact le_rfl

theorem primeDivisorConvolution_lower (P : Finset ℕ) (a : ℕ → ℝ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (ha : ∀ d, D < d → a d = 0)
    (hlower : ∀ n, (∑ d ∈ Finset.Icc 1 D, if d ∣ n then a d else 0) ≤ roughIndicator n z)
    (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (Q * D), if m ∣ n then primeDivisorConvolution P a m else 0) ≤
      primeCofactorWeight P z n := by
  rw [primeDivisorConvolution_divisor_sum P a hP ha]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact hlower (n / p)
  · exact le_rfl

end Erdos421
