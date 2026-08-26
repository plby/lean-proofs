import ErdosProblems.Erdos421.SelbergRankin

/-! # Euler products controlling the truncated Selberg normalizer -/

namespace Erdos421

noncomputable def sieveEulerProduct (s : BoundingSieve) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)

theorem sieveEulerProduct_pos (s : BoundingSieve) : 0 < sieveEulerProduct s := by
  apply Finset.prod_pos
  intro p hp
  exact sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp))

theorem selbergTerms_prime (s : BoundingSieve) {p : ℕ} (hp : p.Prime) :
    s.selbergTerms p = s.nu p / (1 - s.nu p) := by
  rw [BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton]
  rfl

theorem selberg_full_euler_product (s : BoundingSieve) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p)) = (sieveEulerProduct s)⁻¹ := by
  rw [sieveEulerProduct, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hne : 1 - s.nu p ≠ 0 :=
    (sub_pos.mpr (s.nu_lt_one_of_prime p hpprime (Nat.dvd_of_mem_primeFactors hp))).ne'
  rw [selbergTerms_prime s hpprime]
  field_simp
  ring

theorem selberg_twisted_euler_product (s : BoundingSieve) (α : ℝ) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 + s.selbergTerms p * (p : ℝ) ^ α)) =
      (sieveEulerProduct s)⁻¹ *
        ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * ((p : ℝ) ^ α - 1)) := by
  rw [← selberg_full_euler_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hne : 1 - s.nu p ≠ 0 :=
    (sub_pos.mpr (s.nu_lt_one_of_prime p hpprime (Nat.dvd_of_mem_primeFactors hp))).ne'
  rw [selbergTerms_prime s hpprime]
  field_simp
  ring

theorem selberg_euler_ratio_le_exp (s : BoundingSieve) {α : ℝ} (hα : 0 ≤ α) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * ((p : ℝ) ^ α - 1))) ≤
      Real.exp (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * ((p : ℝ) ^ α - 1)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hν := (s.nu_pos_of_prime p hpprime (Nat.dvd_of_mem_primeFactors hp)).le
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_lt.le
    have hr := Real.one_le_rpow hp1 hα
    positivity
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (s.nu p * ((p : ℝ) ^ α - 1))

theorem selbergNormalizer_exp_rankin (s : BoundingSieve) {D : ℕ} (hD : 0 < D)
    {α : ℝ} (hα : 0 ≤ α) :
    (sieveEulerProduct s)⁻¹ * (1 - ((D : ℝ) ^ α)⁻¹ *
      Real.exp (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * ((p : ℝ) ^ α - 1))) ≤
        selbergNormalizer s D := by
  have hG := selbergNormalizer_rankin s hD hα
  rw [selberg_full_euler_product, selberg_twisted_euler_product] at hG
  have hV := (sieveEulerProduct_pos s).le
  have hb := mul_le_mul_of_nonneg_left (selberg_euler_ratio_le_exp s hα)
    (by positivity : 0 ≤ ((D : ℝ) ^ α)⁻¹ * (sieveEulerProduct s)⁻¹)
  nlinarith

end Erdos421
