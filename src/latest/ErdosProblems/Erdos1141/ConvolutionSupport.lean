import Mathlib

/-!
# The convolution when small split primes are absent
-/

open scoped BigOperators

namespace Erdos1141

lemma zetaMul_prime_pow_eq_zero {q p k : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hχp : χ (p : ZMod q) = -1) (hk : Even (k + 1)) :
    χ.zetaMul (p ^ k) = 0 := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero,
    ne_eq, false_and, if_false, Nat.cast_pow, map_pow, hχp, neg_one_geom_sum, hk, if_true]

lemma squarefree_part_dvd_of_zetaMul_ne_zero {q M X n a b : ℕ}
    (χ : DirichletCharacter ℂ q) (hM : M ≠ 0) (hn : n ≠ 0) (hnX : n ≤ X)
    (hsq : b ^ 2 * a = n) (ha : Squarefree a) (hcoeff : χ.zetaMul n ≠ 0)
    (hprimes : ∀ p : ℕ, p.Prime → p ≤ X → ¬p ∣ M → χ (p : ZMod q) = -1) :
    a ∣ M := by
  have hb : b ≠ 0 := by intro hb; simp [hb] at hsq; omega
  apply (Nat.factorization_le_iff_dvd ha.ne_zero hM).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hpn : p ∣ n := by rw [← hsq]; exact dvd_mul_of_dvd_right hpa _
      have hpX : p ≤ X := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn).trans hnX
      have hpm : p ∣ M := by
        by_contra hpm
        have hχp := hprimes p hp hpX hpm
        have hfac : n.factorization p = 2 * b.factorization p + 1 := by
          rw [← hsq, Nat.factorization_mul (pow_ne_zero 2 hb) ha.ne_zero,
            Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
            smul_eq_mul, Nat.factorization_eq_one_of_squarefree ha hp hpa]
        have heven : Even (n.factorization p + 1) := ⟨b.factorization p + 1, by omega⟩
        apply hcoeff
        rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn]
        apply Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
        exact zetaMul_prime_pow_eq_zero χ hp hχp heven
      exact (ha.natFactorization_le_one p).trans ((hp.dvd_iff_one_le_factorization hM).mp hpm)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

lemma norm_zetaMul_le_divisors_card {q n : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖χ.zetaMul n‖ ≤ n.divisors.card := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖toArithmeticFunction (χ ·) d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      simpa only [toArithmeticFunction, ArithmeticFunction.coe_mk, hd0, if_false] using
        χ.norm_le_one (d : ZMod q)
    _ = _ := by simp

theorem exists_square_times_divisor_of_zetaMul_ne_zero {q M X n : ℕ}
    (χ : DirichletCharacter ℂ q) (hM : M ≠ 0) (hn : n ≠ 0) (hnX : n ≤ X)
    (hcoeff : χ.zetaMul n ≠ 0)
    (hprimes : ∀ p : ℕ, p.Prime → p ≤ X → ¬p ∣ M → χ (p : ZMod q) = -1) :
    ∃ a ∈ M.divisors, ∃ b ∈ Finset.Icc 1 (Nat.sqrt X), b ^ 2 * a = n := by
  obtain ⟨a, b, hsq, ha⟩ := Nat.sq_mul_squarefree n
  have haM := squarefree_part_dvd_of_zetaMul_ne_zero χ hM hn hnX hsq ha hcoeff hprimes
  have hb : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro hb
    apply hn
    rw [← hsq, hb]
    simp
  have hbX : b ≤ Nat.sqrt X := by
    apply Nat.le_sqrt.mpr
    have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha.ne_zero
    nlinarith
  exact ⟨a, Nat.mem_divisors.mpr ⟨haM, hM⟩, b, Finset.mem_Icc.mpr ⟨hb, hbX⟩, hsq⟩

theorem norm_zetaMul_prefix_le_of_no_split_prime {q M X : ℕ}
    (χ : DirichletCharacter ℂ q) (hM : M ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hdivisors : ∀ n : ℕ, 0 < n → n ≤ X → (n.divisors.card : ℝ) ≤ C)
    (hprimes : ∀ p : ℕ, p.Prime → p ≤ X → ¬p ∣ M → χ (p : ZMod q) = -1) :
    ‖∑ n ∈ Finset.Icc 1 X, χ.zetaMul n‖ ≤ (M.divisors.card : ℝ) * Nat.sqrt X * C := by
  classical
  let S := (Finset.Icc 1 X).filter fun n ↦ χ.zetaMul n ≠ 0
  let T := M.divisors.product (Finset.Icc 1 (Nat.sqrt X))
  have hsubset : S ⊆ T.image (fun z : ℕ × ℕ ↦ z.2 ^ 2 * z.1) := by
    intro n hn
    obtain ⟨hnI, hncoeff⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := (show 0 < n from (Finset.mem_Icc.mp hnI).1).ne'
    obtain ⟨a, ha, b, hb, hab⟩ := exists_square_times_divisor_of_zetaMul_ne_zero
      χ hM hn0 (Finset.mem_Icc.mp hnI).2 hncoeff hprimes
    exact Finset.mem_image.mpr ⟨(a, b), by
      simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using And.intro ha hb, hab⟩
  have hcard : S.card ≤ M.divisors.card * Nat.sqrt X := by
    have h := (Finset.card_le_card hsubset).trans (Finset.card_image_le)
    simpa [T] using h
  have hsum : (∑ n ∈ S, χ.zetaMul n) = ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnS
    have hnot : ¬ χ.zetaMul n ≠ 0 := by
      intro h
      exact hnS (Finset.mem_filter.mpr ⟨hn, h⟩)
    exact not_not.mp hnot
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ S, ‖χ.zetaMul n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, C := by
      apply Finset.sum_le_sum
      intro n hn
      have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      exact (norm_zetaMul_le_divisors_card χ).trans (hdivisors n hnI.1 hnI.2)
    _ = (S.card : ℝ) * C := by simp
    _ ≤ (M.divisors.card : ℝ) * Nat.sqrt X * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast hcard

end Erdos1141
