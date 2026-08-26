import Mathlib

/-!
# The common square-divisor factor

Halving the prime exponents of a positive integer gives the root of its
largest square divisor. Applied to the gcd of the two binary-form
coefficients, this is the factor occurring in the local product estimate.
-/

namespace Erdos1148.DukeArithmetic

noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun k => k / 2) (by decide)

lemma halfFactorization_le (n : ℕ) : halfFactorization n ≤ n.factorization := by
  intro p
  simp only [halfFactorization, Finsupp.mapRange_apply]
  omega

noncomputable def squareContentRoot (n : ℕ) : ℕ := (halfFactorization n).prod (· ^ ·)

lemma squareContentRoot_factorization (n : ℕ) :
    (squareContentRoot n).factorization = halfFactorization n :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (halfFactorization_le n)

lemma squareContentRoot_dvd (n : ℕ) : squareContentRoot n ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (halfFactorization_le n)

lemma squareContentRoot_ne_zero (n : ℕ) (hn : n ≠ 0) : squareContentRoot n ≠ 0 := by
  intro hzero
  have h := squareContentRoot_dvd n
  rw [hzero, zero_dvd_iff] at h
  exact hn h

lemma squareContentRoot_sq_dvd (n : ℕ) (hn : n ≠ 0) : squareContentRoot n ^ 2 ∣ n := by
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero 2 (squareContentRoot_ne_zero n hn)) hn).mp
  intro p
  simp only [Nat.factorization_pow, squareContentRoot_factorization, Finsupp.smul_apply,
    halfFactorization, Finsupp.mapRange_apply, smul_eq_mul]
  omega

noncomputable def pairSquareContent (d ℓ : ℤ) : ℕ := squareContentRoot (d.natAbs.gcd ℓ.natAbs)

lemma pairSquareContent_factorization (d ℓ : ℤ) (p : ℕ) :
    (pairSquareContent d ℓ).factorization p = (d.natAbs.gcd ℓ.natAbs).factorization p / 2 := by
  simp only [pairSquareContent, squareContentRoot_factorization, halfFactorization,
    Finsupp.mapRange_apply]

lemma pairSquareContent_sq_dvd (d ℓ : ℤ) (hd : d ≠ 0) :
    (pairSquareContent d ℓ : ℤ) ^ 2 ∣ d ∧ (pairSquareContent d ℓ : ℤ) ^ 2 ∣ ℓ := by
  have hG : d.natAbs.gcd ℓ.natAbs ≠ 0 := by
    intro hG
    exact (Int.natAbs_ne_zero.mpr hd) (Nat.gcd_eq_zero_iff.mp hG).1
  have hf := squareContentRoot_sq_dvd (d.natAbs.gcd ℓ.natAbs) hG
  have hddiv : pairSquareContent d ℓ ^ 2 ∣ d.natAbs := hf.trans (Nat.gcd_dvd_left _ _)
  have hℓdiv : pairSquareContent d ℓ ^ 2 ∣ ℓ.natAbs := hf.trans (Nat.gcd_dvd_right _ _)
  constructor
  · simpa only [Nat.cast_pow] using Int.natCast_dvd.mpr hddiv
  · simpa only [Nat.cast_pow] using Int.natCast_dvd.mpr hℓdiv

lemma pairSquareContent_dvd_binary_discriminant (d ℓ : ℤ) :
    pairSquareContent d ℓ ∣ (ℓ ^ 2 - 4 * d ^ 2).natAbs := by
  have hf := squareContentRoot_dvd (d.natAbs.gcd ℓ.natAbs)
  have hddiv : (pairSquareContent d ℓ : ℤ) ∣ d :=
    Int.natCast_dvd.mpr (hf.trans (Nat.gcd_dvd_left _ _))
  have hℓdiv : (pairSquareContent d ℓ : ℤ) ∣ ℓ :=
    Int.natCast_dvd.mpr (hf.trans (Nat.gcd_dvd_right _ _))
  apply Int.natCast_dvd.mp
  exact dvd_sub (dvd_pow hℓdiv (by decide)) (dvd_mul_of_dvd_right (dvd_pow hddiv (by decide)) 4)

end Erdos1148.DukeArithmetic
