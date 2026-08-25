import ErdosProblems.Erdos1197.BMProducts

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

lemma bm_prime_coeff_zero_of_product_eq
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (rBM : BMIdx k ν → ℤ) (z : ℤ)
    (hAB : bmA p rBM z = bmB p rBM z) :
    ∀ i : PrimeIdx k, rBM (Sum.inl i) = 0 := by
  intro i
  rcases lt_trichotomy (rBM (Sum.inl i)) 0 with hneg | hzero | hpos
  · exfalso
    have hdivFactor : p i ∣ p i ^ zneg (rBM (Sum.inl i)) := by
      exact dvd_pow_self _ (zneg_pos_of_neg hneg).ne'
    have hdivPrimeNeg : p i ∣ bmPrimeNegProd p rBM := by
      unfold bmPrimeNegProd
      exact dvd_trans hdivFactor
        (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zneg (rBM (Sum.inl i')))
          (Finset.mem_univ i))
    have hdivB : p i ∣ bmB p rBM z := by
      have hfirst : p i ∣ (2 ^ zpos z) * bmPrimeNegProd p rBM := by
        exact dvd_mul_of_dvd_right hdivPrimeNeg (2 ^ zpos z)
      simpa [bmB, mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_right hfirst (bmIntNegProd rBM)
    have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
      (Ne.symm (bm_prime_ne_two hν p hp_window i))
    have hnotTwo : ¬ p i ∣ 2 := by
      have hcop : Nat.Coprime (p i) 2 :=
        Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
      exact (hpPrime i).coprime_iff_not_dvd.mp hcop
    have hnotPrimePos : ¬ p i ∣ bmPrimePosProd p rBM := by
      unfold bmPrimePosProd
      apply Prime.not_dvd_finsetProd (p := p i) (hpPrime i).prime
      intro i' hi'
      by_cases hii' : i = i'
      · subst hii'
        simp [zpos_eq_zero_of_nonpos hneg.le, (hpPrime i).ne_one]
      · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
    have hnotIntPos : ¬ p i ∣ bmIntPosProd rBM := by
      unfold bmIntPosProd
      apply Prime.not_dvd_finsetProd (p := p i) (hpPrime i).prime
      intro j hj
      exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
        (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
    have hnotA : ¬ p i ∣ bmA p rBM z := by
      unfold bmA
      have hnotFirst : ¬ p i ∣ (2 ^ zneg z) * bmPrimePosProd p rBM :=
        Nat.Prime.not_dvd_mul (hpPrime i)
          (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimePos
      exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntPos
    exact hnotA (hAB ▸ hdivB)
  · exact hzero
  · exfalso
    have hdivFactor : p i ∣ p i ^ zpos (rBM (Sum.inl i)) := by
      exact dvd_pow_self _ (zpos_pos_of_pos hpos).ne'
    have hdivPrimePos : p i ∣ bmPrimePosProd p rBM := by
      unfold bmPrimePosProd
      exact dvd_trans hdivFactor
        (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zpos (rBM (Sum.inl i')))
          (Finset.mem_univ i))
    have hdivA : p i ∣ bmA p rBM z := by
      have hfirst : p i ∣ (2 ^ zneg z) * bmPrimePosProd p rBM := by
        exact dvd_mul_of_dvd_right hdivPrimePos (2 ^ zneg z)
      simpa [bmA, mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_right hfirst (bmIntPosProd rBM)
    have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
      (Ne.symm (bm_prime_ne_two hν p hp_window i))
    have hnotTwo : ¬ p i ∣ 2 := by
      have hcop : Nat.Coprime (p i) 2 :=
        Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
      exact (hpPrime i).coprime_iff_not_dvd.mp hcop
    have hnotPrimeNeg : ¬ p i ∣ bmPrimeNegProd p rBM := by
      unfold bmPrimeNegProd
      apply Prime.not_dvd_finsetProd (p := p i) (hpPrime i).prime
      intro i' hi'
      by_cases hii' : i = i'
      · subst hii'
        simp [zneg_eq_zero_of_nonneg hpos.le, (hpPrime i).ne_one]
      · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
    have hnotIntNeg : ¬ p i ∣ bmIntNegProd rBM := by
      unfold bmIntNegProd
      apply Prime.not_dvd_finsetProd (p := p i) (hpPrime i).prime
      intro j hj
      exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
        (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
    have hnotB : ¬ p i ∣ bmB p rBM z := by
      unfold bmB
      have hnotFirst : ¬ p i ∣ (2 ^ zpos z) * bmPrimeNegProd p rBM :=
        Nat.Prime.not_dvd_mul (hpPrime i)
          (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimeNeg
      exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntNeg
    exact hnotB (hAB ▸ hdivA)

end

end Erdos1197
