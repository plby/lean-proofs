import ErdosProblems.Erdos851.SingularProductExpansion

/-!
# A consecutive-integer average for the two-prime singular factor

This is the small Euler-product estimate needed when the four-prime
representation count is grouped by the two prime differences.  It is kept
separate from the Erdős 851 power-of-two average: here the parameters range
over consecutive integers, so elementary counting of multiples gives a
uniform second moment.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

/-- The increment obtained by squaring one active singular local factor. -/
def singularSquareIncrement (p : ℕ) : ℝ :=
  ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1

lemma singularSquareIncrement_nonneg {p : ℕ} (hp : 1 < p) :
    0 ≤ singularSquareIncrement p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hratio : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold singularSquareIncrement
  nlinarith [sq_nonneg ((p : ℝ) / ((p : ℝ) - 1) - 1)]

lemma singularSquareIncrement_div_le_secondOrder_sq_sub_one
    {p : ℕ} (hp : 2 < p) :
    singularSquareIncrement p / (p : ℝ) ≤
      Erdos851.secondOrderCorrection p ^ 2 - 1 := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  unfold singularSquareIncrement Erdos851.secondOrderCorrection
  field_simp [hp0.ne', hp1.ne', hp2.ne']
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
    (sq_nonneg ((p : ℝ) - 1)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
      (mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)
        (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1))]

private lemma prod_dvd_iff_all_dvd
    {T : Finset ℕ} (hprime : ∀ p ∈ T, p.Prime) {n : ℕ} :
    (∏ p ∈ T, p) ∣ n ↔ ∀ p ∈ T, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    exact Finset.prod_primes_dvd n (fun p hp ↦ (hprime p hp).prime) h

private lemma prod_ite_dvd_increment
    {T : Finset ℕ} (hprime : ∀ p ∈ T, p.Prime) (n : ℕ) :
    (∏ p ∈ T, if p ∣ n then singularSquareIncrement p else 0) =
      if (∏ p ∈ T, p) ∣ n then
        ∏ p ∈ T, singularSquareIncrement p else 0 := by
  by_cases h : ∀ p ∈ T, p ∣ n
  · have hprod : (∏ p ∈ T, p) ∣ n :=
      (prod_dvd_iff_all_dvd hprime).2 h
    rw [if_pos hprod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [if_pos (h p hp)]
  · have hprod : ¬ (∏ p ∈ T, p) ∣ n := by
      exact fun hp ↦ h ((prod_dvd_iff_all_dvd hprime).1 hp)
    rw [if_neg hprod]
    push Not at h
    obtain ⟨p, hpT, hpn⟩ := h
    exact Finset.prod_eq_zero hpT (by simp [hpn])

/-- Exact subset expansion of the square of a truncated singular factor. -/
theorem singularFactor_sq_eq_subset_sum (n z y : ℕ) :
    Erdos851.singularFactor n z y ^ 2 =
      ∑ T ∈ (Erdos851.sievePrimes z y).powerset,
        if (∏ p ∈ T, p) ∣ n then
          ∏ p ∈ T, singularSquareIncrement p else 0 := by
  classical
  let P := Erdos851.sievePrimes z y
  have hprime : ∀ p ∈ P, p.Prime := fun p hp ↦
    (Erdos851.mem_sievePrimes.mp hp).2.2
  calc
    Erdos851.singularFactor n z y ^ 2 =
        ∏ p ∈ P,
          (if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1) ^ 2 := by
      exact (Finset.prod_pow P 2 _).symm
    _ = ∏ p ∈ P,
          (1 + if p ∣ n then singularSquareIncrement p else 0) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpn : p ∣ n <;> simp [hpn, singularSquareIncrement]
    _ = ∑ T ∈ P.powerset,
          ∏ p ∈ T, (if p ∣ n then singularSquareIncrement p else 0) := by
      exact Finset.prod_one_add P
    _ = ∑ T ∈ P.powerset,
        if (∏ p ∈ T, p) ∣ n then
          ∏ p ∈ T, singularSquareIncrement p else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      exact prod_ite_dvd_increment
        (fun p hp ↦ hprime p (Finset.mem_powerset.mp hT hp)) n

/-- Consecutive positive integers have uniformly bounded mean square
singular factor.  The constant `4` comes from the square of the standard
second-order Euler correction, whose product is at most `2`. -/
theorem sum_Ioc_singularFactor_sq_le (z y N : ℕ) (hz : 2 ≤ z) :
    (∑ n ∈ Finset.Ioc 0 N, Erdos851.singularFactor n z y ^ 2) ≤
      4 * (N : ℝ) := by
  classical
  let P := Erdos851.sievePrimes z y
  have hprime : ∀ p ∈ P, p.Prime := fun p hp ↦
    (Erdos851.mem_sievePrimes.mp hp).2.2
  have hinc : ∀ p ∈ P, 0 ≤ singularSquareIncrement p := by
    intro p hp
    exact singularSquareIncrement_nonneg (hprime p hp).one_lt
  calc
    (∑ n ∈ Finset.Ioc 0 N, Erdos851.singularFactor n z y ^ 2) =
        ∑ T ∈ P.powerset,
          (∏ p ∈ T, singularSquareIncrement p) *
            (((Finset.Ioc 0 N).filter
              (fun n ↦ (∏ p ∈ T, p) ∣ n)).card : ℝ) := by
      simp_rw [singularFactor_sq_eq_subset_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ T ∈ P.powerset,
          (∏ p ∈ T, singularSquareIncrement p) *
            ((N / (∏ p ∈ T, p) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ T ∈ P.powerset,
          (N : ℝ) *
            (∏ p ∈ T, singularSquareIncrement p / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro T hT
      have hprodNonneg : 0 ≤ ∏ p ∈ T, singularSquareIncrement p :=
        Finset.prod_nonneg fun p hp ↦ hinc p (Finset.mem_powerset.mp hT hp)
      calc
        (∏ p ∈ T, singularSquareIncrement p) *
              ((N / (∏ p ∈ T, p) : ℕ) : ℝ) ≤
            (∏ p ∈ T, singularSquareIncrement p) *
              ((N : ℝ) / ((∏ p ∈ T, p) : ℝ)) := by
          have hdiv :
              ((N / (∏ p ∈ T, p) : ℕ) : ℝ) ≤
                (N : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) := Nat.cast_div_le
          exact mul_le_mul_of_nonneg_left
            (by simpa only [Nat.cast_prod] using hdiv) hprodNonneg
        _ = (N : ℝ) *
              (∏ p ∈ T, singularSquareIncrement p / (p : ℝ)) := by
          rw [Finset.prod_div_distrib]
          ring
    _ = (N : ℝ) *
          ∏ p ∈ P, (1 + singularSquareIncrement p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ (N : ℝ) *
          ∏ p ∈ P, Erdos851.secondOrderCorrection p ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.prod_le_prod
      · intro p hp
        exact add_nonneg zero_le_one
          (div_nonneg (hinc p hp) (Nat.cast_nonneg p))
      · intro p hp
        have hp2 : 2 < p := by
          have hp' := Erdos851.mem_sievePrimes.mp hp
          omega
        linarith [singularSquareIncrement_div_le_secondOrder_sq_sub_one hp2]
    _ = (N : ℝ) *
          (∏ p ∈ P, Erdos851.secondOrderCorrection p) ^ 2 := by
      rw [Finset.prod_pow]
    _ ≤ (N : ℝ) * 2 ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      have hprod0 : 0 ≤ ∏ p ∈ P, Erdos851.secondOrderCorrection p :=
        Finset.prod_nonneg fun p hp ↦
          (Erdos851.one_le_secondOrderCorrection (by
            have hp' := Erdos851.mem_sievePrimes.mp hp
            omega)).trans' zero_le_one
      exact (sq_le_sq₀ hprod0 (by norm_num)).2
        (Erdos851.secondOrderCorrection_product_le_two hz)
    _ = 4 * (N : ℝ) := by ring

end

end Erdos67b
