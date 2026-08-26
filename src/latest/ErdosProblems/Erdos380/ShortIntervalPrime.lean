import ErdosProblems.Erdos380.Intervals
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A restricted substitute for Sylvester--Schur

A coarse binomial coefficient estimate suffices when the cube of the
interval length is small relative to its left endpoint. This also handles
bounded lengths in the eventual square-anchor theorem.
-/

open scoped BigOperators

namespace Erdos380

lemma three_mul_primeCount_le_two_mul {k : ℕ} (hk : 2 ≤ k) :
    3 * (k + 1).primesBelow.card ≤ 2 * k := by
  let t := (Finset.range ((k - 1) / 2)).image (fun j => 2 * j + 3)
  have hsub : (k + 1).primesBelow ⊆ insert 2 t := by
    intro p hp
    obtain ⟨hpk, hp⟩ := Nat.mem_primesBelow.mp hp
    have hpmin := hp.two_le
    rcases hp.eq_two_or_odd with rfl | hpodd
    · exact Finset.mem_insert_self _ _
    · by_cases hp2 : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp2)
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨(p - 3) / 2, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  have hcard : (k + 1).primesBelow.card ≤ (k - 1) / 2 + 1 := by
    calc
      _ ≤ (insert 2 t).card := Finset.card_le_card hsub
      _ ≤ t.card + 1 := Finset.card_insert_le _ _
      _ ≤ _ := by
        have h := Finset.card_image_le (s := Finset.range ((k - 1) / 2))
          (f := fun j => 2 * j + 3)
        simpa [t] using Nat.add_le_add_right h 1
  omega

lemma choose_cube_le_of_small_prime_factors {n k : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hk : 2 ≤ k)
    (hsmall : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k) :
    (n.choose k) ^ 3 ≤ n ^ (2 * k) := by
  have hcpos : 0 < n.choose k := Nat.choose_pos hkn
  have hsub : (n.choose k).primeFactors ⊆ (k + 1).primesBelow := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_iff.mpr (hsmall p hprime (Nat.dvd_of_mem_primeFactors hp)), hprime⟩
  have he : 3 * (n.choose k).primeFactors.card ≤ 2 * k :=
    (Nat.mul_le_mul_left 3 (Finset.card_le_card hsub)).trans
      (three_mul_primeCount_le_two_mul hk)
  have hprod : n.choose k ≤ n ^ (n.choose k).primeFactors.card := by
    calc
      n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p :=
        Nat.prod_primeFactors_pow_factorization hcpos.ne'
      _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
        Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hn
      _ = _ := Finset.prod_const n
  calc
    (n.choose k) ^ 3 ≤ (n ^ (n.choose k).primeFactors.card) ^ 3 := Nat.pow_le_pow_left hprod 3
    _ = n ^ (3 * (n.choose k).primeFactors.card) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

lemma intervalProduct_eq_factorial_mul_choose {u v k : ℕ} (hu : 1 ≤ u)
    (hku : u + k = v + 1) : intervalProduct u v = k.factorial * v.choose k := by
  have hlen : v + 1 - u = k := by omega
  have hend : u + k - 1 = v := by omega
  unfold intervalProduct
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    hlen, ← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose', hend]

lemma intervalProduct_ge_pow {u v k : ℕ} (hku : u + k = v + 1) :
    u ^ k ≤ intervalProduct u v := by
  have hlen : v + 1 - u = k := by omega
  calc
    u ^ k = ∏ _n ∈ Finset.Icc u v, u := by simp [hlen]
    _ ≤ _ := Finset.prod_le_prod' fun n hn => (Finset.mem_Icc.mp hn).1

/-- A coarse large-prime-factor theorem sufficient for the short-interval range. -/
theorem intervalPrime_gt_of_cubic {u v k : ℕ} (hu : 1 ≤ u) (hk : 2 ≤ k)
    (hku : u + k = v + 1) (hv : v ≤ 2 * u) (hlarge : 4 * k ^ 3 < u) :
    k < intervalPrime u v := by
  by_contra h
  have hQ : intervalPrime u v ≤ k := by omega
  have hkn : k ≤ v := by omega
  have hvpos : 0 < v := by omega
  have hprod := intervalProduct_eq_factorial_mul_choose hu hku
  have hchoose : v.choose k ∣ intervalProduct u v := by
    rw [hprod]
    exact dvd_mul_left _ _
  have hsmall : ∀ p, p.Prime → p ∣ v.choose k → p ≤ k := by
    intro p hp hpc
    exact (prime_le_largestPrimeFactor (intervalProduct_pos hu).ne' hp
      (hpc.trans hchoose)).trans hQ
  have hc := choose_cube_le_of_small_prime_factors hvpos hkn hk hsmall
  have hl : u ^ k ≤ k ^ k * v.choose k := by
    calc
      u ^ k ≤ intervalProduct u v := intervalProduct_ge_pow hku
      _ = k.factorial * v.choose k := hprod
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
  have hpower : (u ^ 3) ^ k ≤ (k ^ 3 * v ^ 2) ^ k := by
    calc
      (u ^ 3) ^ k = (u ^ k) ^ 3 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 k]
      _ ≤ (k ^ k * v.choose k) ^ 3 := Nat.pow_le_pow_left hl 3
      _ = (k ^ 3) ^ k * (v.choose k) ^ 3 := by
        rw [mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 3]
      _ ≤ (k ^ 3) ^ k * (v ^ 2) ^ k := by
        exact Nat.mul_le_mul_left _ (by simpa only [pow_mul] using hc)
      _ = _ := (mul_pow _ _ _).symm
  have hbase : u ^ 3 ≤ k ^ 3 * v ^ 2 :=
    (Nat.pow_le_pow_iff_left (by omega : k ≠ 0)).mp hpower
  have hv2 := Nat.pow_le_pow_left hv 2
  have hmul := Nat.mul_le_mul_left (k ^ 3) hv2
  have hbound : u ^ 2 * u ≤ u ^ 2 * (4 * k ^ 3) := by nlinarith
  have hstrict := Nat.mul_lt_mul_of_pos_left hlarge (pow_pos (by omega : 0 < u) 2)
  exact (not_lt_of_ge hbound) hstrict

lemma BadInterval.short_of_cubic {u v : ℕ} (hbad : BadInterval u v)
    (hlarge : 4 * (v - u + 1) ^ 3 < u) : v - u < intervalPrime u v := by
  by_cases huv : u = v
  · have hQ := one_le_largestPrimeFactor (intervalProduct u v)
    change v - u < largestPrimeFactor (intervalProduct u v)
    omega
  · have hlen : u + (v - u + 1) = v + 1 := by have := hbad.2.1; omega
    have hlt := intervalPrime_gt_of_cubic hbad.1 (by have := hbad.2.1; omega)
      hlen (by have := hbad.right_lt_two_mul_left; omega) hlarge
    omega

theorem BadInterval.exists_square_anchor_of_cubic {u v : ℕ} (hbad : BadInterval u v)
    (hlarge : 4 * (v - u + 1) ^ 3 < u) :
    ∃ a ∈ Finset.Icc u v,
      intervalPrime u v ^ 2 ∣ a ∧ largestPrimeFactor a = intervalPrime u v :=
  hbad.exists_square_anchor_of_short (hbad.short_of_cubic hlarge)

end Erdos380
