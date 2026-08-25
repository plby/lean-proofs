import ErdosProblems.Erdos964.PrimePowerConvolution
import Mathlib.Data.Nat.Choose.Sum

/-!
# The local Euler factors of the scalar corrections

The dimension-two and dimension-three corrections have the same local
sum at every prime. At every good prime, this common sum exceeds one.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem scalarMomentCorrectionAF_local_summable (M k : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => scalarMomentCorrectionAF M k (p ^ j)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (k + 2))
  intro j hj
  exact scalarMomentCorrectionAF_prime_pow_eq_zero M k j hp
    (by simp only [Finset.mem_range] at hj; omega)

theorem scalarMomentCorrectionAF_local_tsum (M k : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, scalarMomentCorrectionAF M k (p ^ j)) =
      (1 + scalarMomentAF M k p) * (1 + coprimeMobiusInvAF M p) ^ k := by
  let a := scalarMomentAF M k p
  let b := coprimeMobiusInvAF M p
  have hbin : (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ) * b ^ j) = (1 + b) ^ k := by
    rw [add_comm 1 b, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [one_pow, mul_one]
    ring
  have hshift : (∑ j ∈ Finset.range (k + 1), (Nat.choose k (j + 1) : ℝ) * b ^ (j + 1)) + 1 =
      (1 + b) ^ k := by
    have heq : (∑ j ∈ Finset.range ((k + 1) + 1), (Nat.choose k j : ℝ) * b ^ j) =
        (1 + b) ^ k := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : k < k + 1)]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact hbin
    rw [Finset.sum_range_succ'] at heq
    simpa only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul] using heq
  rw [tsum_eq_sum (s := Finset.range (k + 2)) (fun j hj =>
    scalarMomentCorrectionAF_prime_pow_eq_zero M k j hp
      (by simp only [Finset.mem_range] at hj; omega))]
  rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [pow_zero, (scalarMomentCorrectionAF_multiplicative M k).map_one]
  simp_rw [scalarMomentCorrectionAF_prime_pow_succ M k _ hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ j ∈ Finset.range (k + 1), (Nat.choose k (j + 1) : ℝ) * b ^ (j + 1)) +
    a * (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ) * b ^ j) + 1 =
      (1 + a) * (1 + b) ^ k
  rw [hbin]
  nlinarith [hshift]

theorem scalarMomentCorrectionAF_local_tsum_formula (M k : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, scalarMomentCorrectionAF M k (p ^ j)) =
      if p ∣ M then 1 else
        (1 + (k : ℝ) / ((p : ℝ) - 3)) * (1 - (1 : ℝ) / p) ^ k := by
  rw [scalarMomentCorrectionAF_local_tsum M k hp, scalarMomentAF_prime M k hp,
    coprimeMobiusInvAF_prime M hp]
  by_cases h : p ∣ M
  · simp only [if_pos h, add_zero, one_pow, mul_one]
  · simp only [if_neg h]
    congr 1
    congr 1
    ring

theorem scalarMomentCorrectionAF_local_tsum_two_eq_three (M : ℕ) (h3M : 3 ∣ M)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, scalarMomentCorrectionAF M 2 (p ^ j)) =
      ∑' j : ℕ, scalarMomentCorrectionAF M 3 (p ^ j) := by
  rw [scalarMomentCorrectionAF_local_tsum_formula M 2 hp,
    scalarMomentCorrectionAF_local_tsum_formula M 3 hp]
  by_cases h : p ∣ M
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases hp3 : p = 3
    · subst p
      exact (h h3M).elim
    · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hp3R : (p : ℝ) - 3 ≠ 0 := by exact_mod_cast (show (p : ℤ) - 3 ≠ 0 by omega)
      norm_num only [Nat.cast_ofNat]
      field_simp
      ring

theorem scalarMomentCorrectionAF_local_tsum_three_ge_one (M : ℕ)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) {p : ℕ} (hp : p.Prime) :
    1 ≤ ∑' j : ℕ, scalarMomentCorrectionAF M 3 (p ^ j) := by
  rw [scalarMomentCorrectionAF_local_tsum_formula M 3 hp]
  by_cases h : p ∣ M
  · rw [if_pos h]
  · rw [if_neg h]
    have hp2 : p ≠ 2 := fun heq => h (heq ▸ h2M)
    have hp3 : p ≠ 3 := fun heq => h (heq ▸ h3M)
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by have := hp.two_le; omega)
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp3R : (p : ℝ) - 3 ≠ 0 := by linarith
    have hid : (1 + (3 : ℝ) / ((p : ℝ) - 3)) * (1 - (1 : ℝ) / p) ^ 3 =
        1 + (3 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * ((p : ℝ) - 3)) := by
      field_simp
      ring
    norm_num only [Nat.cast_ofNat]
    rw [hid]
    apply le_add_of_nonneg_right
    exact div_nonneg (by linarith) (mul_nonneg (sq_nonneg _) (by linarith))

end Erdos964
