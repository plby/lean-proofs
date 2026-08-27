import ErdosProblems.Erdos587.HooleyRobustModelExtraction

/-! # Elementary total-mass bounds for interval inputs -/

open scoped BigOperators

namespace Erdos587.CFP

lemma delta_interval_mass_le (A : Finset ℤ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) : ∑ a ∈ A, a ≤ (N : ℤ) * (N + 1) := by
  have hcard : A.card ≤ N + 1 := by
    have hh := Finset.card_le_card hA
    simpa only [Int.card_Icc, sub_zero, ← Nat.cast_add_one, Int.toNat_natCast] using hh
  calc
    _ ≤ ∑ _a ∈ A, (N : ℤ) := Finset.sum_le_sum (fun a ha => (Finset.mem_Icc.mp (hA ha)).2)
    _ = (A.card : ℤ) * N := by simp
    _ ≤ (N + 1 : ℤ) * N := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

lemma delta_dyadic_interval_mass_le (A : Finset ℤ) (L : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) :
    ∑ a ∈ A, a ≤ (2 : ℤ) ^ (2 * L + 1) := by
  have htwo : (1 : ℤ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  have hh := delta_interval_mass_le A (2 ^ L) hA
  push_cast at hh
  have hpow : (2 : ℤ) ^ (2 * L + 1) = 2 * (2 ^ L) ^ 2 := by
    rw [pow_add, pow_one, pow_mul']
    ring
  rw [hpow]
  nlinarith

end Erdos587.CFP
