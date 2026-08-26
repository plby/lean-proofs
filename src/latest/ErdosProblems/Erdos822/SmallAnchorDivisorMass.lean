/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallAnchorFiber
import ErdosProblems.Erdos822.SmoothClassHarmonic

/-! # Cancelling the fixed smooth part in the small-divisor anchor sum -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_small_anchor_divisor_mass_bound {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ m' h U : ℕ,
      m' ∈ gilCofactors N S C → 0 < h → h ≤ N ^ 3 → h ∣ shiftedTotient m' →
      roughPart h (b1Cutoff N) = h → Nat.log 2 N ≤ U →
      ((smoothPart m' (b1Cutoff N) : ℝ) * h) *
        (∑ m ∈ smallSupportedDivisorCofactors N S C m' h,
          ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U) ≤
        K * Real.log (N : ℝ) * (4 : ℝ) ^ h.primeFactors.card / h := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_small_fixedPair_singular_bound hS C
  obtain ⟨A, hA, hclassMass⟩ := exists_sum_inv_smoothClass_le_log_ratio
  refine ⟨K * A, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 2]
    with N hbound hN hy
  intro m' h U hm' hh hhN hhF hrough hLU
  let y := b1Cutoff N
  let d := smoothPart m' y
  let T := (oddSmallFactors N).filter (fun k ↦ smoothPart k y = d)
  let V := K * Real.log (y : ℝ) * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2
  have hd : 0 < d := Nat.pos_of_ne_zero (smoothPart_ne_zero _ _)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlogyp : 0 < Real.log (y + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y + 1))
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hyL : y ≤ Nat.log 2 N :=
    (nthRoot_le_self_of_pos (by norm_num : 0 < 4)).trans (Nat.log_le_self 2 (Nat.log 2 N))
  have hyN : y + 1 ≤ N := by
    have hLN := Nat.log_lt_self 2 (by omega : N ≠ 0)
    omega
  have hTmass : (∑ k ∈ T, (1 : ℝ) / k) ≤ A * Real.log (N : ℝ) / ((d : ℝ) * Real.log (y + 1 : ℕ)) :=
    hclassMass T N d y (by omega) hyN
      (fun k hk ↦ oddSmallFactors_pos (Finset.mem_filter.mp hk).1)
      (fun k hk ↦ oddSmallFactors_le (Finset.mem_filter.mp hk).1)
      (fun k hk ↦ (Finset.mem_filter.mp hk).2)
  have hsum : (∑ m ∈ smallSupportedDivisorCofactors N S C m' h,
      ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U) ≤
      V * ∑ k ∈ T, (1 : ℝ) / k := by
    rw [sum_smallSupportedDivisorCofactors_eq_fixedPairs hN]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkclass : smoothPart k y = d
    · rw [if_pos hkclass]
      have h := mul_le_mul_of_nonneg_left (hbound k m' h U hk hm' hh hhN hhF hrough hLU)
        (by positivity : (0 : ℝ) ≤ 1 / k)
      calc
        _ ≤ ((1 : ℝ) / k) * V := h
        _ = _ := by ring
    · have hempty := smallOffDiagonalPrimePairs_empty_of_smoothPart_ne (h := h) hN hk hm' hkclass
      simp only [hempty, Finset.sum_empty, mul_zero, if_neg hkclass]
      exact le_rfl
  have hratio : Real.log (y : ℝ) / Real.log (y + 1 : ℕ) ≤ 1 := by
    apply (div_le_one hlogyp).mpr
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
    exact_mod_cast Nat.le_succ y
  calc
    _ ≤ ((d : ℝ) * h) * (V * ∑ k ∈ T, (1 : ℝ) / k) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((d : ℝ) * h) * (V * (A * Real.log (N : ℝ) / ((d : ℝ) * Real.log (y + 1 : ℕ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hTmass (by dsimp [V]; positivity)
    _ = (K * A * Real.log (N : ℝ) * (4 : ℝ) ^ h.primeFactors.card / h) *
        (Real.log (y : ℝ) / Real.log (y + 1 : ℕ)) := by
      dsimp [V]
      field_simp
    _ ≤ (K * A * Real.log (N : ℝ) * (4 : ℝ) ^ h.primeFactors.card / h) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

#print axioms exists_eventually_small_anchor_divisor_mass_bound

end Erdos822
