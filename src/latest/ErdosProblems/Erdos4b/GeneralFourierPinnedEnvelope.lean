/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedExceptional

/-!
# Logarithmic envelope for the pinned exceptional integer

Each cross difference is bounded by `m * p₀ * (2 * K)`. The logarithm
of the product is consequently bounded by a fixed multiple of the
ambient logarithm, without any primorial factor in that envelope.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem pinnedIndexCrossDifference_natAbs_le
    {K m p₀ : ℕ} (h : Fin K) (i j : PinnedShiftIndex h) :
    (pinnedIndexCrossDifference h m p₀ i j).natAbs ≤ (m * p₀ + 1) * K := by
  have hiK : (i.val.val : ℤ) < K := by exact_mod_cast i.val.isLt
  have hjK : (j.val.val : ℤ) < K := by exact_mod_cast j.val.isLt
  have hhK : (h.val : ℤ) < K := by exact_mod_cast h.isLt
  have hi0 : (0 : ℤ) ≤ i.val.val := by positivity
  have hj0 : (0 : ℤ) ≤ j.val.val := by positivity
  have hh0 : (0 : ℤ) ≤ h.val := by positivity
  have hab : |(i.val.val : ℤ) - j.val.val| ≤ K := abs_le.mpr ⟨by omega, by omega⟩
  have hhi : |(h.val : ℤ) - i.val.val| ≤ K := abs_le.mpr ⟨by omega, by omega⟩
  have hbound : |pinnedIndexCrossDifference h m p₀ i j| ≤ ((m : ℤ) * p₀ + 1) * K := by
    rw [pinnedIndexCrossDifference, add_sub_assoc]
    calc
      _ ≤ |(m : ℤ) * p₀ * ((i.val.val : ℤ) - j.val.val)| +
          |(h.val : ℤ) - i.val.val| := abs_add_le _ _
      _ = (m : ℤ) * p₀ * |(i.val.val : ℤ) - j.val.val| +
          |(h.val : ℤ) - i.val.val| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (m : ℤ) * p₀)]
      _ ≤ (m : ℤ) * p₀ * K + K :=
        add_le_add (mul_le_mul_of_nonneg_left hab (by positivity)) hhi
      _ = _ := by ring
  rw [← Int.natCast_natAbs] at hbound
  exact_mod_cast hbound

theorem pinnedIndexCrossDifference_natAbs_le_simple
    {K m p₀ : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : 0 < p₀) (i j : PinnedShiftIndex h) :
    (pinnedIndexCrossDifference h m p₀ i j).natAbs ≤ m * p₀ * (2 * K) := by
  have hu : 1 ≤ m * p₀ := Nat.succ_le_iff.mpr (Nat.mul_pos hm hp₀)
  apply (pinnedIndexCrossDifference_natAbs_le h i j).trans
  nlinarith

theorem pinnedIndexExceptionalModulus_le_envelope
    {K m p₀ : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : 0 < p₀) :
    pinnedIndexExceptionalModulus h m p₀ ≤
      m * (m * p₀ * (2 * K)) ^ (Fintype.card (PinnedShiftIndex h) ^ 2) := by
  apply Nat.mul_le_mul_left m
  calc
    _ ≤ ∏ _ij : PinnedShiftIndex h × PinnedShiftIndex h, m * p₀ * (2 * K) := by
      apply Finset.prod_le_prod
      · intro ij hij
        exact Nat.zero_le _
      · intro ij hij
        exact pinnedIndexCrossDifference_natAbs_le_simple h hm hp₀ ij.1 ij.2
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, pow_two]

theorem log_pinnedIndexExceptionalModulus_le
    {K m p₀ : ℕ} (h : Fin K) (hm : 0 < m) (hKp₀ : K ≤ p₀) {V : ℝ}
    (hmV : Real.log m ≤ V) (hp₀V : Real.log p₀ ≤ 2 * V)
    (hKV : Real.log (2 * (K : ℝ)) ≤ V) :
    Real.log (pinnedIndexExceptionalModulus h m p₀) ≤
      (1 + 4 * (Fintype.card (PinnedShiftIndex h) : ℝ) ^ 2) * V := by
  have hK : 0 < K := h.pos
  have hp₀ : 0 < p₀ := hK.trans_le hKp₀
  have hM : (0 : ℝ) < pinnedIndexExceptionalModulus h m p₀ := by
    exact_mod_cast pinnedIndexExceptionalModulus_pos h hm hKp₀
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR : (0 : ℝ) < p₀ := by exact_mod_cast hp₀
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbound := Real.log_le_log hM
    (show (pinnedIndexExceptionalModulus h m p₀ : ℝ) ≤
      (m * (m * p₀ * (2 * K)) ^ (Fintype.card (PinnedShiftIndex h) ^ 2) : ℕ) by
        exact_mod_cast pinnedIndexExceptionalModulus_le_envelope h hm hp₀)
  push_cast at hbound
  rw [Real.log_mul hmR.ne' (by positivity), Real.log_pow,
    Real.log_mul (by positivity : (m : ℝ) * p₀ ≠ 0) (by positivity : 2 * (K : ℝ) ≠ 0),
    Real.log_mul hmR.ne' hpR.ne'] at hbound
  simp only [Nat.cast_pow] at hbound
  have hsum : Real.log m + Real.log p₀ + Real.log (2 * (K : ℝ)) ≤ 4 * V := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (Fintype.card (PinnedShiftIndex h) : ℝ))
  nlinarith

end

end Erdos4b
