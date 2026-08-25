import ErdosProblems.Erdos67.MRAppendixLargeValues
import Mathlib.Analysis.PSeries

/-!
# Square mass of a weighted prime block

The high-moment term in the Ramaré bad-frequency estimate contains the
square mass of `f(p) p^{-sigma}`.  For `sigma >= 1`, the whole block is
bounded by the elementary tail of `sum n^{-2}`.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

theorem sum_normSq_weightedPrimeCoefficient_primesInBlock_le
    {I : ℕ × ℕ} (hlo : 2 ≤ I.1) (hIU : I.1 ≤ I.2) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    (∑ p ∈ primesInBlock I,
        Complex.normSq (weightedPrimeCoefficient f sigma p)) ≤
      ((I.1 - 1 : ℕ) : ℝ)⁻¹ := by
  have hterm : ∀ p ∈ primesInBlock I,
      Complex.normSq (weightedPrimeCoefficient f sigma p) ≤
        (((p : ℝ) ^ 2)⁻¹) := by
    intro p hp
    have hpPrime := (mem_primesInBlock.mp hp).1
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
    have hrpow : (p : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-(1 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
    have hrpowNonneg : 0 ≤ (p : ℝ) ^ (-sigma) := by positivity
    have hinvNonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hsquare : ((p : ℝ) ^ (-sigma)) ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by
      rw [Real.rpow_neg_one] at hrpow
      exact pow_le_pow_left₀ hrpowNonneg hrpow 2
    exact (normSq_weightedPrimeCoefficient_le hbound sigma hpPrime.pos).trans
      (by simpa only [inv_pow] using hsquare)
  have hsubset : primesInBlock I ⊆ Finset.Ioc (I.1 - 1) I.2 := by
    intro p hp
    rw [Finset.mem_Ioc]
    have hpRange := (mem_primesInBlock.mp hp).2
    omega
  calc
    (∑ p ∈ primesInBlock I,
        Complex.normSq (weightedPrimeCoefficient f sigma p)) ≤
        ∑ p ∈ primesInBlock I, (((p : ℝ) ^ 2)⁻¹) := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ioc (I.1 - 1) I.2,
        (((n : ℝ) ^ 2)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ by positivity)
    _ ≤ ((I.1 - 1 : ℕ) : ℝ)⁻¹ - (I.2 : ℝ)⁻¹ := by
      apply sum_Ioc_inv_sq_le_sub
      · omega
      · omega
    _ ≤ ((I.1 - 1 : ℕ) : ℝ)⁻¹ :=
      sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

end

end Erdos67
