import ErdosProblems.Erdos421.Sampling

/-! # Packing unit-separated sample times in an interval -/

namespace Erdos421

open MeasureTheory

theorem separated_sample_card_le (F : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ} (hAB : A ≤ B)
    (ht : ∀ i ∈ F, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|) :
    (F.card : ℝ) ≤ B + 1 - A := by
  have hb := sum_unit_integrals_le F t hAB ht hsep
    (H := fun _ ↦ (1 : ℝ)) continuous_const (fun _ ↦ zero_le_one)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul] using hb

end Erdos421
