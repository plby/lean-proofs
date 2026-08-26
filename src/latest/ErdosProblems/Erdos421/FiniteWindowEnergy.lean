import ErdosProblems.Erdos421.ProductWindowScaling
import ErdosProblems.Erdos421.ActiveProductScales

/-! # Summing the energy of finitely many active product rectangles -/

namespace Erdos421

open MeasureTheory

theorem finite_sum_norm_square_le {ι : Type*} (I : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ I, f i‖ ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, ‖f i‖ ^ 2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  exact sq_sum_le_card_mul_sum_sq

theorem finite_sum_interval_energy_le {ι : Type*} (I : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ I, Integrable (fun y ↦ ‖f i y‖ ^ 2)) {a b : ℝ} (hab : a ≤ b) :
    (∫ y in a..b, ‖∑ i ∈ I, f i y‖ ^ 2) ≤
      (I.card : ℝ) * ∑ i ∈ I, ∫ y : ℝ, ‖f i y‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hab]
  calc
    _ ≤ ∫ y in Set.Ioc a b, (I.card : ℝ) * ∑ i ∈ I, ‖f i y‖ ^ 2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ sq_nonneg _))
        ((integrable_finsetSum I (fun i hi ↦ (hf i hi).integrableOn)).const_mul (I.card : ℝ))
        (Filter.Eventually.of_forall (fun y ↦ finite_sum_norm_square_le I (fun i ↦ f i y)))
    _ = (I.card : ℝ) * ∑ i ∈ I, ∫ y in Set.Ioc a b, ‖f i y‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum I (fun i hi ↦ (hf i hi).integrableOn)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg I.card)
      apply Finset.sum_le_sum
      intro i hi
      exact setIntegral_le_integral (hf i hi) (Filter.Eventually.of_forall (fun y ↦ sq_nonneg _))

theorem finite_product_window_energy_le {ι : Type*} (I : Finset ι)
    (S : ι → Finset ℕ) (T : Finset ℕ) (a b : ℕ → ℂ) (σ : ℝ)
    {δ ρ u v E : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (huv : u ≤ v)
    (hmean : ∀ i ∈ I, (∫ y : ℝ,
      ‖scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow δ y -
        scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow ρ y‖ ^ 2) ≤ E) :
    (∫ y in u..v, ‖∑ i ∈ I,
      (scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow δ y -
        scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow ρ y)‖ ^ 2) ≤
          (I.card : ℝ) ^ 2 * E := by
  have hb := finite_sum_interval_energy_le I
    (fun i y ↦ scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow δ y -
      scaledProductWindow (S i) T a b σ oneSidedSchwartzWindow ρ y)
    (fun i _ ↦ scaledProductWindow_energy_integrable (S i) T a b σ oneSidedSchwartzWindow hδ hρ) huv
  apply hb.trans
  calc
    _ ≤ (I.card : ℝ) * ∑ _i ∈ I, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmean) (Nat.cast_nonneg I.card)
    _ = _ := by simp [pow_two, mul_assoc]

end Erdos421
