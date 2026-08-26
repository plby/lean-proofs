import ErdosProblems.Erdos421.FiniteWindowEnergy

/-! # Combining finitely many real window comparisons on the same interval -/

namespace Erdos421

open MeasureTheory

theorem finite_real_window_energy_le {ι : Type*} (I : Finset ι) (f g : ι → ℝ → ℝ)
    (hf : ∀ i ∈ I, Continuous (f i)) (hg : ∀ i ∈ I, Continuous (g i))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ y in a..b, |(∑ i ∈ I, f i y) - ∑ i ∈ I, g i y| ^ 2) ≤
      (I.card : ℝ) * ∑ i ∈ I, ∫ y in a..b, |f i y - g i y| ^ 2 := by
  have hF : Continuous (fun y ↦ |(∑ i ∈ I, f i y) - ∑ i ∈ I, g i y| ^ 2) :=
    (((continuous_finsetSum I hf).sub (continuous_finsetSum I hg)).abs.pow 2)
  have hterm (i : ι) (hi : i ∈ I) : Continuous (fun y ↦ |f i y - g i y| ^ 2) :=
    (((hf i hi).sub (hg i hi)).abs.pow 2)
  have hG : Continuous (fun y ↦ (I.card : ℝ) * ∑ i ∈ I, |f i y - g i y| ^ 2) :=
    continuous_const.mul (continuous_finsetSum I hterm)
  have hpoint (y : ℝ) : |(∑ i ∈ I, f i y) - ∑ i ∈ I, g i y| ^ 2 ≤
      (I.card : ℝ) * ∑ i ∈ I, |f i y - g i y| ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    simp only [sq_abs]
    exact sq_sum_le_card_mul_sum_sq
  have hb := intervalIntegral.integral_mono_on (μ := volume) hab (hF.intervalIntegrable a b)
    (hG.intervalIntegrable a b) (fun y _ ↦ hpoint y)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i hi ↦ (hterm i hi).intervalIntegrable a b)] at hb
  exact hb

theorem finite_real_window_energy_bound {ι : Type*} (I : Finset ι) (f g : ι → ℝ → ℝ)
    (hf : ∀ i ∈ I, Continuous (f i)) (hg : ∀ i ∈ I, Continuous (g i))
    {a b E : ℝ} (hab : a ≤ b)
    (hmean : ∀ i ∈ I, (∫ y in a..b, |f i y - g i y| ^ 2) ≤ E) :
    (∫ y in a..b, |(∑ i ∈ I, f i y) - ∑ i ∈ I, g i y| ^ 2) ≤ (I.card : ℝ) ^ 2 * E := by
  apply (finite_real_window_energy_le I f g hf hg hab).trans
  calc
    _ ≤ (I.card : ℝ) * ∑ _i ∈ I, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmean) (Nat.cast_nonneg I.card)
    _ = _ := by simp [pow_two, mul_assoc]

end Erdos421
