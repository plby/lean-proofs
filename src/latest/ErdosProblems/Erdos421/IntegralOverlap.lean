import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Summing local integral bounds with bounded overlap -/

namespace Erdos421

open MeasureTheory

theorem integral_bounded_overlap_le {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset I) (E : I → Set X) [∀ x, DecidablePred (fun i ↦ x ∈ E i)]
    (F : X → ℝ) {W : ℝ}
    (hE : ∀ i ∈ S, MeasurableSet (E i)) (hF : Integrable F μ)
    (hFnonneg : ∀ x, 0 ≤ F x)
    (hcover : ∀ x, (((S.filter (fun i ↦ x ∈ E i)).card : ℕ) : ℝ) ≤ W) :
    (∑ i ∈ S, ∫ x in E i, F x ∂μ) ≤ W * ∫ x, F x ∂μ := by
  classical
  have hfi : ∀ i ∈ S, Integrable ((E i).indicator F) μ :=
    fun i hi ↦ hF.indicator (hE i hi)
  have hpoint (x : X) : (∑ i ∈ S, (E i).indicator F x) ≤ W * F x := by
    calc
      _ = (((S.filter (fun i ↦ x ∈ E i)).card : ℕ) : ℝ) * F x := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcover x) (hFnonneg x)
  calc
    _ = ∑ i ∈ S, ∫ x, (E i).indicator F x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_indicator (hE i hi)).symm
    _ = ∫ x, ∑ i ∈ S, (E i).indicator F x ∂μ := (integral_finsetSum S hfi).symm
    _ ≤ ∫ x, W * F x ∂μ :=
      integral_mono (integrable_finsetSum S hfi) (hF.const_mul W) hpoint
    _ = _ := integral_const_mul W F

theorem sum_le_of_local_integral_bound {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset I) (E : I → Set X) [∀ x, DecidablePred (fun i ↦ x ∈ E i)]
    (F : X → ℝ) (a : I → ℝ)
    {v W : ℝ} (hE : ∀ i ∈ S, MeasurableSet (E i)) (hF : Integrable F μ)
    (hFnonneg : ∀ x, 0 ≤ F x)
    (hcover : ∀ x, (((S.filter (fun i ↦ x ∈ E i)).card : ℕ) : ℝ) ≤ W)
    (hlocal : ∀ i ∈ S, v * a i ≤ ∫ x in E i, F x ∂μ) :
    v * (∑ i ∈ S, a i) ≤ W * ∫ x, F x ∂μ := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum hlocal).trans (integral_bounded_overlap_le μ S E F hE hF hFnonneg hcover)

end Erdos421
